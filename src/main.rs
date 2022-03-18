#![allow(unused_imports)]

use parity_wasm::elements::Instruction::*;
use parity_wasm::elements::*;
use std::fs::File;
use std::io::Read;
use ark_crypto_primitives::crh::poseidon::{ /* TwoToOneCRH, */ CRH};
use ark_crypto_primitives::crh::poseidon::constraints::{CRHGadget, CRHParametersVar};
use ark_sponge::poseidon::PoseidonParameters;
// use ark_bls12_377::Fr;
use ark_std::UniformRand;
use ark_std::Zero;
use ark_crypto_primitives::CRHScheme;
use ark_relations::r1cs::ConstraintSystem;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::{
    fields::fp::{AllocatedFp, FpVar},
};
use ark_crypto_primitives::CRHSchemeGadget;
use ark_relations::r1cs::ConstraintSystemRef;
use ark_relations::r1cs::SynthesisError;
use ark_relations::r1cs::ConstraintSynthesizer;
use ark_ff::PrimeField;
use ark_sponge::Absorb;

use ark_mnt4_298::{
    constraints::PairingVar as MNT4PairingVar, Fr, MNT4_298 as MNT4PairingEngine,
};
use ark_mnt6_298::{
    Fr as MNT6Fr,
    constraints::PairingVar as MNT6PairingVar, MNT6_298 as MNT6PairingEngine,
};
use ark_groth16::Groth16;
use ark_groth16::constraints::Groth16VerifierGadget;
use ark_std::test_rng;
use ark_crypto_primitives::SNARK;
use ark_crypto_primitives::CircuitSpecificSetupSNARK;
use ark_r1cs_std::boolean::Boolean;
use ark_relations::ns;
use ark_ec::PairingEngine;
use ark_crypto_primitives::snark::constraints::SNARKGadget;
use ark_r1cs_std::eq::EqGadget;
use ark_groth16::Proof;
use ark_groth16::VerifyingKey;
use ark_std::One;
use ark_groth16::ProvingKey;
use ark_r1cs_std::ToBitsGadget;
use ark_crypto_primitives::snark::FromFieldElementsGadget;
use ark_r1cs_std::boolean::AllocatedBool;

trait HashField : Absorb + PrimeField {
}

#[derive(Debug, Clone)]
pub struct Transition {
    pub before: VM,
    pub after: VM,
}

pub trait InstructionCircuit : ConstraintSynthesizer<Fr> + Clone {
    fn calc_hash(&self) -> Fr;
    fn transition(&self) -> Transition;
}

pub trait InstructionCircuit2 : ConstraintSynthesizer<MNT6Fr> + Clone {
    fn calc_hash(&self) -> Fr;
}

fn get_file(fname: String) -> Vec<u8> {
    let mut file = File::open(&fname).unwrap();
    let mut buffer = Vec::<u8>::new();
    file.read_to_end(&mut buffer).unwrap();
    buffer
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum CodeTree {
    CLoop (Vec<CodeTree>),
    CConst (u32),
    CAdd,
    CSub,
    CGt,
    CEnd,
    CBreakIf (u32),
    CSetLocal (u32),
    CGetLocal (u32),
}

use CodeTree::*;

fn block_start(op: &Instruction) -> bool {
    match &*op {
        Loop(_) => true,
        _ => false,
    }
}

fn find_end(code: &[Instruction]) -> &[Instruction] {
    let mut depth = 0;
    for (i, op) in code.iter().enumerate() {
        // println!("scanning {}", op);
        if block_start(op) {
            depth = depth + 1;
        } else if *op == End && depth == 0{
            return &code[i+1..];
        } else if *op == End {
            depth = depth - 1
        }
    }
    panic!("Cannot find end");
}

fn process_code(code: &[Instruction]) -> Vec<CodeTree> {
    let mut res = vec![];
    for (i, op) in code.iter().enumerate() {
        // println!("op {}", op);
        match &*op {
            Loop(_) => {
                let cont = find_end(&code[i+1..]);
                res.push(CLoop(process_code(cont)))
            }
            I32Add => res.push(CAdd),
            I32Sub => res.push(CSub),
            I32GtU => res.push(CGt),
            GetLocal(x) => res.push(CGetLocal(*x as u32)),
            SetLocal(x) => res.push(CSetLocal(*x as u32)),
            I32Const(x) => res.push(CConst(*x as u32)),
            BrIf(x) => res.push(CBreakIf(*x as u32)),
            End => {
                res.push(CEnd);
                return res;
            }
            _ => println!("Unknown op"),
        }
    }
    res
}

fn hash_list(params: &PoseidonParameters<Fr>, lst: &[Fr]) -> Fr {
    let mut res = Fr::zero();
    for elem in lst.iter() {
        let mut inputs = vec![];
        inputs.push(elem.clone());
        inputs.push(res);
        res = CRH::<Fr>::evaluate(&params, inputs).unwrap();
    }
    res
}

fn hash_many(params: &PoseidonParameters<Fr>, lst: &[Fr]) -> Fr {
    let mut inputs = vec![];
    for e in lst.iter() {
        inputs.push(e.clone())
    }
    CRH::<Fr>::evaluate(&params, inputs).unwrap()
}

fn hash_code(params: &PoseidonParameters<Fr>, code: &[CodeTree]) -> Fr {
    let mut res = Fr::zero();
    for op in code.iter().rev() {
        // println!("hashing {:?}", op);
        match &*op {
            CAdd => {
                let mut inputs = vec![];
                inputs.push(Fr::from(1));
                inputs.push(res);
                res = CRH::<Fr>::evaluate(&params, inputs).unwrap();
            }
            CSub => {
                let mut inputs = vec![];
                inputs.push(Fr::from(2));
                inputs.push(res);
                res = CRH::<Fr>::evaluate(&params, inputs).unwrap();
            }
            CGt => {
                let mut inputs = vec![];
                inputs.push(Fr::from(3));
                inputs.push(res);
                res = CRH::<Fr>::evaluate(&params, inputs).unwrap();
            }
            CGetLocal(x) => {
                let mut inputs = vec![];
                inputs.push(Fr::from(4));
                inputs.push(Fr::from(*x));
                inputs.push(res);
                res = CRH::<Fr>::evaluate(&params, inputs).unwrap();
            }
            CSetLocal(x) => {
                let mut inputs = vec![];
                inputs.push(Fr::from(5));
                inputs.push(Fr::from(*x));
                inputs.push(res);
                res = CRH::<Fr>::evaluate(&params, inputs).unwrap();
            }
            CConst(x) => {
                let mut inputs = vec![];
                inputs.push(Fr::from(6));
                inputs.push(Fr::from(*x));
                inputs.push(res);
                res = CRH::<Fr>::evaluate(&params, inputs).unwrap();
            }
            CBreakIf(x) => {
                let mut inputs = vec![];
                inputs.push(Fr::from(7));
                inputs.push(Fr::from(*x));
                inputs.push(res);
                res = CRH::<Fr>::evaluate(&params, inputs).unwrap();
            }
            CLoop(cont) => {
                let mut inputs = vec![];
                inputs.push(Fr::from(8));
                inputs.push(hash_code(&params, cont));
                inputs.push(res);
                res = CRH::<Fr>::evaluate(&params, inputs).unwrap();
            }
            CEnd => {
                let mut inputs = vec![];
                inputs.push(Fr::from(9));
                inputs.push(res);
                // println!("cend {} {} {}", &inputs[0], &inputs[1], &res);
                res = CRH::<Fr>::evaluate(&params, inputs).unwrap();
                // println!("cend {}", &res);
            }
        }
    }
    res
}

fn generate_hash() -> PoseidonParameters<Fr> {
    let mut test_rng = ark_std::test_rng();

    // TODO: The following way of generating the MDS matrix is incorrect
    // and is only for test purposes.

    let mut mds = vec![vec![]; 3];
    for i in 0..3 {
        for _ in 0..3 {
            mds[i].push(Fr::rand(&mut test_rng));
        }
    }

    let mut ark = vec![vec![]; 8 + 24];
    for i in 0..8 + 24 {
        for _ in 0..3 {
            ark[i].push(Fr::rand(&mut test_rng));
        }
    }

    let mut test_a = Vec::new();
    let mut test_b = Vec::new();
    for _ in 0..3 {
        test_a.push(Fr::rand(&mut test_rng));
        test_b.push(Fr::rand(&mut test_rng));
    }
    PoseidonParameters::<Fr>::new(8, 24, 31, mds, ark)

}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum ControlFrame {
    LoopFrame(Vec<CodeTree>, Vec<CodeTree>)
}

impl ControlFrame {
    fn hash(&self, params: &PoseidonParameters<Fr>) -> Fr {
        match self {
            ControlFrame::LoopFrame(a, b) => {
                let mut inputs = vec![];
                inputs.push(Fr::from(1));
                inputs.push(hash_code(&params, &a));
                inputs.push(hash_code(&params, &b));
                CRH::<Fr>::evaluate(&params, inputs).unwrap()
            }
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub struct VM {
    pub expr_stack : Vec<u32>,
    pub locals : Vec<u32>,
    pub control_stack: Vec<ControlFrame>,
    pub pc: Vec<CodeTree>,
    pub step_counter: usize,
}

pub mod add;
pub mod sub;
pub mod gt;
pub mod get;
pub mod set;
pub mod constant;
pub mod loopi;
pub mod endi;
pub mod breakno;
pub mod breakyes;

pub mod memory;

use crate::add::AddCircuit;
use crate::sub::SubCircuit;
use crate::gt::GtCircuit;
use crate::get::GetCircuit;
use crate::set::SetCircuit;
use crate::constant::ConstCircuit;
use crate::loopi::LoopCircuit;
use crate::endi::EndCircuit;
use crate::breakno::BreakNoCircuit;
use crate::breakyes::BreakYesCircuit;

#[derive(Debug, Clone)]
pub struct Collector {
    add: Vec<AddCircuit>,
    sub: Vec<SubCircuit>,
    gt: Vec<GtCircuit>,
    get: Vec<GetCircuit>,
    set: Vec<SetCircuit>,
    constant: Vec<ConstCircuit>,
    loopi: Vec<LoopCircuit>,
    endi: Vec<EndCircuit>,
    breakno: Vec<BreakNoCircuit>,
    breakyes: Vec<BreakYesCircuit>,
}

impl VM {
    fn new(code: Vec<CodeTree>) -> Self {
        VM {
            pc: code,
            expr_stack: vec![],
            control_stack: vec![],
            locals: vec![0; 2],
            step_counter: 0,
        }
    }

    fn hash_stack(&self, params: &PoseidonParameters<Fr>) -> Fr {
        hash_list(&params, &self.expr_stack.iter().map(|a| Fr::from(*a)).collect::<Vec<Fr>>())
    }

    fn hash_locals(&self, params: &PoseidonParameters<Fr>) -> Fr {
        hash_many(&params, &self.locals.iter().map(|a| Fr::from(*a)).collect::<Vec<Fr>>())
    }

    fn hash_control(&self, params: &PoseidonParameters<Fr>) -> Fr {
        hash_list(&params, &self.control_stack.iter().map(|a| a.hash(&params)).collect::<Vec<Fr>>())
    }

    fn hash(&self, params: &PoseidonParameters<Fr>) -> Fr {
        let mut inputs = vec![];
        inputs.push(hash_code(&params, &self.pc));
        inputs.push(self.hash_stack(&params));
        inputs.push(self.hash_locals(&params));
        inputs.push(self.hash_control(&params));
        CRH::<Fr>::evaluate(&params, inputs).unwrap()
    }

    fn hash_mem(&self, params: &PoseidonParameters<Fr>) -> Fr {
        let mut inputs = vec![];
        inputs.push(hash_code(&params, &self.pc));
        inputs.push(self.hash_stack(&params));
        inputs.push(Fr::from(self.step_counter as u32));
        inputs.push(self.hash_control(&params));
        CRH::<Fr>::evaluate(&params, inputs).unwrap()
    }

    fn incr_pc(&mut self) {
        self.pc = self.pc[1..].iter().map(|a| a.clone()).collect::<Vec<CodeTree>>();
    }

    fn step(&mut self, params: &PoseidonParameters<Fr>, c : &mut Collector) {
        if self.pc.len() == 0 {
            return
        }
        let elen = self.expr_stack.len();
        let clen = self.control_stack.len();
        let before = self.clone();
        self.step_counter = self.step_counter + 1;
        match &self.pc[0] {
            CAdd => {
                let p1 = self.expr_stack[elen - 1];
                let p2 = self.expr_stack[elen - 2];
                self.expr_stack[elen - 2] = p1 + p2;
                self.expr_stack.pop();
                self.incr_pc();
                let after = self.clone();
                c.add.push(AddCircuit{
                    before,
                    after,
                    params: params.clone(),
                })
            }
            CSub => {
                let p1 = self.expr_stack[elen - 1];
                let p2 = self.expr_stack[elen - 2];
                self.expr_stack[elen - 2] = p2 - p1;
                self.expr_stack.pop();
                self.incr_pc();
                c.sub.push(SubCircuit{
                    before,
                    after: self.clone(),
                    params: params.clone(),
                })
            }
            CGt => {
                let p1 = self.expr_stack[elen - 1];
                let p2 = self.expr_stack[elen - 2];
                let res = if p1 < p2 { 1 } else { 0 };
                self.expr_stack[elen - 2] = res;
                self.expr_stack.pop();
                self.incr_pc();
                c.gt.push(GtCircuit{
                    before,
                    after: self.clone(),
                    params: params.clone(),
                })
            }
            CConst(a) => {
                let a = *a;
                self.expr_stack.push(a);
                self.incr_pc();
                c.constant.push(ConstCircuit{
                    before,
                    after: self.clone(),
                    params: params.clone(),
                    idx: a,
                })
            }
            CGetLocal(a) => {
                self.expr_stack.push(self.locals[*a as usize]);
                let a = *a;
                self.incr_pc();
                c.get.push(GetCircuit{
                    before,
                    after: self.clone(),
                    params: params.clone(),
                    idx: a,
                })
            }
            CSetLocal(a) => {
                let a = *a as usize;
                self.locals[a] = self.expr_stack[elen - 1];
                self.expr_stack.pop();
                self.incr_pc();
                c.set.push(SetCircuit{
                    before,
                    after: self.clone(),
                    params: params.clone(),
                    idx: a,
                })
            }
            CLoop(cont) => {
                self.control_stack.push(ControlFrame::LoopFrame(cont.clone(), self.pc.clone()));
                self.incr_pc();
                c.loopi.push(LoopCircuit{
                    before,
                    after: self.clone(),
                    params: params.clone(),
                })
            }
            CEnd => {
                if clen == 0 {
                    return
                }
                let ControlFrame::LoopFrame(c1, _) = self.control_stack[clen - 1].clone();
                self.control_stack.pop();
                self.pc = c1;
                c.endi.push(EndCircuit{
                    before,
                    after: self.clone(),
                    params: params.clone(),
                })
            }
            CBreakIf(num) => {
                let num = *num as usize;
                let p1 = self.expr_stack[elen - 1];
                self.expr_stack.pop();
                if p1 != 0 {
                    let ControlFrame::LoopFrame(_, c1) = self.control_stack[clen - 1 - num].clone();
                    for _i in 0..=num {
                        self.control_stack.pop();
                    }
                    self.pc = c1;
                    c.breakyes.push(BreakYesCircuit{
                        before,
                        after: self.clone(),
                        params: params.clone(),
                    })
                } else {
                    self.incr_pc();
                    c.breakno.push(BreakNoCircuit{
                        before,
                        after: self.clone(),
                        params: params.clone(),
                    })
                }
            }
        }
    } 
}

fn hash_pair(params: &PoseidonParameters<Fr>, a: &Fr, b: &Fr) -> Fr {
    let mut inputs = vec![];
    inputs.push(a.clone());
    inputs.push(b.clone());
    CRH::<Fr>::evaluate(params, inputs).unwrap()
}

type InnerSNARK = Groth16<MNT4PairingEngine>;
type InnerSNARKProof = Proof<MNT4PairingEngine>;
type InnerSNARKVK = VerifyingKey<MNT4PairingEngine>;
type InnerSNARKPK = ProvingKey<MNT4PairingEngine>;
type InnerSNARKGadget = Groth16VerifierGadget<MNT4PairingEngine, MNT4PairingVar>;

type OuterSNARK = Groth16<MNT6PairingEngine>;
type OuterSNARKProof = Proof<MNT6PairingEngine>;
type OuterSNARKVK = VerifyingKey<MNT6PairingEngine>;
type OuterSNARKPK = ProvingKey<MNT6PairingEngine>;
type OuterSNARKGadget = Groth16VerifierGadget<MNT6PairingEngine, MNT6PairingVar>;

fn convert_inputs(inputs: &[Fr]) -> Vec<MNT6Fr> {
    inputs
        .iter()
        .map(|input| {
            MNT6Fr::from_repr(input
                .into_repr()).unwrap()
        })
        .collect::<Vec<_>>()
}

fn mnt6(input: &Fr) -> MNT6Fr {
    MNT6Fr::from_repr(input.into_repr()).unwrap()
}

pub mod aggtransition;
pub mod merkleloop;
pub mod aggloop;
pub mod aggfinal;
pub mod select;

pub mod permutation;
pub mod as_waksman;

pub mod bucket;
pub mod tree;

#[allow(dead_code)]
fn test_circuit<T: ConstraintSynthesizer<Fr>>(circuit: T) {
    let cs_sys = ConstraintSystem::<Fr>::new();
    let cs = ConstraintSystemRef::new(cs_sys);
    println!("Testing circuit");
    circuit.generate_constraints(cs.clone()).unwrap();
    println!("Satified: {}", cs.is_satisfied().unwrap());
}

#[allow(dead_code)]
fn test_circuit2<T: ConstraintSynthesizer<MNT6Fr>>(circuit: T) {
    let cs_sys = ConstraintSystem::<MNT6Fr>::new();
    let cs = ConstraintSystemRef::new(cs_sys);
    println!("Testing circuit");
    circuit.generate_constraints(cs.clone()).unwrap();
    println!("Satified: {}", cs.is_satisfied().unwrap());
}

fn setup_circuit<T: InstructionCircuit>(circuit: T) -> (InnerSNARKPK, InnerSNARKVK) {
    let mut rng = test_rng();
    println!("Setting up circuit");
    let (pk, vk) = InnerSNARK::setup(circuit.clone(), &mut rng).unwrap();
    println!("Testing prove");
    let proof = InnerSNARK::prove(&pk, circuit.clone(), &mut rng).unwrap();
    println!("proof: {}", InnerSNARK::verify(&vk, &vec![circuit.calc_hash().clone()], &proof).unwrap());
    (pk, vk)
}



fn get_transition<C: InstructionCircuit>(circuits: &mut Vec<Transition>, lst: &[C]) {
    for i in lst {
        circuits.push(i.transition());
    }
}

fn get_transitions(c: &Collector) -> Vec<Transition> {
    let mut circuits = vec![];

    get_transition(&mut circuits, &c.add);
    get_transition(&mut circuits, &c.sub);
    get_transition(&mut circuits, &c.gt);
    get_transition(&mut circuits, &c.constant);
    get_transition(&mut circuits, &c.get);
    get_transition(&mut circuits, &c.set);
    get_transition(&mut circuits, &c.loopi);
    get_transition(&mut circuits, &c.endi);
    get_transition(&mut circuits, &c.breakno);
    get_transition(&mut circuits, &c.breakyes);

    circuits
}

use crate::aggfinal::InnerAggregateFinal;
use crate::select::make_circuits;
use crate::select::SelectionCircuit;
use crate::aggtransition::aggregate_list2;
use crate::aggtransition::aggregate_list1;
use crate::aggtransition::outer_to_inner;
use crate::aggtransition::inner_to_outer;
use crate::aggtransition::OuterSetup;
use crate::aggtransition::HashCircuit;

fn main3() {
    crate::permutation::test_permutation();
}

fn main() {
    let params = generate_hash();
    crate::tree::test_tree(&params);
}

fn main2() {

    let buffer = get_file("test.wasm".into());

    let module = parity_wasm::deserialize_buffer::<Module>(&buffer).unwrap();
    assert!(module.code_section().is_some());

    let code_section = module.code_section().unwrap(); // Part of the module with functions code

    let params = generate_hash();

    for f in code_section.bodies().iter() {
        let code = process_code(f.code().elements());
        println!("{:?}", code);
        let res = hash_code(&params, &code);
        println!("hash {}", res);
        let mut vm = VM::new(code);
        println!("vm init {}", vm.hash(&params));
        let mut c = Collector {
            add: vec![],
            sub: vec![],
            gt: vec![],
            get: vec![],
            set: vec![],
            constant: vec![],
            loopi: vec![],
            endi: vec![],
            breakno: vec![],
            breakyes: vec![],
        };
        for i in 0..32 {
            vm.step(&params, &mut c);
            println!("{}: vm hash {}", i, vm.hash(&params));
            // println!("vm state {:?}", vm);
        }

        let trs = get_transitions(&c);

        // memory::test_memory(&params, trs);

        // return;

        let (loop_proof, loop_vk, start_st, end_st) = merkleloop::handle_loop(&params, trs);

        let mut keys = vec![];
        keys.push(setup_circuit(c.add[0].clone()));
        keys.push(setup_circuit(c.sub[0].clone()));
        keys.push(setup_circuit(c.gt[0].clone()));
        keys.push(setup_circuit(c.constant[0].clone()));
        keys.push(setup_circuit(c.get[0].clone()));
        keys.push(setup_circuit(c.set[0].clone()));
        keys.push(setup_circuit(c.loopi[0].clone()));
        if c.endi.len() > 0 {
            keys.push(setup_circuit(c.endi[0].clone()));
        } else {
            keys.push(keys[0].clone());
        }
        if c.breakno.len() > 0 {
            keys.push(setup_circuit(c.breakno[0].clone()));
        } else {
            keys.push(keys[0].clone());
        }
        if c.breakyes.len() > 0 {
            keys.push(setup_circuit(c.breakyes[0].clone()));
        } else {
            keys.push(keys[0].clone());
        }
        while keys.len() < 16 {
            keys.push(keys[0].clone());
        }

        let mut rng = test_rng();

        let proof = InnerSNARK::prove(&keys[0].0, c.add[0].clone(), &mut rng).unwrap();

        let circuit = SelectionCircuit {
            hash : c.add[0].calc_hash().clone(),
            proof: proof,
            keys: keys.iter().map(|a| a.1.clone()).collect(),
            idx: 12,
            // transition: c.add[0].transition(),
        };

        let (pk, vk) = OuterSNARK::setup(circuit.clone(), &mut rng).unwrap();
        println!("Testing prove");
        let proof = OuterSNARK::prove(&pk, circuit.clone(), &mut rng).unwrap();
        println!("proof: {}", OuterSNARK::verify(&vk, &convert_inputs(&vec![circuit.hash.clone()]), &proof).unwrap());

        // setup recursive circuits
        let hash_circuit = HashCircuit {
            a: Fr::from(0),
            b: Fr::from(0),
            params: params.clone(),
        };
        let (hash_pk, hash_vk) = InnerSNARK::setup(hash_circuit.clone(), &mut rng).unwrap();

        let setup1 = OuterSetup {
            pk,
            vk,
            params: params.clone(),
        };

        let mut setups1 = vec![];
        let mut setups2 = vec![];
        let mut agg_circuits1 = vec![];
        let mut agg_circuits2 = vec![];
        let (agg_circuit_in, setup_in) = outer_to_inner(&circuit, &setup1, &hash_pk, &hash_vk);

        setups2.push(setup_in.clone());
        agg_circuits2.push(agg_circuit_in);

        for i in 0..3 {
            let (agg_circuit_out, setup_out) = inner_to_outer(&agg_circuits2[i], &setups2[i]);
            let (agg_circuit_in, setup_in) = outer_to_inner(&agg_circuit_out, &setup_out, &hash_pk, &hash_vk);
            setups2.push(setup_in);
            setups1.push(setup_out);
            agg_circuits2.push(agg_circuit_in);
            agg_circuits1.push(agg_circuit_out);
        }

        // First step is proving all instructions and then making them uniform
        let mut circuits = vec![];

        make_circuits(&mut circuits, &c.add, &keys, 0);
        make_circuits(&mut circuits, &c.sub, &keys, 1);
        make_circuits(&mut circuits, &c.gt, &keys, 2);
        make_circuits(&mut circuits, &c.constant, &keys, 3);
        make_circuits(&mut circuits, &c.get, &keys, 4);
        make_circuits(&mut circuits, &c.set, &keys, 5);
        make_circuits(&mut circuits, &c.loopi, &keys, 6);
        make_circuits(&mut circuits, &c.endi, &keys, 7);
        make_circuits(&mut circuits, &c.breakno, &keys, 8);
        make_circuits(&mut circuits, &c.breakyes, &keys, 9);

        println!("Got circuits {}", circuits.len());

        let level1 = aggregate_list2(&circuits, &setup1);

        let mut prev_level = level1;
        for i in 0..2 {
            println!("Level {} first len {}", i, prev_level.len());
            let level2 = aggregate_list1(&prev_level, &setups2[i]);
            println!("Level {} second len {}", i, level2.len());
            if level2.len() == 1 {
                let last = level2[0].clone();
                let setup = setups1[i].clone();
                let hash1 = last.calc_hash();
                let proof1 = OuterSNARK::prove(&setup.pk, last.clone(), &mut rng).unwrap();
                println!("last proof (outer): {}", OuterSNARK::verify(&setup.vk, &convert_inputs(&vec![hash1.clone()]), &proof1).unwrap());
                return
            }
            prev_level = aggregate_list2(&level2, &setups1[i]);
        }

        // prove last
        {
            let last = prev_level[0].clone();
            let setup = setups2[3].clone();
            let hash1 = last.calc_hash();
            let proof1 = InnerSNARK::prove(&setup.pk, last.clone(), &mut rng).unwrap();
            println!("last proof: {}", InnerSNARK::verify(&setup.vk, &vec![hash1.clone()], &proof1).unwrap());
            println!("root hash {}", hash1);

            let fin = InnerAggregateFinal {
                start_st: start_st.clone(),
                end_st: end_st.clone(),
                root: hash1.clone(),
                proof1,
                proof2: loop_proof,
                vk: setup.vk.clone(),
                vk_loop: loop_vk,
            };
            let (final_pk, final_vk) = OuterSNARK::setup(fin.clone(), &mut rng).unwrap();
            println!("final setup");
            let final_proof = OuterSNARK::prove(&final_pk, fin.clone(), &mut rng).unwrap();
            println!("final proof: {}", OuterSNARK::verify(&final_vk, &vec![mnt6(&start_st),mnt6(&end_st),mnt6(&hash1)], &final_proof).unwrap());

        }

    }

}

