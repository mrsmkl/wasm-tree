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

trait InstructionCircuit : ConstraintSynthesizer<Fr> + Clone {
    fn calc_hash(&self) -> Fr;
    fn transition(&self) -> Transition;
}

trait InstructionCircuit2 : ConstraintSynthesizer<MNT6Fr> + Clone {
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

#[derive(Debug, Clone)]
struct HashCircuit {
    a : Fr,
    b : Fr,
    params: PoseidonParameters<Fr>,
}

impl HashCircuit {
    fn calc_hash(&self) -> Fr {
        let mut inputs = vec![];
        inputs.push(self.a.clone());
        inputs.push(self.b.clone());
        CRH::<Fr>::evaluate(&self.params, inputs).unwrap()
    }
}

impl ConstraintSynthesizer<Fr> for HashCircuit {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<Fr>,
    ) -> Result<(), SynthesisError> {
        let a_var = FpVar::Var(
            AllocatedFp::<Fr>::new_input(cs.clone(), || Ok(self.a)).unwrap(),
        );
        let b_var = FpVar::Var(
            AllocatedFp::<Fr>::new_input(cs.clone(), || Ok(self.b)).unwrap(),
        );
        let c_var = FpVar::Var(
            AllocatedFp::<Fr>::new_input(cs.clone(), || Ok(self.calc_hash())).unwrap(),
        );
        let params_g = CRHParametersVar::<Fr>::new_witness(cs.clone(), || Ok(self.params.clone())).unwrap();
        let mut inputs = Vec::new();
        inputs.push(a_var.clone());
        inputs.push(b_var.clone());
        let hash_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs).unwrap();
        hash_gadget.enforce_equal(&c_var)?;
        Ok(())
    }
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

#[derive(Debug, Clone)]
struct InnerAggregationCircuit {
    a : Fr,
    b : Fr,
    c : Fr,
    proof1: InnerSNARKProof,
    proof2: InnerSNARKProof,
    proof_hash: InnerSNARKProof,
    vk: InnerSNARKVK,
    hash_vk: InnerSNARKVK,
}

impl InstructionCircuit2 for InnerAggregationCircuit {
    fn calc_hash(&self) -> Fr {
        self.c.clone()
    }
}

impl ConstraintSynthesizer<MNT6Fr> for InnerAggregationCircuit {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<MNT6Fr>,
    ) -> Result<(), SynthesisError> {
        let public_var = <InnerSNARKGadget as SNARKGadget<
            <MNT4PairingEngine as PairingEngine>::Fr,
            <MNT4PairingEngine as PairingEngine>::Fq,
            InnerSNARK,
        >>::InputVar::new_input(ns!(cs, "public_input"), || Ok(vec![self.c.clone()])).unwrap();

        // println!("inner public var {:?}", public_var);

        let input1_gadget = <InnerSNARKGadget as SNARKGadget<
            <MNT4PairingEngine as PairingEngine>::Fr,
            <MNT4PairingEngine as PairingEngine>::Fq,
            InnerSNARK,
        >>::InputVar::new_witness(ns!(cs, "new_input"), || Ok(vec![self.a.clone()]))
        .unwrap();
        let input2_gadget = <InnerSNARKGadget as SNARKGadget<
            <MNT4PairingEngine as PairingEngine>::Fr,
            <MNT4PairingEngine as PairingEngine>::Fq,
            InnerSNARK,
        >>::InputVar::new_witness(ns!(cs, "new_input"), || Ok(vec![self.b.clone()]))
        .unwrap();
        let input_hash_gadget = <InnerSNARKGadget as SNARKGadget<
            <MNT4PairingEngine as PairingEngine>::Fr,
            <MNT4PairingEngine as PairingEngine>::Fq,
            InnerSNARK,
        >>::InputVar::new_witness(ns!(cs, "new_input"), || Ok(vec![self.a.clone(), self.b.clone(), self.c.clone()]))
        .unwrap();

        let input1_bool_vec = input1_gadget.clone().into_iter().collect::<Vec<_>>();
        let input2_bool_vec = input2_gadget.clone().into_iter().collect::<Vec<_>>();
        let input3_bool_vec = public_var.clone().into_iter().collect::<Vec<_>>();
        let input_hash_bool_vec = input_hash_gadget.clone().into_iter().collect::<Vec<_>>();

        // println!("Input vecs {} {} {}", input1_bool_vec[0].len(), input2_bool_vec[0].len(), input3_bool_vec[0].len());

        input1_bool_vec[0].enforce_equal(&input_hash_bool_vec[0])?;
        input2_bool_vec[0].enforce_equal(&input_hash_bool_vec[1])?;
        input3_bool_vec[0].enforce_equal(&input_hash_bool_vec[2])?;

        let proof1_gadget = <InnerSNARKGadget as SNARKGadget<
            <MNT4PairingEngine as PairingEngine>::Fr,
            <MNT4PairingEngine as PairingEngine>::Fq,
            InnerSNARK,
        >>::ProofVar::new_witness(ns!(cs, "alloc_proof"), || Ok(self.proof1))
        .unwrap();
        let proof2_gadget = <InnerSNARKGadget as SNARKGadget<
            <MNT4PairingEngine as PairingEngine>::Fr,
            <MNT4PairingEngine as PairingEngine>::Fq,
            InnerSNARK,
        >>::ProofVar::new_witness(ns!(cs, "alloc_proof"), || Ok(self.proof2))
        .unwrap();
        let proof_hash_gadget = <InnerSNARKGadget as SNARKGadget<
            <MNT4PairingEngine as PairingEngine>::Fr,
            <MNT4PairingEngine as PairingEngine>::Fq,
            InnerSNARK,
        >>::ProofVar::new_witness(ns!(cs, "alloc_proof"), || Ok(self.proof_hash))
        .unwrap();
        let vk_gadget = <InnerSNARKGadget as SNARKGadget<
            <MNT4PairingEngine as PairingEngine>::Fr,
            <MNT4PairingEngine as PairingEngine>::Fq,
            InnerSNARK,
        >>::VerifyingKeyVar::new_constant(ns!(cs, "alloc_vk"), self.vk.clone())
        .unwrap();
        let hash_vk_gadget = <InnerSNARKGadget as SNARKGadget<
            <MNT4PairingEngine as PairingEngine>::Fr,
            <MNT4PairingEngine as PairingEngine>::Fq,
            InnerSNARK,
        >>::VerifyingKeyVar::new_constant(ns!(cs, "alloc_hash_vk"), self.hash_vk.clone())
        .unwrap();
        <InnerSNARKGadget as SNARKGadget<
            <MNT4PairingEngine as PairingEngine>::Fr,
            <MNT4PairingEngine as PairingEngine>::Fq,
            InnerSNARK,
        >>::verify(&vk_gadget, &input1_gadget, &proof1_gadget)
        .unwrap()
        .enforce_equal(&Boolean::constant(true))
        .unwrap();
        InnerSNARKGadget::verify(&vk_gadget, &input2_gadget, &proof2_gadget)
        .unwrap()
        .enforce_equal(&Boolean::constant(true))
        .unwrap();
        InnerSNARKGadget::verify(&hash_vk_gadget, &input_hash_gadget, &proof_hash_gadget)
        .unwrap()
        .enforce_equal(&Boolean::constant(true))
        .unwrap();

        // println!("Working: {}", cs.is_satisfied().unwrap());

        println!("recursive circuit has {} constraints", cs.num_constraints());

        Ok(())
    }
}

fn convert_inputs(inputs: &[Fr]) -> Vec<MNT6Fr> {
    inputs
        .iter()
        .map(|input| {
            MNT6Fr::from_repr(input
                .into_repr()).unwrap()
        })
        .collect::<Vec<_>>()
}

/*
fn convert_inputs2(inputs: &[MNT6Fr]) -> Vec<Fr> {
    inputs
        .iter()
        .map(|input| {
            Fr::from_repr(input
                .into_repr()).unwrap()
        })
        .collect::<Vec<_>>()
}*/

fn mnt6(input: &Fr) -> MNT6Fr {
    MNT6Fr::from_repr(input.into_repr()).unwrap()
}

#[derive(Debug, Clone)]
struct OuterAggregationCircuit {
    a : Fr,
    b : Fr,
    c : Fr,
    proof1: OuterSNARKProof,
    proof2: OuterSNARKProof,
    vk: OuterSNARKVK,
    params: PoseidonParameters<Fr>,
}

impl InstructionCircuit for OuterAggregationCircuit {
    fn calc_hash(&self) -> Fr {
        self.c.clone()
    }
    fn transition(&self) -> Transition {
        panic!("no transitions here...");
    }
}

impl ConstraintSynthesizer<Fr> for OuterAggregationCircuit {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<Fr>,
    ) -> Result<(), SynthesisError> {
        let public_var = <OuterSNARKGadget as SNARKGadget<
            <MNT6PairingEngine as PairingEngine>::Fr,
            <MNT6PairingEngine as PairingEngine>::Fq,
            OuterSNARK,
        >>::InputVar::new_witness(ns!(cs, "public_input"), || Ok(vec![mnt6(&self.c)])).unwrap();

        let input1_gadget = <OuterSNARKGadget as SNARKGadget<
            <MNT6PairingEngine as PairingEngine>::Fr,
            <MNT6PairingEngine as PairingEngine>::Fq,
            OuterSNARK,
        >>::InputVar::new_witness(ns!(cs, "new_input"), || Ok(vec![mnt6(&self.a)]))
        .unwrap();
        let input2_gadget = <OuterSNARKGadget as SNARKGadget<
            <MNT6PairingEngine as PairingEngine>::Fr,
            <MNT6PairingEngine as PairingEngine>::Fq,
            OuterSNARK,
        >>::InputVar::new_witness(ns!(cs, "new_input"), || Ok(vec![mnt6(&self.b)]))
        .unwrap();

        // inputs for hashing
        let a_var = FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(self.a.clone())).unwrap(),
        );
        let b_var = FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(self.b.clone())).unwrap(),
        );
        let c_var = FpVar::Var(
            AllocatedFp::<Fr>::new_input(cs.clone(), || Ok(self.c.clone())).unwrap(),
        );
        let params_g = CRHParametersVar::<Fr>::new_witness(cs.clone(), || Ok(self.params.clone())).unwrap();
        let mut inputs = Vec::new();
        inputs.push(a_var.clone());
        inputs.push(b_var.clone());
        let hash_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs).unwrap();
        hash_gadget.enforce_equal(&c_var)?;
    
        let a_bits = a_var.to_bits_le().unwrap();
        let b_bits = b_var.to_bits_le().unwrap();
        let c_bits = c_var.to_bits_le().unwrap();
    
        let input1_bool_vec = input1_gadget.clone().into_iter().collect::<Vec<_>>();
        let input2_bool_vec = input2_gadget.clone().into_iter().collect::<Vec<_>>();
        let input3_bool_vec = public_var.clone().into_iter().collect::<Vec<_>>();
        input1_bool_vec[0].enforce_equal(&a_bits)?;
        input2_bool_vec[0].enforce_equal(&b_bits)?;
        input3_bool_vec[0].enforce_equal(&c_bits)?;
    
        let proof1_gadget = <OuterSNARKGadget as SNARKGadget<
            <MNT6PairingEngine as PairingEngine>::Fr,
            <MNT6PairingEngine as PairingEngine>::Fq,
            OuterSNARK,
        >>::ProofVar::new_witness(ns!(cs, "alloc_proof"), || Ok(self.proof1))
        .unwrap();
        let proof2_gadget = <OuterSNARKGadget as SNARKGadget<
            <MNT6PairingEngine as PairingEngine>::Fr,
            <MNT6PairingEngine as PairingEngine>::Fq,
            OuterSNARK,
        >>::ProofVar::new_witness(ns!(cs, "alloc_proof"), || Ok(self.proof2))
        .unwrap();
        let vk_gadget = <OuterSNARKGadget as SNARKGadget<
            <MNT6PairingEngine as PairingEngine>::Fr,
            <MNT6PairingEngine as PairingEngine>::Fq,
            OuterSNARK,
        >>::VerifyingKeyVar::new_constant(ns!(cs, "alloc_vk"), self.vk.clone())
        .unwrap();
        <OuterSNARKGadget as SNARKGadget<
            <MNT6PairingEngine as PairingEngine>::Fr,
            <MNT6PairingEngine as PairingEngine>::Fq,
            OuterSNARK,
        >>::verify(&vk_gadget, &input1_gadget, &proof1_gadget)
        .unwrap()
        .enforce_equal(&Boolean::constant(true))
        .unwrap();
        OuterSNARKGadget::verify(&vk_gadget, &input2_gadget, &proof2_gadget)
        .unwrap()
        .enforce_equal(&Boolean::constant(true))
        .unwrap();
    
        // println!("Working: {}", cs.is_satisfied().unwrap());
    
        println!("recursive circuit has {} constraints", cs.num_constraints());
        Ok(())
    }
}

#[derive(Debug, Clone)]
struct InnerSetup {
    pub pk: InnerSNARKPK,
    pub hash_pk: InnerSNARKPK,
    pub vk: InnerSNARKVK,
    pub hash_vk: InnerSNARKVK, 
    pub params: PoseidonParameters<Fr>,
}

fn aggregate_level1<C:InstructionCircuit>(a: C, b: C, setup: &InnerSetup) -> InnerAggregationCircuit {
    let mut rng = test_rng();
    let hash1 = a.calc_hash();
    let hash2 = b.calc_hash();

    let hash_circuit = HashCircuit {
        a: hash1,
        b: hash2,
        params: setup.params.clone(),
    };

    let proof1 = InnerSNARK::prove(&setup.pk, a.clone(), &mut rng).unwrap();
    let proof2 = InnerSNARK::prove(&setup.pk, b.clone(), &mut rng).unwrap();
    let proof_hash = InnerSNARK::prove(&setup.hash_pk, hash_circuit.clone(), &mut rng).unwrap();

    let hash3 = hash_circuit.calc_hash();

    println!("proof1: {}", InnerSNARK::verify(&setup.vk, &vec![hash1.clone()], &proof1).unwrap());
    println!("proof2: {}", InnerSNARK::verify(&setup.vk, &vec![hash2.clone()], &proof2).unwrap());
    println!(
        "proof hash: {}",
        InnerSNARK::verify(&setup.hash_vk, &vec![hash1.clone(), hash2.clone(), hash3.clone()], &proof_hash).unwrap()
    );

    InnerAggregationCircuit {
        a: hash1,
        b: hash2,
        c: hash3,
        proof1: proof1,
        proof2: proof2,
        proof_hash: proof_hash,
        vk: setup.vk.clone(),
        hash_vk: setup.hash_vk.clone(),
    }
}

#[derive(Debug, Clone)]
struct OuterSetup {
    pub pk: OuterSNARKPK,
    pub vk: OuterSNARKVK,
    pub params: PoseidonParameters<Fr>,
}

fn aggregate_level2<C:InstructionCircuit2>(a: C, b: C, setup: &OuterSetup) -> OuterAggregationCircuit {
    let mut rng = test_rng();
    let hash1 = a.calc_hash();
    let hash2 = b.calc_hash();

    let proof1 = OuterSNARK::prove(&setup.pk, a.clone(), &mut rng).unwrap();
    let proof2 = OuterSNARK::prove(&setup.pk, b.clone(), &mut rng).unwrap();

    println!("proof1: {}", OuterSNARK::verify(&setup.vk, &convert_inputs(&vec![hash1.clone()]), &proof1).unwrap());
    println!("proof2: {}", OuterSNARK::verify(&setup.vk, &convert_inputs(&vec![hash2.clone()]), &proof2).unwrap());

    OuterAggregationCircuit {
        a: hash1,
        b: hash2,
        c: hash_pair(&setup.params, &hash1, &hash2),
        proof1: proof1,
        proof2: proof2,
        vk: setup.vk.clone(),
        params: setup.params.clone(),
    }
}

pub mod merkleloop;
pub mod aggloop;
pub mod aggfinal;

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

#[derive(Debug, Clone)]
struct SelectionCircuit {
    hash : Fr,
    proof: InnerSNARKProof,
    keys: Vec<InnerSNARKVK>,
    idx: u32,
    // transition: Transition,
}

impl InstructionCircuit2 for SelectionCircuit {
    fn calc_hash(&self) -> Fr {
        self.hash.clone()
    }
}

use ark_mnt4_298::constraints::{G2Var as MNT4G2Var, G1Var as MNT4G1Var};
use ark_r1cs_std::groups::CurveVar;
use ark_ec::AffineCurve;
use ark_groth16::constraints::VerifyingKeyVar;
use ark_r1cs_std::prelude::CondSelectGadget;
use ark_r1cs_std::R1CSVar;

impl ConstraintSynthesizer<MNT6Fr> for SelectionCircuit {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<MNT6Fr>,
    ) -> Result<(), SynthesisError> {
        let input_gadget = <InnerSNARKGadget as SNARKGadget<
            <MNT4PairingEngine as PairingEngine>::Fr,
            <MNT4PairingEngine as PairingEngine>::Fq,
            InnerSNARK,
        >>::InputVar::new_input(ns!(cs, "new_input"), || Ok(vec![self.hash.clone()]))
        .unwrap();

        let proof_gadget = <InnerSNARKGadget as SNARKGadget<
            <MNT4PairingEngine as PairingEngine>::Fr,
            <MNT4PairingEngine as PairingEngine>::Fq,
            InnerSNARK,
        >>::ProofVar::new_witness(ns!(cs, "alloc_proof"), || Ok(self.proof))
        .unwrap();

        let idx_gadget = FpVar::Var(
            AllocatedFp::<MNT6Fr>::new_witness(cs.clone(), || Ok(MNT6Fr::from(self.idx))).unwrap(),
        );

        let bools = idx_gadget.to_bits_le()?;

        // println!("bools {:?}", bools.value().unwrap());

        let keys : Vec<_> = self.keys.iter().map(|vk| {
            let VerifyingKey {
                alpha_g1,
                beta_g2,
                gamma_g2,
                delta_g2,
                gamma_abc_g1,
            } = vk.clone();
            let alpha_g1 = MNT4G1Var::constant(alpha_g1.into_projective());
            let beta_g2 = MNT4G2Var::constant(beta_g2.into_projective());
            let gamma_g2 = MNT4G2Var::constant(gamma_g2.into_projective());
            let delta_g2 = MNT4G2Var::constant(delta_g2.into_projective());
 
            let gamma_abc_g1 : Vec<MNT4G1Var> = gamma_abc_g1.iter().map(|a| MNT4G1Var::constant(a.into_projective())).collect();
            let vk_gadget : VerifyingKeyVar<MNT4PairingEngine, MNT4PairingVar> = VerifyingKeyVar {
                alpha_g1: alpha_g1,
                beta_g2: beta_g2,
                gamma_g2: gamma_g2,
                delta_g2: delta_g2,
                gamma_abc_g1: gamma_abc_g1,
            };
            vk_gadget
        }).collect();

        let mut bools2 = vec![];
        for i in bools[0..4].iter().rev() {
            bools2.push(i.clone())
        }

        let vk_gadget = VerifyingKeyVar::conditionally_select_power_of_two_vector(&bools2, &keys).unwrap();

        <InnerSNARKGadget as SNARKGadget<
            <MNT4PairingEngine as PairingEngine>::Fr,
            <MNT4PairingEngine as PairingEngine>::Fq,
            InnerSNARK,
        >>::verify(&vk_gadget, &input_gadget, &proof_gadget)
        .unwrap()
        .enforce_equal(&Boolean::constant(true))
        .unwrap();

        // println!("Working: {}", cs.is_satisfied().unwrap());

        println!("recursive circuit has {} constraints", cs.num_constraints());

        Ok(())
    }
}

fn make_circuits<C: InstructionCircuit>(circuits: &mut Vec<SelectionCircuit>, lst: &[C], keys: &[(InnerSNARKPK, InnerSNARKVK)], idx: usize) {
    let mut rng = test_rng();
    for i in lst {
        let proof = InnerSNARK::prove(&keys[idx].0, i.clone(), &mut rng).unwrap();
        circuits.push(SelectionCircuit {
            hash : i.calc_hash().clone(),
            proof: proof,
            keys: keys.iter().map(|a| a.1.clone()).collect(),
            idx: idx as u32,
            // transition: i.transition(),
        });
    }
}

fn get_transition<C: InstructionCircuit>(circuits: &mut Vec<Transition>, lst: &[C]) {
    for i in lst {
        circuits.push(i.transition());
    }
}

fn outer_to_inner<C: InstructionCircuit2>(circuit: &C, setup: &OuterSetup, hash_pk: &InnerSNARKPK, hash_vk: &InnerSNARKVK) ->
    (OuterAggregationCircuit, InnerSetup) {
    let mut rng = test_rng();
    let agg_circuit1 = aggregate_level2(circuit.clone(), circuit.clone(), setup);
    let (pk, vk) = InnerSNARK::setup(agg_circuit1.clone(), &mut rng).unwrap();

    let setup2 = InnerSetup {
        pk,
        vk,
        hash_pk: hash_pk.clone(),
        hash_vk: hash_vk.clone(),
        params: setup.params.clone(),
    };

    (agg_circuit1, setup2)
}

fn inner_to_outer<C: InstructionCircuit>(circuit: &C, setup: &InnerSetup) ->
    (InnerAggregationCircuit, OuterSetup) {
    let mut rng = test_rng();
    let agg_circuit1 = aggregate_level1(circuit.clone(), circuit.clone(), setup);
    let (pk, vk) = OuterSNARK::setup(agg_circuit1.clone(), &mut rng).unwrap();

    let setup2 = OuterSetup {
        pk,
        vk,
        params: setup.params.clone(),
    };

    (agg_circuit1, setup2)
}

fn aggregate_list2<C: InstructionCircuit2>(circuit: &[C], setup: &OuterSetup) -> Vec<OuterAggregationCircuit> {
    let mut level1 = vec![];
    for i in 0..circuit.len()/2 {
        level1.push(aggregate_level2(circuit[2*i].clone(), circuit[2*i+1].clone(), setup));
    }
    level1
}

fn aggregate_list1<C: InstructionCircuit>(circuit: &[C], setup: &InnerSetup) -> Vec<InnerAggregationCircuit> {
    let mut level1 = vec![];
    for i in 0..circuit.len()/2 {
        level1.push(aggregate_level1(circuit[2*i].clone(), circuit[2*i+1].clone(), setup));
    }
    level1
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

fn main() {

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

