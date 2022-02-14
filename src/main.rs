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
    R1CSVar,
};
use ark_crypto_primitives::CRHSchemeGadget;
use ark_relations::r1cs::ConstraintSystemRef;
use ark_relations::r1cs::SynthesisError;
use ark_ff::BigInteger;
use ark_relations::r1cs::ConstraintSynthesizer;
use ark_relations::r1cs::Field;
use ark_ff::PrimeField;
use ark_sponge::Absorb;

use ark_mnt4_298::{
    constraints::PairingVar as MNT4PairingVar, Fr, MNT4_298 as MNT4PairingEngine,
};
use ark_mnt6_298::{
    Fr as MNT6Fr,
    constraints::PairingVar as MNT6PairingVar, MNT6_298 as MNT6PairingEngine,
};
use ark_ec::mnt4::MNT4;
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
use ark_ff::ToConstraintField;
use ark_groth16::ProvingKey;
use ark_r1cs_std::ToBitsGadget;
use ark_crypto_primitives::snark::FromFieldElementsGadget;
use ark_r1cs_std::boolean::AllocatedBool;

trait HashField : Absorb + PrimeField {
}

fn get_file(fname: String) -> Vec<u8> {
    let mut file = File::open(&fname).unwrap();
    let mut buffer = Vec::<u8>::new();
    file.read_to_end(&mut buffer).unwrap();
    buffer
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
enum CodeTree {
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

fn hash_code(params: &PoseidonParameters<Fr>, code: &Vec<CodeTree>) -> Fr {
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
            CEnd => {
                let mut inputs = vec![];
                inputs.push(Fr::from(9));
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

fn generate_outer_hash() -> PoseidonParameters<MNT6Fr> {
    let mut test_rng = ark_std::test_rng();

    // TODO: The following way of generating the MDS matrix is incorrect
    // and is only for test purposes.

    let mut mds = vec![vec![]; 3];
    for i in 0..3 {
        for _ in 0..3 {
            mds[i].push(MNT6Fr::rand(&mut test_rng));
        }
    }

    let mut ark = vec![vec![]; 8 + 24];
    for i in 0..8 + 24 {
        for _ in 0..3 {
            ark[i].push(MNT6Fr::rand(&mut test_rng));
        }
    }

    let mut test_a = Vec::new();
    let mut test_b = Vec::new();
    for _ in 0..3 {
        test_a.push(MNT6Fr::rand(&mut test_rng));
        test_b.push(MNT6Fr::rand(&mut test_rng));
    }
    PoseidonParameters::<MNT6Fr>::new(8, 24, 31, mds, ark)

}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
enum ControlFrame {
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
struct VM {
    pub expr_stack : Vec<u32>,
    pub locals : Vec<u32>,
    pub control_stack: Vec<ControlFrame>,
    pub pc: Vec<CodeTree>,
}

impl VM {
    fn new(code: Vec<CodeTree>) -> Self {
        VM {
            pc: code,
            expr_stack: vec![],
            control_stack: vec![],
            locals: vec![0; 10],
        }
    }
    fn hash(&self, params: &PoseidonParameters<Fr>) -> Fr {
        let mut inputs = vec![];
        inputs.push(hash_code(&params, &self.pc));
        inputs.push(hash_list(&params, &self.expr_stack.iter().map(|a| Fr::from(*a)).collect::<Vec<Fr>>()));
        inputs.push(hash_list(&params, &self.locals.iter().map(|a| Fr::from(*a)).collect::<Vec<Fr>>()));
        inputs.push(hash_list(&params, &self.control_stack.iter().map(|a| a.hash(&params)).collect::<Vec<Fr>>()));
        CRH::<Fr>::evaluate(&params, inputs).unwrap()
    }

    fn incr_pc(&mut self) {
        self.pc = self.pc[1..].iter().map(|a| a.clone()).collect::<Vec<CodeTree>>();
    }

    fn step(&mut self, params: &PoseidonParameters<Fr>, adds : &mut Vec<AddCircuit>) {
        if self.pc.len() == 0 {
            return
        }
        let elen = self.expr_stack.len();
        let clen = self.control_stack.len();
        match &self.pc[0] {
            CAdd => {
                let before = self.clone();
                let p1 = self.expr_stack[elen - 1];
                let p2 = self.expr_stack[elen - 2];
                self.expr_stack[elen - 2] = p1 + p2;
                self.expr_stack.pop();
                self.incr_pc();
                let after = self.clone();
                adds.push(AddCircuit{
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
                self.incr_pc()
            }
            CGt => {
                let p1 = self.expr_stack[elen - 1];
                let p2 = self.expr_stack[elen - 2];
                let res = if p1 < p2 { 1 } else { 0 };
                self.expr_stack[elen - 2] = res;
                self.expr_stack.pop();
                self.incr_pc()
            }
            CConst(a) => {
                self.expr_stack.push(*a);
                self.incr_pc()
            }
            CGetLocal(a) => {
                self.expr_stack.push(self.locals[*a as usize]);
                self.incr_pc()
            }
            CSetLocal(a) => {
                self.locals[*a as usize] = self.expr_stack[elen - 1];
                self.expr_stack.pop();
                self.incr_pc()
            }
            CLoop(cont) => {
                self.control_stack.push(ControlFrame::LoopFrame(cont.clone(), self.pc.clone()));
                self.incr_pc()
            }
            CEnd => {
                if clen == 0 {
                    return
                }
                let ControlFrame::LoopFrame(c1, _) = self.control_stack[clen - 1].clone();
                self.control_stack.pop();
                self.pc = c1
            }
            CBreakIf(num) => {
                let num = *num as usize;
                let p1 = self.expr_stack[elen - 1];
                self.expr_stack.pop();
                if p1 == 1 {
                    let ControlFrame::LoopFrame(_, c1) = self.control_stack[clen - 1 - num].clone();
                    for _i in 0..=num {
                        self.control_stack.pop();
                    }
                    self.pc = c1
                } else {
                    self.incr_pc()
                }
            }
        }
    } 
}

#[derive(Debug, Clone)]
struct AddCircuit {
    before: VM,
    after: VM,
    params: PoseidonParameters<Fr>,
}

impl AddCircuit {
    fn calc_hash(&self) -> Fr {
        let mut inputs = vec![];
        inputs.push(self.before.hash(&self.params));
        inputs.push(self.after.hash(&self.params));
        CRH::<Fr>::evaluate(&self.params, inputs).unwrap()
    }
}

impl ConstraintSynthesizer<Fr> for AddCircuit {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<Fr>,
    ) -> Result<(), SynthesisError> {
        let before = self.before.clone();
        let after = self.after.clone();

        println!("before {:?}", before);
        println!("after {:?}", after);
    
        let elen = before.expr_stack.len();
    
        let pc_hash = hash_code(&self.params, &after.pc);
        let stack_hash = hash_list(&self.params, &before.expr_stack[..elen-2].iter().map(|a| Fr::from(*a)).collect::<Vec<Fr>>());
        let locals_hash = hash_list(&self.params, &before.locals.iter().map(|a| Fr::from(*a)).collect::<Vec<Fr>>());
        let control_hash = hash_list(&self.params, &before.control_stack.iter().map(|a| a.hash(&self.params)).collect::<Vec<Fr>>());

        let p1 = before.expr_stack[elen - 1];
        let p2 = before.expr_stack[elen - 2];

        let public_var = FpVar::Var(
            AllocatedFp::<Fr>::new_input(cs.clone(), || Ok(self.calc_hash())).unwrap(),
        );
    
        println!("p1 {}, p2 {}", p1, p2);
    
        let params_g = CRHParametersVar::<Fr>::new_witness(cs.clone(), || Ok(self.params.clone())).unwrap();
    
        let var_a = FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(p1))).unwrap(),
        );
        let var_b = FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(p2))).unwrap(),
        );
    
        let locals_var = FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(locals_hash)).unwrap(),
        );
        let control_var = FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(control_hash)).unwrap(),
        );
    
        let hash_pc_after_var = FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(pc_hash)).unwrap(),
        );
    
        let mut inputs_pc = Vec::new();
        inputs_pc.push(FpVar::Constant(Fr::from(1)));
        inputs_pc.push(hash_pc_after_var.clone());
        let hash_pc_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs_pc).unwrap();
    
        println!("pc hash {}", hash_code(&self.params, &before.pc));
//        println!("pc hash {}", hash_pc_gadget.value().unwrap());
    
        let mut inputs_stack_before2 = Vec::new();
        inputs_stack_before2.push(var_b.clone());
        inputs_stack_before2.push(FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(stack_hash)).unwrap(),
        ));
        let hash_stack_before2_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs_stack_before2).unwrap();
    
        println!("stack before2 {}", hash_list(&self.params, &before.expr_stack[..elen-1].iter().map(|a| Fr::from(*a)).collect::<Vec<Fr>>()));
//        println!("stack before2 {}", hash_stack_before2_gadget.value().unwrap());
    
        let mut inputs_stack_before = Vec::new();
        inputs_stack_before.push(var_a.clone());
        inputs_stack_before.push(hash_stack_before2_gadget);
        let hash_stack_before_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs_stack_before).unwrap();
    
        println!("stack before {}", hash_list(&self.params, &before.expr_stack.iter().map(|a| Fr::from(*a)).collect::<Vec<Fr>>()));
//        println!("stack before {}", hash_stack_before_gadget.value().unwrap());
    
        let mut inputs_stack_after = Vec::new();
        inputs_stack_after.push(var_a.clone() + var_b.clone());
        inputs_stack_after.push(FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(stack_hash)).unwrap(),
        ));
        let hash_stack_after_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs_stack_after).unwrap();
    
        println!("stack after {}", hash_list(&self.params, &after.expr_stack.iter().map(|a| Fr::from(*a)).collect::<Vec<Fr>>()));
//        println!("stack after {}", hash_stack_after_gadget.value().unwrap());

        // Compute VM hash before
        let mut inputs_vm_before = Vec::new();
        inputs_vm_before.push(hash_pc_gadget);
        inputs_vm_before.push(hash_stack_before_gadget);
        inputs_vm_before.push(locals_var.clone());
        inputs_vm_before.push(control_var.clone());
        let hash_vm_before_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs_vm_before).unwrap();
    
        // Compute VM hash after
        let mut inputs_vm_after = Vec::new();
        inputs_vm_after.push(hash_pc_after_var);
        inputs_vm_after.push(hash_stack_after_gadget);
        inputs_vm_after.push(locals_var.clone());
        inputs_vm_after.push(control_var.clone());
        let hash_vm_after_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs_vm_after).unwrap();

        let mut inputs_transition = Vec::new();
        inputs_transition.push(hash_vm_before_gadget.clone());
        inputs_transition.push(hash_vm_after_gadget.clone());
        let hash_transition_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs_transition).unwrap();
        hash_transition_gadget.enforce_equal(&public_var)?;
    
        println!("Made circuit");
        println!("before {}, after {}", before.hash(&self.params), after.hash(&self.params));
//        println!("before {}, after {}", hash_vm_before_gadget.value().unwrap(), hash_vm_after_gadget.value().unwrap());

        Ok(())
    }
}

fn hash(params: &PoseidonParameters<Fr>, a: &Fr, b: &Fr) -> Fr {
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

        println!("Input vecs {} {} {}", input1_bool_vec[0].len(), input2_bool_vec[0].len(), input3_bool_vec[0].len());

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

impl ConstraintSynthesizer<Fr> for OuterAggregationCircuit {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<Fr>,
    ) -> Result<(), SynthesisError> {
        let public_var = <OuterSNARKGadget as SNARKGadget<
            <MNT6PairingEngine as PairingEngine>::Fr,
            <MNT6PairingEngine as PairingEngine>::Fq,
            OuterSNARK,
        >>::InputVar::new_input(ns!(cs, "public_input"), || Ok(vec![mnt6(&self.c)])).unwrap();
    
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
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(self.c.clone())).unwrap(),
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

fn aggregate_level1(a: AddCircuit, b: AddCircuit, pk: &InnerSNARKPK, hash_pk: &InnerSNARKPK,
    vk: &InnerSNARKVK, hash_vk: &InnerSNARKVK) -> (InnerAggregationCircuit, Fr) {
    let mut rng = test_rng();
    let hash1 = a.calc_hash();
    let hash2 = b.calc_hash();

    let hash_circuit = HashCircuit {
        a: hash1,
        b: hash2,
        params: a.params.clone(),
    };

    let proof1 = InnerSNARK::prove(&pk, a.clone(), &mut rng).unwrap();
    let proof2 = InnerSNARK::prove(&pk, b.clone(), &mut rng).unwrap();
    let proof_hash = InnerSNARK::prove(&hash_pk, hash_circuit.clone(), &mut rng).unwrap();

    let hash3 = hash_circuit.calc_hash();

    println!("proof1: {}", InnerSNARK::verify(&vk, &vec![hash1.clone()], &proof1).unwrap());
    println!("proof2: {}", InnerSNARK::verify(&vk, &vec![hash2.clone()], &proof2).unwrap());
    println!(
        "proof hash: {}",
        InnerSNARK::verify(&hash_vk, &vec![hash1.clone(), hash2.clone(), hash3.clone()], &proof_hash).unwrap()
    );

    let agg_circuit = InnerAggregationCircuit {
        a: hash1,
        b: hash2,
        c: hash3,
        proof1: proof1,
        proof2: proof2,
        proof_hash: proof_hash,
        vk: vk.clone(),
        hash_vk: hash_vk.clone(),
    };

    (agg_circuit, hash3)
}

fn handle_recursive_groth(a: Vec<AddCircuit>) {
    let mut rng = test_rng();

    let hash1 = a[0].calc_hash();
    let hash2 = a[1].calc_hash();
    let params = &a[0].params;

    let hash_circuit = HashCircuit {
        a: hash1,
        b: hash2,
        params: a[0].params.clone(),
    };

    let (pk, vk) = InnerSNARK::setup(a[0].clone(), &mut rng).unwrap();
    let (hash_pk, hash_vk) = InnerSNARK::setup(hash_circuit.clone(), &mut rng).unwrap();

    let (agg_circuit1, hash3) = aggregate_level1(a[0].clone(), a[1].clone(), &pk, &hash_pk, &vk, &hash_vk);
    let (agg_circuit2, hash4) = aggregate_level1(a[2].clone(), a[3].clone(), &pk, &hash_pk, &vk, &hash_vk);

    let (inner_pk, inner_vk) = OuterSNARK::setup(agg_circuit1.clone(), &mut rng).unwrap();

    let inner_proof1 = OuterSNARK::prove(&inner_pk, agg_circuit1.clone(), &mut rng).unwrap();
    println!("inner proof 1: {}", OuterSNARK::verify(&inner_vk, &convert_inputs(&vec![hash3.clone()]), &inner_proof1).unwrap());

    let inner_proof2 = OuterSNARK::prove(&inner_pk, agg_circuit2.clone(), &mut rng).unwrap();
    println!("inner proof 2: {}", OuterSNARK::verify(&inner_vk, &convert_inputs(&vec![hash4.clone()]), &inner_proof2).unwrap());

    let hash5 = hash(params, &hash3, &hash4);

    let agg_circuit_outer = OuterAggregationCircuit {
        a: hash3,
        b: hash4,
        c: hash5,
        proof1: inner_proof1,
        proof2: inner_proof2,
        vk: inner_vk.clone(),
        params: params.clone(),
    };

    let (outer_pk, outer_vk) = InnerSNARK::setup(agg_circuit_outer.clone(), &mut rng).unwrap();
    let outer_proof = InnerSNARK::prove(&outer_pk, agg_circuit_outer.clone(), &mut rng).unwrap();
    let outer_input = <OuterSNARKGadget as SNARKGadget<
        <MNT6PairingEngine as PairingEngine>::Fr,
        <MNT6PairingEngine as PairingEngine>::Fq,
        OuterSNARK,
        >>::InputVar::repack_input(&vec![mnt6(&hash5)]);
    println!("outer proof: {}", InnerSNARK::verify(&outer_vk, &outer_input, &outer_proof).unwrap());

}

fn merkle_circuit(cs: ConstraintSystemRef<Fr>, params : &PoseidonParameters<Fr>, path: &[Fr], root: FpVar<Fr>, selectors: &[bool]) -> FpVar<Fr> {

    let first = FpVar::Var(
        AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(path[0].clone())).unwrap(),
    );

    let mut last = first.clone();

    // println!("Working: {}", cs.is_satisfied().unwrap());
    for (i, next_hash) in path[1..].iter().enumerate() {
        let b_var = FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(next_hash.clone())).unwrap(),
        );
        let bool_var = Boolean::from(
            AllocatedBool::<Fr>::new_witness(cs.clone(), || Ok(selectors[i+1].clone())).unwrap(),
        );
        let params_g = CRHParametersVar::<Fr>::new_witness(cs.clone(), || Ok(params.clone())).unwrap();
        let mut inputs = Vec::new();
        inputs.push(bool_var.select(&last, &b_var).unwrap());
        inputs.push(bool_var.select(&b_var, &last).unwrap());
        let hash_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs[..]).unwrap();
        last = hash_gadget
    }

    last.enforce_equal(&root).unwrap();

    println!("circuit has {} constraints", cs.num_constraints());

    first
}

fn merkle_loop(cs: ConstraintSystemRef<Fr>, params : &PoseidonParameters<Fr>, path: Vec<Vec<Fr>>, leafs: Vec<Fr>, root: Fr, selectors: Vec<Vec<bool>>) {

    let first = FpVar::Var(
        AllocatedFp::<Fr>::new_input(cs.clone(), || Ok(leafs[0].clone())).unwrap(),
    );
    let end_var = FpVar::Var(
        AllocatedFp::<Fr>::new_input(cs.clone(), || Ok(leafs[leafs.len()-1].clone())).unwrap(),
    );
    let root_var = FpVar::Var(
        AllocatedFp::<Fr>::new_input(cs.clone(), || Ok(root.clone())).unwrap(),
    );

    let mut last = first.clone();
    let params_g = CRHParametersVar::<Fr>::new_witness(cs.clone(), || Ok(params.clone())).unwrap();

    for (i,p) in path.iter().enumerate() {
        let leaf_var = merkle_circuit(cs.clone(), params, p, root_var.clone(), &selectors[i]);
        // check leafs
        let next = FpVar::Var(
            AllocatedFp::<Fr>::new_input(cs.clone(), || Ok(leafs[i+1].clone())).unwrap(),
        );
        let mut inputs = Vec::new();
        inputs.push(last.clone());
        inputs.push(next.clone());
        let hash_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs[..]).unwrap();
        hash_gadget.enforce_equal(&leaf_var);
        last = next
    }
    last.enforce_equal(&end_var).unwrap();

}

fn main() {
    let params = generate_hash();
    let selectors = vec![false, false, false, false];
    let root = Fr::one();
    let path = vec![root, root, root, root];
    let cs_sys = ConstraintSystem::<Fr>::new();
    let cs = ConstraintSystemRef::new(cs_sys);
    // merkle_circuit(cs, &params, &path, root.clone(), &selectors);
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
        let mut adds = vec![];
        for i in 0..60 {
            vm.step(&params, &mut adds);
            println!("{}: vm hash {}", i, vm.hash(&params));
            // println!("vm state {:?}", vm);
        }
        handle_recursive_groth(adds)
    }

}

