use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::{
    fields::fp::{AllocatedFp, FpVar},
};
use ark_crypto_primitives::crh::poseidon::CRH;
use ark_crypto_primitives::crh::poseidon::constraints::{CRHGadget, CRHParametersVar};
use ark_mnt4_298::Fr;
use ark_relations::r1cs::ConstraintSynthesizer;
use ark_crypto_primitives::{CRHSchemeGadget, CRHScheme};
use ark_relations::r1cs::SynthesisError;
use ark_relations::r1cs::ConstraintSystemRef;
use ark_r1cs_std::eq::EqGadget;
use ark_sponge::poseidon::PoseidonParameters;
use ark_relations::r1cs::ConstraintSystem;
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::boolean::AllocatedBool;
use ark_r1cs_std::select::CondSelectGadget;
use ark_r1cs_std::fields::FieldVar;

use crate::hash::{Params,poseidon,poseidon_gadget};

// New version of VM

#[derive(Debug, Clone)]
pub struct VM {
    pub registers: Vec<u64>,
    pub params: Params,
    pub control_pointer: usize,
    pub frame_pointer: usize,
    pub mem_counter: usize,
    // pub pc: Vec<CodeTree>,
    pub pc: Vec<u64>,
}

pub struct VMVar {
    pub registers: Vec<FpVar<Fr>>,
    pub control_pointer: FpVar<Fr>,
    pub frame_pointer: FpVar<Fr>,
    pub mem_counter: FpVar<Fr>,
    pub pc_hash: FpVar<Fr>,
}

fn hash_code(params: &Params, code: &[u64]) -> Fr {
    let mut res = Fr::from(0);
    for op in code.iter().rev() {
        // println!("hashing {:?}", op);
        let mut inputs = vec![];
        inputs.push(Fr::from(*op));
        inputs.push(res);
        res = poseidon(&params, inputs);
    }
    res
}

fn decode(a: u64, n: usize) -> Vec<bool> {
    let mut res = vec![];
    let mut a = a;
    for i in 0..n {
        let x = a%2;
        res.push(if x == 0 { false } else { true });
        a = a/2;
    }
    res
}

fn decode_var(cs: &ConstraintSystemRef<Fr>, a: u64, n: usize) -> Vec<Boolean<Fr>> {
    decode(a, n).iter().map(|b| Boolean::from(AllocatedBool::<Fr>::new_witness(cs.clone(), || Ok(b)).unwrap())).collect::<Vec<_>>()
}

fn decode2(a: u128, n: usize) -> Vec<bool> {
    let mut res = vec![];
    let mut a = a;
    for i in 0..n {
        let x = a%2;
        res.push(if x == 0 { false } else { true });
        a = a/2;
    }
    res
}

fn decode_var2(cs: &ConstraintSystemRef<Fr>, a: u128, n: usize) -> Vec<Boolean<Fr>> {
    decode2(a, n).iter().map(|b| Boolean::from(AllocatedBool::<Fr>::new_witness(cs.clone(), || Ok(b)).unwrap())).collect::<Vec<_>>()
}

fn decode_op(a: u64) -> (u64, usize, usize) {
    (a%16, ((a/16)%4) as usize, ((a/(16*4))%4) as usize)
}

fn compute(op: u64, a: u64, b: u64) -> u128 {
    if op == 0 {
        (a as u128) + (b as u128)
    } else if op == 1 {
        (a as u128) * (b as u128)
    } else /* if op == 2 */ {
        (1u128 << 64) + (a as u128) - (b as u128)
    }
}

fn generate_step(cs: &ConstraintSystemRef<Fr>, before: VM, before_var: VMVar) -> Result<VMVar, SynthesisError> {
    // For PC, just make the hash
    let params = &before.params;
    let inst = before.pc[0];
    let inst_bools = decode_var(cs, inst, 16);
    let next_pc_hash = hash_code(params, &before.pc[1..]);
    let next_hash = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(next_pc_hash))).unwrap());
    // Instruction comes from boolean wires...
    let inst_var = Boolean::le_bits_to_fp_var(&inst_bools).unwrap();
    let prev_hash = poseidon_gadget(params, vec![inst_var, next_hash]);
    before_var.pc_hash.enforce_equal(&prev_hash);

    // Select registers
    let a_var = FpVar::conditionally_select_power_of_two_vector(&inst_bools[0..2], &before_var.registers).unwrap();
    let b_var = FpVar::conditionally_select_power_of_two_vector(&inst_bools[2..4], &before_var.registers).unwrap();

    let add_var = a_var.clone() + b_var.clone();
    let mul_var = a_var.clone() * b_var.clone();
    let minus_var = (a_var.clone() - b_var.clone()) + FpVar::constant(Fr::from(1u128 << 64));
    let neg_var = FpVar::constant(Fr::from(1u128 << 64)) - a_var.clone();

    // result will have 64 bits
    // or for multiplication there will be 128 bits
    let (op, r1, r2) = decode_op(inst);
    let result = compute(op, before.registers[r1], before.registers[r2]);
    let result_bools = decode_var2(cs, result, 128);
    let result_var = Boolean::le_bits_to_fp_var(&result_bools[0..64]).unwrap();
    let over_var = Boolean::le_bits_to_fp_var(&result_bools[64..128]).unwrap();
    let combined_var = result_var.clone() + FpVar::constant(Fr::from(1u128 << 64)) * over_var.clone();

    let ops = vec![add_var, mul_var, minus_var, neg_var];
    let selected = FpVar::conditionally_select_power_of_two_vector(&inst_bools[4..6], &ops).unwrap();

    // Then need to select the result registers

    Ok(before_var)
}

