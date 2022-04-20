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

use ark_std::UniformRand;
use ark_ff::Field;
use ark_r1cs_std::fields::FieldVar;
use ark_r1cs_std::R1CSVar;
use ark_r1cs_std::boolean::Boolean;

use crate::{VM,Transition,hash_list,hash_code};
use crate::InstructionCircuit;

fn shr_bool(a: Vec<Boolean<Fr>>, r: usize) -> Vec<Boolean<Fr>> {
    let mut out = vec![];
    for i in 0..a.len() {
        out.push(if i+r >= 64 { Boolean::FALSE } else { a[i-r].clone() })
    }
    out
}

fn shl_bool(a: Vec<Boolean<Fr>>, r: usize) -> Vec<Boolean<Fr>> {
    let mut out = vec![];
    for i in 0..a.len() {
        out.push(if i < r { Boolean::FALSE } else { a[i-r].clone() })
    }
    out
}

fn or_bool(a: Vec<Boolean<Fr>>, b: Vec<Boolean<Fr>>) -> Vec<Boolean<Fr>> {
    let mut out = vec![];
    for i in 0..a.len() {
        out.push(a[i].clone().or(&b[i]).unwrap())
    }
    out
}

fn xor_bool(a: Vec<Boolean<Fr>>, b: Vec<Boolean<Fr>>) -> Vec<Boolean<Fr>> {
    let mut out = vec![];
    for i in 0..a.len() {
        out.push(a[i].clone().xor(&b[i]).unwrap())
    }
    out
}

fn perm_d(a: Vec<Boolean<Fr>>, b: Vec<Boolean<Fr>>, shl: usize, shr: usize) -> Vec<Boolean<Fr>> {
    // d = b ^ (a<<shl | a>>shr)

    let aux0 = shr_bool(a.clone(), shr);
    let aux1 = shl_bool(a, shl);

    let aux2 = or_bool(aux0, aux1);
    xor_bool(b, aux2)
}


