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
use ark_r1cs_std::boolean::{AllocatedBool,Boolean};
use std::cmp::Ordering;

use crate::{VM,Transition,hash_code};
use crate::InstructionCircuit;
use crate::CodeTree;

use ark_r1cs_std::R1CSVar;

mod as_waksman;

fn make_switch(cs: ConstraintSystemRef<Fr>, a: FpVar<Fr>, b: FpVar<Fr>, switch: Boolean<Fr>) -> (FpVar<Fr>,FpVar<Fr>) {
    let out1 = bool_var.select(&a, &b);
    let out2 = bool_var.select(&b, &a);
    (out1, out2)
}

// get a list of variables and integer permutation?



