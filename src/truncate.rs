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
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::fields::FieldVar;
use std::cmp::Ordering;
use ark_relations::r1cs::ConstraintSystem;
use ark_r1cs_std::ToBitsGadget;
use ark_r1cs_std::R1CSVar;

// truncate to 200 bits

fn truncate(v: FpVar<Fr>) -> FpVar<Fr> {
    let bits = v.to_bits_le().unwrap();
    // how to convert bits to var?
    let res = Boolean::le_bits_to_fp_var(&bits[0..200]).unwrap();
    res
}

// This will compress hashes of transitions...
fn sum_transitions(v: Vec<FpVar<Fr>>) -> FpVar<Fr> {
    let mut acc = FpVar::Constant(Fr::from(0));
    for elem in v {
        acc = acc + truncate(elem)
    }
    acc
}

fn sum_sequence(
    params: &PoseidonParameters<Fr>,
    params_g: &CRHParametersVar::<Fr>,
    v: Vec<FpVar<Fr>>,
) -> FpVar<Fr> {
    let mut vars = vec![];
    for i in 0..v.len()-1 {
        let hash_var = CRHGadget::<Fr>::evaluate(&params_g, &vec![v[i].clone(), v[i+1].clone()]).unwrap();
        vars.push(hash_var)
    }
    sum_transitions(vars)
}

pub fn test(params: &PoseidonParameters<Fr>) {
    let cs_sys = ConstraintSystem::<Fr>::new();
    let cs = ConstraintSystemRef::new(cs_sys);
    let params_g = CRHParametersVar::<Fr>::new_witness(cs.clone(), || Ok(params.clone())).unwrap();

    let var = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(100))).unwrap());
    let tvar = truncate(var.clone());

    println!("truncated {}", tvar.value().unwrap());

    println!("num constraints {}, valid {}", cs.num_constraints(), cs.is_satisfied().unwrap());
}
