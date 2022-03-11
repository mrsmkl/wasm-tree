use crate::as_waksman::IntegerPermutation;
use crate::as_waksman::AsWaksmanRoute;
use crate::as_waksman::AsWaksmanTopology;
use crate::Transition;

use ark_mnt4_298::Fr;
use ark_crypto_primitives::crh::poseidon::constraints::CRHGadget;
use ark_r1cs_std::fields::fp::FpVar;
use ark_crypto_primitives::crh::poseidon::constraints::CRHParametersVar;
use ark_crypto_primitives::CRHSchemeGadget;
use ark_sponge::poseidon::PoseidonParameters;
use ark_relations::r1cs::ConstraintSystemRef;
use ark_r1cs_std::prelude::CondSelectGadget;
use ark_r1cs_std::boolean::AllocatedBool;
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::fp::AllocatedFp;

#[derive(Debug, Clone)]
struct Step {
    a: usize,
    b: usize,
    c: usize,
    input: i32,
}

fn make_bools(cs: &ConstraintSystemRef<Fr>, mem_size: usize, a: usize) -> Vec<Boolean<Fr>> {
    let mut a_bools = vec![];
    for i in 0..mem_size {
        let is_set = (a >> i) % 2 == 1;
        let bool_var = Boolean::from(AllocatedBool::<Fr>::new_witness(cs.clone(), || Ok(is_set)).unwrap());
        a_bools.push(bool_var)
    }
    a_bools
}

fn hash_step(
    cs: &ConstraintSystemRef<Fr>,
    step: Step,
    params: &PoseidonParameters<Fr>,
    params_g: &CRHParametersVar::<Fr>,
    vars: &[FpVar<Fr>], // memory
    input: FpVar<Fr>, // input from permutation
    mem_size: usize,
) -> Vec<FpVar<Fr>> { // output memory
    let mut inputs = vec![];
    for v in vars.iter() {
        inputs.push(v.clone());
    }
    inputs.push(input);

    let a_bools = make_bools(cs, mem_size, step.a);
    let b_bools = make_bools(cs, mem_size, step.b);

    let a_var = FpVar::conditionally_select_power_of_two_vector(&a_bools, &inputs).unwrap();
    let b_var = FpVar::conditionally_select_power_of_two_vector(&b_bools, &inputs).unwrap();

    let c_var = CRHGadget::<Fr>::evaluate(&params_g, &vec![a_var, b_var]).unwrap();

    let mut outputs = vec![];
    let c_idx_var = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(step.c as u32))).unwrap());
    for (i,v) in vars.iter().enumerate() {
        let idx_var = FpVar::Constant(Fr::from(i as u32));
        let bool_var = idx_var.is_eq(&c_idx_var).unwrap();
        let out_var = bool_var.select(&c_var, &v).unwrap();
        outputs.push(out_var);
    };
    outputs
}
