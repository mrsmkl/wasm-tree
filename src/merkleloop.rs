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
use ark_r1cs_std::boolean::AllocatedBool;
use ark_r1cs_std::boolean::Boolean;

use crate::{VM,Transition,hash_list,hash_code};
use crate::InstructionCircuit;

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
        hash_gadget.enforce_equal(&leaf_var).unwrap();
        last = next
    }
    last.enforce_equal(&end_var).unwrap();

}
