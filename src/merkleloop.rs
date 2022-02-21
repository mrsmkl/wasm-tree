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
use ark_relations::r1cs::ConstraintSystem;

use crate::{VM,Transition,hash_list,hash_code,hash_pair};
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

fn merkle_loop(cs: ConstraintSystemRef<Fr>, params : &PoseidonParameters<Fr>, path: Vec<Vec<Fr>>, leafs: &Vec<Fr>, root: Fr, selectors: Vec<Vec<bool>>) {

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

    println!("Testing {}", cs.is_satisfied().unwrap());

}

fn compute_level(params : &PoseidonParameters<Fr>, l: &[Fr]) -> Vec<Fr> {
    let mut res = vec![];
    for i in 0..l.len()/2 {
        res.push(hash_pair(params, &l[2*i], &l[2*i+1]))
    };
    res
}

fn compute_levels(params : &PoseidonParameters<Fr>, l: &Vec<Fr>) -> Vec<Vec<Fr>> {
    let mut res = vec![];
    res.push(l.clone());
    let mut last = l.clone();
    while last.len() > 1 {
        last = compute_level(params, &last);
        res.push(last.clone());
    };
    res
}

fn adj(i: usize) -> usize {
    if i % 2 == 1 { i - 1 } else { i + 1 }
}

fn compute_path(levels: &Vec<Vec<Fr>>, idx: usize) -> (Vec<Fr>, Vec<bool>) {
    let mut idx = idx;
    let mut path = vec![];
    let mut selector = vec![];
    for i in 0..levels.len()-1 {
        path.push(levels[i][adj(idx)]);
        selector.push(idx % 2 == 0);
        idx = idx/2;
    }
    (path, selector)
} 

pub fn handle_loop(params : &PoseidonParameters<Fr>, transitions: Vec<Transition>) {
    let mut level1 = vec![];

    let mut leafs = vec![];
    let mut paths = vec![];
    let mut selectors = vec![];

    for i in 0..transitions.len() {
        leafs.push(Fr::from(0));
        paths.push(vec![]);
        selectors.push(vec![]);
    }

    for tr in transitions.iter() {
        level1.push(hash_pair(params, &tr.before.hash(params), &tr.after.hash(params)));
    }
    let levels = compute_levels(params, &level1);

    for (i,tr) in transitions.iter().enumerate() {
        let idx = tr.before.step_counter;
        leafs[idx] = tr.before.hash(params);
        // Last state
        if idx == transitions.len() - 1 {
            leafs.push(tr.after.hash(params))
        }
        let (path, sel) = compute_path(&levels, i);
        paths[idx] = path;
        selectors[idx] = sel;
    }

    // 

    let cs_sys = ConstraintSystem::<Fr>::new();
    let cs = ConstraintSystemRef::new(cs_sys);

    let root = levels.last().unwrap()[0].clone();

    merkle_loop(cs, params, paths, &leafs, root, selectors);
}

