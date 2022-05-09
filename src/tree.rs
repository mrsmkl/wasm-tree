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
use ark_relations::r1cs::ConstraintSystem;

use crate::hash_pair;

#[derive(Debug, Clone)]
struct Tree {
    nodes: Vec<(usize, usize)>,
}

fn hash_tree(
    cs: &ConstraintSystemRef<Fr>,
    tree: &Tree,
    params: &PoseidonParameters<Fr>,
    params_g: &CRHParametersVar::<Fr>,
    inputs: &Vec<FpVar<Fr>>, // Some of these inputs might be zeroes
    values: &Vec<Fr>, // computed values of inputs
) -> FpVar<Fr> {
    // add nodes to values
    let mut values = values.clone();
    // inputs and internal nodes
    let mut inputs = inputs.clone();
    let mut nodes = vec![];
    // route inputs
    let mut perm = IntegerPermutation::new(inputs.len() + tree.nodes.len() - 1);
    for (i, (a,b)) in tree.nodes.iter().enumerate() {
        let h = hash_pair(&params, &values[*a], &values[*b]);
        values.push(h.clone());
        let var = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(h)).unwrap());
        // last node only has output
        if i != tree.nodes.len() - 1 {
            inputs.push(var.clone());
        }
        nodes.push(var.clone());
        perm.set(i*2, *a);
        perm.set(i*2+1, *b);
    }
    // println!("permutation {:?}", perm);
    let inputs = crate::permutation::permutation(cs.clone(), inputs, perm);
    // create hashes, check that inner nodes are correct
    for (i, (a,b)) in tree.nodes.iter().enumerate() {
        let a_var = inputs[*a].clone();
        let b_var = inputs[*b].clone();
        let hash_var = CRHGadget::<Fr>::evaluate(&params_g, &vec![a_var, b_var]).unwrap();
        hash_var.enforce_equal(&nodes[i]).unwrap();
    }
    nodes.last().unwrap().clone()
}

pub fn test_tree(params: &PoseidonParameters<Fr>) {
    let cs_sys = ConstraintSystem::<Fr>::new();
    let cs = ConstraintSystemRef::new(cs_sys);
    let params_g = CRHParametersVar::<Fr>::new_witness(cs.clone(), || Ok(params.clone())).unwrap();

    let mut acc = 0;
    let mut sz = 1024;
    let mut vars = vec![];
    let mut inputs = vec![];
    for i in 0..sz {
        let fr = Fr::from(i as u32);
        vars.push(FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(fr)).unwrap()));
        inputs.push(fr)
    }
    let mut nodes = vec![];
    while sz > 0 {
        for i in 0..sz/2 {
            nodes.push((acc + i*2, acc + i*2+1));
        }
        acc += sz;
        sz = sz/2;
    }
    // println!("{:?}", nodes);
    let tree = Tree {nodes};
    let _res = hash_tree(&cs, &tree, &params, &params_g, &vars, &inputs);
    println!("num constraints {}, valid {}", cs.num_constraints(), cs.is_satisfied().unwrap());
}
