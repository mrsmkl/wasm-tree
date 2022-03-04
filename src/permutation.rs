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

use crate::as_waksman::IntegerPermutation;

use ark_r1cs_std::R1CSVar;
use crate::as_waksman::AsWaksmanRoute;
use crate::as_waksman::AsWaksmanTopology;

fn make_switch(cs: ConstraintSystemRef<Fr>, a: FpVar<Fr>, b: FpVar<Fr>, switch: Boolean<Fr>) -> (FpVar<Fr>,FpVar<Fr>) {
    let out1 = switch.select(&a, &b).unwrap();
    let out2 = switch.select(&b, &a).unwrap();
    (out1, out2)
}

// get a list of variables and integer permutation?
fn permutation(cs: ConstraintSystemRef<Fr>, lst: Vec<FpVar<Fr>>, perm: IntegerPermutation) -> Vec<FpVar<Fr>> {
    let size = lst.len();
    let topology = AsWaksmanTopology::new(size);
    let num_columns = AsWaksmanTopology::num_colunms(size);
    let route = AsWaksmanRoute::new(&perm);
    let mut permutation = lst.clone();
    for column_idx in 0..num_columns {
        let mut next_permutation = permutation.clone();
        for packet_idx in 0..size/2 {
            let packet_idx = packet_idx*2;
            let switch1 = topology.topology[column_idx][packet_idx];
            let switch2 = topology.topology[column_idx][packet_idx+1];
            match route.switches[column_idx].get(&packet_idx) {
                // If is none, means straight switch (for both)
                None => {
                    assert!(switch1.0 == switch1.1 && switch2.0 == switch2.1);
                    next_permutation[switch1.0] = permutation[packet_idx].clone();
                    next_permutation[switch2.0] = permutation[packet_idx+1].clone();
                }
                Some(switch_val) => {
                    let bool_var = Boolean::from(AllocatedBool::<Fr>::new_witness(cs.clone(), || Ok(switch_val)).unwrap());
                    let (v1, v2) = make_switch(cs.clone(), permutation[packet_idx].clone(), permutation[packet_idx+1].clone(), bool_var);
                    next_permutation[switch1.0] = v2;
                    next_permutation[switch1.1] = v1;
                }
            }
        }
        permutation = next_permutation;
        println!("{} variable states {:?}", column_idx, permutation.iter().map(|v| v.value().unwrap().to_string()).collect::<Vec<_>>());
    }
    permutation
}

use ark_relations::r1cs::ConstraintSystem;

pub fn test_permutation() {
    let size = 16;
    let mut perm = IntegerPermutation::new(size);
    for i in 0..size {
        perm.set(i, size-1-i);
    }
    let topology = AsWaksmanTopology::new(size);
    let route = AsWaksmanRoute::new(&perm);
    println!("premut {:?}", perm);
    println!("topology {:?} {}", topology, topology.topology.len());
    println!("route {:?} {}", route, route.switches.len());
    println!("checking {:?}", route.calculate_permutation());

    let cs_sys = ConstraintSystem::<Fr>::new();
    let cs = ConstraintSystemRef::new(cs_sys);
    let mut vars = vec![];
    for i in 0..size {
        let var = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(i as u32))).unwrap());
        vars.push(var);
    }

    let vars_perm = permutation(cs.clone(), vars.clone(), perm.clone());
}
