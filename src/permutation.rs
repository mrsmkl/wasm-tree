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

fn make_switch_list(cs: ConstraintSystemRef<Fr>, a: Vec<FpVar<Fr>>, b: Vec<FpVar<Fr>>, switch: Boolean<Fr>) -> (Vec<FpVar<Fr>>,Vec<FpVar<Fr>>) {
    let mut out1 = vec![];
    let mut out2 = vec![];
    for i in 0..a.len() {
        out1.push(switch.select(&a[i], &b[i]).unwrap());
        out2.push(switch.select(&a[i], &b[i]).unwrap());
    }
    (out1, out2)
}

// get a list of variables and integer permutation?
pub fn permutation(cs: ConstraintSystemRef<Fr>, lst: Vec<FpVar<Fr>>, perm: IntegerPermutation) -> Vec<FpVar<Fr>> {
    let size = lst.len();
    let topology = AsWaksmanTopology::new(size);
    let num_columns = AsWaksmanTopology::num_colunms(size);
    let route = AsWaksmanRoute::new(&perm);
    let mut permutation = lst.clone();
    for column_idx in 0..num_columns {
        let mut next_permutation = permutation.clone();
        // println!("column topology {:?}", topology.topology[column_idx]);
        let mut p_idx = 0;
        while p_idx < size {
            let switch1 = topology.topology[column_idx][p_idx];
            match route.switches[column_idx].get(&p_idx) {
                // If is none, means straight switch (for both)
                None => {
                    // println!("1: {:?}, 2: {:?}", switch1, switch2);
                    assert!(switch1.0 == switch1.1);
                    next_permutation[switch1.0] = permutation[p_idx].clone();
                    p_idx += 1;
                }
                Some(switch_val) => {
                    let switch2 = topology.topology[column_idx][p_idx+1];
                    let bool_var = Boolean::from(AllocatedBool::<Fr>::new_witness(cs.clone(), || Ok(switch_val)).unwrap());
                    let (v1, v2) = make_switch(cs.clone(), permutation[p_idx].clone(), permutation[p_idx+1].clone(), bool_var);
                    next_permutation[switch1.0] = v2;
                    next_permutation[switch1.1] = v1;
                    p_idx += 2;
                }
            }
        }
        permutation = next_permutation;
        // println!("{} variable states {:?}", column_idx, permutation.iter().map(|v| v.value().unwrap().to_string()).collect::<Vec<_>>());
    }
    permutation
}

// get a list of variables and integer permutation?
pub fn permutation_list(cs: ConstraintSystemRef<Fr>, lst: Vec<Vec<FpVar<Fr>>>, perm: IntegerPermutation) -> Vec<Vec<FpVar<Fr>>> {
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
                    let (v1, v2) = make_switch_list(cs.clone(), permutation[packet_idx].clone(), permutation[packet_idx+1].clone(), bool_var);
                    next_permutation[switch1.0] = v2;
                    next_permutation[switch1.1] = v1;
                }
            }
        }
        permutation = next_permutation;
        // println!("{} variable states {:?}", column_idx, permutation.iter().map(|v| v.value().unwrap().to_string()).collect::<Vec<_>>());
    }
    permutation
}

use ark_relations::r1cs::ConstraintSystem;

pub fn test_permutation() {
    let size = 1 << 10;
    let mut perm = IntegerPermutation::new(size);
    for i in 0..size {
        perm.set(i, size-1-i);
    }
    /*
    let topology = AsWaksmanTopology::new(size);
    let route = AsWaksmanRoute::new(&perm);
    println!("premut {:?}", perm);
    println!("topology {:?} {}", topology, topology.topology.len());
    println!("route {:?} {}", route, route.switches.len());
    println!("checking {:?}", route.calculate_permutation());
    */

    let cs_sys = ConstraintSystem::<Fr>::new();
    let cs = ConstraintSystemRef::new(cs_sys);
    let mut vars = vec![];
    for i in 0..size {
        let var = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(i as u32))).unwrap());
        vars.push(var);
    }

    let vars_perm = permutation(cs.clone(), vars.clone(), perm.clone());
    println!("num constraints {}, valid {}", cs.num_constraints(), cs.is_satisfied().unwrap());
}
