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

use ark_r1cs_std::R1CSVar;
use crate::aggloop::LoopCircuit;

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
            AllocatedBool::<Fr>::new_witness(cs.clone(), || Ok(selectors[i].clone())).unwrap(),
        );
        let params_g = CRHParametersVar::<Fr>::new_witness(cs.clone(), || Ok(params.clone())).unwrap();
        let mut inputs = Vec::new();
        inputs.push(bool_var.select(&last, &b_var).unwrap());
        inputs.push(bool_var.select(&b_var, &last).unwrap());
        let hash_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs[..]).unwrap();
        // println!("Got hash {}, last {}", hash_gadget.value().unwrap(), last.value().unwrap());
        last = hash_gadget
    }

    // TODO: check this
    last.enforce_equal(&root).unwrap();

    first
}

fn merkle_loop(cs: ConstraintSystemRef<Fr>, params : &PoseidonParameters<Fr>, path: &[Vec<Fr>], leafs: &[Fr], root: Fr, selectors: Vec<Vec<bool>>) {

    let len = path.len();

    let first = FpVar::Var(
        AllocatedFp::<Fr>::new_input(cs.clone(), || Ok(leafs[0].clone())).unwrap(),
    );
    let end_var = FpVar::Var(
        AllocatedFp::<Fr>::new_input(cs.clone(), || Ok(leafs[len].clone())).unwrap(),
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
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(leafs[i+1].clone())).unwrap(),
        );
        let mut inputs = Vec::new();
        inputs.push(last.clone());
        inputs.push(next.clone());
        let hash_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs[..]).unwrap();
        hash_gadget.enforce_equal(&leaf_var).unwrap();
        last = next
    }
    last.enforce_equal(&end_var).unwrap();

    // println!("Testing {}", cs.is_satisfied().unwrap());
    println!("circuit has {} constraints", cs.num_constraints());

}

#[derive(Debug, Clone)]
struct MerkleLoop {
    params : PoseidonParameters<Fr>,
    paths: Vec<Vec<Fr>>,
    leafs: Vec<Fr>,
    root: Fr, 
    selectors: Vec<Vec<bool>>,
}

impl LoopCircuit for MerkleLoop {
    fn get_inputs(&self) -> Vec<Fr> {
        vec![self.leafs[0].clone(), self.leafs[self.leafs.len()-1].clone(), self.root.clone()]
    }
    fn get(&self) -> (Fr,Fr,Fr) {
        (self.leafs[0].clone(), self.leafs[self.leafs.len()-1].clone(), self.root.clone())
    }
}

impl ConstraintSynthesizer<Fr> for MerkleLoop {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        merkle_loop(cs, &self.params, &self.paths, &self.leafs, self.root, self.selectors);
        Ok(())
    }
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
    // println!("Computing path {}", idx);
    let mut idx = idx;
    let mut path = vec![];
    path.push(levels[0][idx].clone());
    let mut selector = vec![];
    for i in 0..levels.len()-1 {
        path.push(levels[i][adj(idx)]);
        selector.push(idx % 2 == 0);
        // println!("making path {} {} elem {}", levels[i][adj(idx)], idx%2 == 0, levels[i][idx]);
        idx = idx/2;
    }
    (path, selector)
}

use ark_std::test_rng;
use crate::InnerSNARK;
use ark_crypto_primitives::CircuitSpecificSetupSNARK;
use ark_crypto_primitives::SNARK;

use crate::aggloop::{OuterSetup,InnerSetup};
use crate::aggloop::inner_to_outer;
use crate::aggloop::outer_to_inner;
use crate::aggloop::{aggregate_list1, aggregate_list2};
use crate::aggloop::LoopCircuit2;
use crate::OuterSNARK;
use crate::InnerSNARKProof;
use crate::InnerSNARKVK;

pub fn handle_loop(params : &PoseidonParameters<Fr>, transitions: Vec<Transition>) -> (InnerSNARKProof, InnerSNARKVK, Fr, Fr) {
    let mut level1 = vec![];

    let mut leafs = vec![];
    let mut paths = vec![];
    let mut selectors = vec![];

    for _i in 0..transitions.len() {
        leafs.push(Fr::from(0));
        paths.push(vec![]);
        selectors.push(vec![]);
    }

    for tr in transitions.iter() {
        level1.push(hash_pair(params, &tr.before.hash(params), &tr.after.hash(params)));
    }
    let levels = compute_levels(params, &level1);
    println!("Got levels {}", levels.len());

    for (i,tr) in transitions.iter().enumerate() {
        let idx = tr.before.step_counter;
        leafs[idx] = tr.before.hash(params);
        // println!("Got tr {} {}", idx, leafs[idx]);
        // Last state
        if idx == transitions.len() - 1 {
            leafs.push(tr.after.hash(params))
        }
        let (path, sel) = compute_path(&levels, i);
        paths[idx] = path;
        selectors[idx] = sel;
    }

    let root = levels.last().unwrap()[0].clone();

    // 

    /*
     let cs_sys = ConstraintSystem::<Fr>::new();
     let cs = ConstraintSystemRef::new(cs_sys);
     merkle_loop(cs, params, &paths, &leafs, root, selectors);
    */

    let mut circuits = vec![];
    let num = 16;
    let len = transitions.len();
    let slice = len / num;

    for i in 0..num {
        circuits.push(MerkleLoop {
            params: params.clone(),
            paths: paths[slice*i..slice*(i+1)].to_vec(),
            leafs: leafs[slice*i..slice*(i+1)+1].to_vec(),
            root,
            selectors: selectors[slice*i..slice*(i+1)].to_vec(),
        });
    }

    let circuit = circuits[0].clone();

    let mut rng = test_rng();
    println!("Setting up circuit");
    let (pk, vk) = InnerSNARK::setup(circuit.clone(), &mut rng).unwrap();
    println!("Testing prove");
    let proof = InnerSNARK::prove(&pk, circuit.clone(), &mut rng).unwrap();
    println!("proof: {}", InnerSNARK::verify(&vk, &circuit.get_inputs(), &proof).unwrap());

    let setup1 = InnerSetup {
        pk,
        vk,
    };

    let (agg_circuit_out, setup_out) = inner_to_outer(&circuit, &setup1);

    let mut setups1 = vec![];
    let mut setups2 = vec![];
    let mut agg_circuits1 = vec![];
    let mut agg_circuits2 = vec![];

    setups1.push(setup_out.clone());
    agg_circuits1.push(agg_circuit_out);

    for i in 0..2 {
        let (agg_circuit_in, setup_in) = outer_to_inner(&agg_circuits1[i], &setups1[i]);
        let (agg_circuit_out, setup_out) = inner_to_outer(&agg_circuit_in, &setup_in);
        setups2.push(setup_in);
        setups1.push(setup_out);
        agg_circuits2.push(agg_circuit_in);
        agg_circuits1.push(agg_circuit_out);
    }

    println!("Starting aggregation");

    let level1 = aggregate_list1(&circuits, &setup1);

    crate::test_circuit2(level1[0].clone());

    let mut prev_level = level1;
    for i in 0..2 {
        println!("Level {} first len {}", i, prev_level.len());
        let level2 = aggregate_list2(&prev_level, &setups1[i]);
        println!("Level {} second len {}", i, level2.len());
        if level2.len() == 1 {
            let last = level2[0].clone();
            let setup = setups2[i].clone();
            let proof1 = InnerSNARK::prove(&setup.pk, last.clone(), &mut rng).unwrap();
            println!("last proof: {}", InnerSNARK::verify(&setup.vk, &last.get_inputs(), &proof1).unwrap());
            return (proof1.clone(), setup.vk.clone(), leafs[0].clone(), leafs.last().unwrap().clone())
        }
        prev_level = aggregate_list1(&level2, &setups2[i]);
    }

    {
        let last = prev_level[0].clone();
        let setup = setups1[1].clone();
        let proof1 = OuterSNARK::prove(&setup.pk, last.clone(), &mut rng).unwrap();
        println!("last proof (outer): {}", OuterSNARK::verify(&setup.vk, &last.get_inputs(), &proof1).unwrap());
    }
    panic!("Wrong kind of last proof");

}

