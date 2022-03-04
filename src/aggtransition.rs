// Aggregating transition circuits

use ark_crypto_primitives::crh::poseidon::{ /* TwoToOneCRH, */ CRH};
use ark_crypto_primitives::crh::poseidon::constraints::{CRHGadget, CRHParametersVar};
use ark_sponge::poseidon::PoseidonParameters;
// use ark_bls12_377::Fr;
use ark_std::UniformRand;
use ark_std::Zero;
use ark_crypto_primitives::CRHScheme;
use ark_relations::r1cs::ConstraintSystem;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::{
    fields::fp::{AllocatedFp, FpVar},
};
use ark_crypto_primitives::CRHSchemeGadget;
use ark_relations::r1cs::ConstraintSystemRef;
use ark_relations::r1cs::SynthesisError;
use ark_relations::r1cs::ConstraintSynthesizer;
use ark_ff::PrimeField;
use ark_sponge::Absorb;

use ark_mnt4_298::{
    constraints::PairingVar as MNT4PairingVar, Fr, MNT4_298 as MNT4PairingEngine,
};
use ark_mnt6_298::{
    Fr as MNT6Fr,
    constraints::PairingVar as MNT6PairingVar, MNT6_298 as MNT6PairingEngine,
};
use ark_groth16::Groth16;
use ark_groth16::constraints::Groth16VerifierGadget;
use ark_std::test_rng;
use ark_crypto_primitives::SNARK;
use ark_crypto_primitives::CircuitSpecificSetupSNARK;
use ark_r1cs_std::boolean::Boolean;
use ark_relations::ns;
use ark_ec::PairingEngine;
use ark_crypto_primitives::snark::constraints::SNARKGadget;
use ark_r1cs_std::eq::EqGadget;
use ark_groth16::Proof;
use ark_groth16::VerifyingKey;
use ark_std::One;
use ark_groth16::ProvingKey;
use ark_r1cs_std::ToBitsGadget;
use ark_crypto_primitives::snark::FromFieldElementsGadget;
use ark_r1cs_std::boolean::AllocatedBool;

use crate::OuterSNARKGadget;
use crate::OuterSNARK;
use crate::InnerSNARKGadget;
use crate::InnerSNARK;
use crate::OuterSNARKVK;
use crate::OuterSNARKProof;
use crate::InnerSNARKVK;
use crate::InnerSNARKProof;
use crate::OuterSNARKPK;
use crate::InnerSNARKPK;

use crate::InstructionCircuit2;
use crate::InstructionCircuit;
use crate::convert_inputs;
use crate::hash_pair;
use crate::Transition;
use crate::mnt6;

#[derive(Debug, Clone)]
pub struct HashCircuit {
    pub a : Fr,
    pub b : Fr,
    pub params: PoseidonParameters<Fr>,
}

impl HashCircuit {
    fn calc_hash(&self) -> Fr {
        let mut inputs = vec![];
        inputs.push(self.a.clone());
        inputs.push(self.b.clone());
        CRH::<Fr>::evaluate(&self.params, inputs).unwrap()
    }
}

impl ConstraintSynthesizer<Fr> for HashCircuit {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<Fr>,
    ) -> Result<(), SynthesisError> {
        let a_var = FpVar::Var(
            AllocatedFp::<Fr>::new_input(cs.clone(), || Ok(self.a)).unwrap(),
        );
        let b_var = FpVar::Var(
            AllocatedFp::<Fr>::new_input(cs.clone(), || Ok(self.b)).unwrap(),
        );
        let c_var = FpVar::Var(
            AllocatedFp::<Fr>::new_input(cs.clone(), || Ok(self.calc_hash())).unwrap(),
        );
        let params_g = CRHParametersVar::<Fr>::new_witness(cs.clone(), || Ok(self.params.clone())).unwrap();
        let mut inputs = Vec::new();
        inputs.push(a_var.clone());
        inputs.push(b_var.clone());
        let hash_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs).unwrap();
        hash_gadget.enforce_equal(&c_var)?;
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct InnerAggregationCircuit {
    a : Fr,
    b : Fr,
    c : Fr,
    proof1: InnerSNARKProof,
    proof2: InnerSNARKProof,
    proof_hash: InnerSNARKProof,
    vk: InnerSNARKVK,
    hash_vk: InnerSNARKVK,
}

impl InstructionCircuit2 for InnerAggregationCircuit {
    fn calc_hash(&self) -> Fr {
        self.c.clone()
    }
}

impl ConstraintSynthesizer<MNT6Fr> for InnerAggregationCircuit {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<MNT6Fr>,
    ) -> Result<(), SynthesisError> {
        let public_var = <InnerSNARKGadget as SNARKGadget<
            <MNT4PairingEngine as PairingEngine>::Fr,
            <MNT4PairingEngine as PairingEngine>::Fq,
            InnerSNARK,
        >>::InputVar::new_input(ns!(cs, "public_input"), || Ok(vec![self.c.clone()])).unwrap();

        // println!("inner public var {:?}", public_var);

        let input1_gadget = <InnerSNARKGadget as SNARKGadget<
            <MNT4PairingEngine as PairingEngine>::Fr,
            <MNT4PairingEngine as PairingEngine>::Fq,
            InnerSNARK,
        >>::InputVar::new_witness(ns!(cs, "new_input"), || Ok(vec![self.a.clone()]))
        .unwrap();
        let input2_gadget = <InnerSNARKGadget as SNARKGadget<
            <MNT4PairingEngine as PairingEngine>::Fr,
            <MNT4PairingEngine as PairingEngine>::Fq,
            InnerSNARK,
        >>::InputVar::new_witness(ns!(cs, "new_input"), || Ok(vec![self.b.clone()]))
        .unwrap();
        let input_hash_gadget = <InnerSNARKGadget as SNARKGadget<
            <MNT4PairingEngine as PairingEngine>::Fr,
            <MNT4PairingEngine as PairingEngine>::Fq,
            InnerSNARK,
        >>::InputVar::new_witness(ns!(cs, "new_input"), || Ok(vec![self.a.clone(), self.b.clone(), self.c.clone()]))
        .unwrap();

        let input1_bool_vec = input1_gadget.clone().into_iter().collect::<Vec<_>>();
        let input2_bool_vec = input2_gadget.clone().into_iter().collect::<Vec<_>>();
        let input3_bool_vec = public_var.clone().into_iter().collect::<Vec<_>>();
        let input_hash_bool_vec = input_hash_gadget.clone().into_iter().collect::<Vec<_>>();

        // println!("Input vecs {} {} {}", input1_bool_vec[0].len(), input2_bool_vec[0].len(), input3_bool_vec[0].len());

        input1_bool_vec[0].enforce_equal(&input_hash_bool_vec[0])?;
        input2_bool_vec[0].enforce_equal(&input_hash_bool_vec[1])?;
        input3_bool_vec[0].enforce_equal(&input_hash_bool_vec[2])?;

        let proof1_gadget = <InnerSNARKGadget as SNARKGadget<
            <MNT4PairingEngine as PairingEngine>::Fr,
            <MNT4PairingEngine as PairingEngine>::Fq,
            InnerSNARK,
        >>::ProofVar::new_witness(ns!(cs, "alloc_proof"), || Ok(self.proof1))
        .unwrap();
        let proof2_gadget = <InnerSNARKGadget as SNARKGadget<
            <MNT4PairingEngine as PairingEngine>::Fr,
            <MNT4PairingEngine as PairingEngine>::Fq,
            InnerSNARK,
        >>::ProofVar::new_witness(ns!(cs, "alloc_proof"), || Ok(self.proof2))
        .unwrap();
        let proof_hash_gadget = <InnerSNARKGadget as SNARKGadget<
            <MNT4PairingEngine as PairingEngine>::Fr,
            <MNT4PairingEngine as PairingEngine>::Fq,
            InnerSNARK,
        >>::ProofVar::new_witness(ns!(cs, "alloc_proof"), || Ok(self.proof_hash))
        .unwrap();
        let vk_gadget = <InnerSNARKGadget as SNARKGadget<
            <MNT4PairingEngine as PairingEngine>::Fr,
            <MNT4PairingEngine as PairingEngine>::Fq,
            InnerSNARK,
        >>::VerifyingKeyVar::new_constant(ns!(cs, "alloc_vk"), self.vk.clone())
        .unwrap();
        let hash_vk_gadget = <InnerSNARKGadget as SNARKGadget<
            <MNT4PairingEngine as PairingEngine>::Fr,
            <MNT4PairingEngine as PairingEngine>::Fq,
            InnerSNARK,
        >>::VerifyingKeyVar::new_constant(ns!(cs, "alloc_hash_vk"), self.hash_vk.clone())
        .unwrap();
        <InnerSNARKGadget as SNARKGadget<
            <MNT4PairingEngine as PairingEngine>::Fr,
            <MNT4PairingEngine as PairingEngine>::Fq,
            InnerSNARK,
        >>::verify(&vk_gadget, &input1_gadget, &proof1_gadget)
        .unwrap()
        .enforce_equal(&Boolean::constant(true))
        .unwrap();
        InnerSNARKGadget::verify(&vk_gadget, &input2_gadget, &proof2_gadget)
        .unwrap()
        .enforce_equal(&Boolean::constant(true))
        .unwrap();
        InnerSNARKGadget::verify(&hash_vk_gadget, &input_hash_gadget, &proof_hash_gadget)
        .unwrap()
        .enforce_equal(&Boolean::constant(true))
        .unwrap();

        // println!("Working: {}", cs.is_satisfied().unwrap());

        println!("recursive circuit has {} constraints", cs.num_constraints());

        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct OuterAggregationCircuit {
    a : Fr,
    b : Fr,
    c : Fr,
    proof1: OuterSNARKProof,
    proof2: OuterSNARKProof,
    vk: OuterSNARKVK,
    params: PoseidonParameters<Fr>,
}

impl InstructionCircuit for OuterAggregationCircuit {
    fn calc_hash(&self) -> Fr {
        self.c.clone()
    }
    fn transition(&self) -> Transition {
        panic!("no transitions here...");
    }
}

impl ConstraintSynthesizer<Fr> for OuterAggregationCircuit {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<Fr>,
    ) -> Result<(), SynthesisError> {
        let public_var = <OuterSNARKGadget as SNARKGadget<
            <MNT6PairingEngine as PairingEngine>::Fr,
            <MNT6PairingEngine as PairingEngine>::Fq,
            OuterSNARK,
        >>::InputVar::new_witness(ns!(cs, "public_input"), || Ok(vec![mnt6(&self.c)])).unwrap();

        let input1_gadget = <OuterSNARKGadget as SNARKGadget<
            <MNT6PairingEngine as PairingEngine>::Fr,
            <MNT6PairingEngine as PairingEngine>::Fq,
            OuterSNARK,
        >>::InputVar::new_witness(ns!(cs, "new_input"), || Ok(vec![mnt6(&self.a)]))
        .unwrap();
        let input2_gadget = <OuterSNARKGadget as SNARKGadget<
            <MNT6PairingEngine as PairingEngine>::Fr,
            <MNT6PairingEngine as PairingEngine>::Fq,
            OuterSNARK,
        >>::InputVar::new_witness(ns!(cs, "new_input"), || Ok(vec![mnt6(&self.b)]))
        .unwrap();

        // inputs for hashing
        let a_var = FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(self.a.clone())).unwrap(),
        );
        let b_var = FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(self.b.clone())).unwrap(),
        );
        let c_var = FpVar::Var(
            AllocatedFp::<Fr>::new_input(cs.clone(), || Ok(self.c.clone())).unwrap(),
        );
        let params_g = CRHParametersVar::<Fr>::new_witness(cs.clone(), || Ok(self.params.clone())).unwrap();
        let mut inputs = Vec::new();
        inputs.push(a_var.clone());
        inputs.push(b_var.clone());
        let hash_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs).unwrap();
        hash_gadget.enforce_equal(&c_var)?;
    
        let a_bits = a_var.to_bits_le().unwrap();
        let b_bits = b_var.to_bits_le().unwrap();
        let c_bits = c_var.to_bits_le().unwrap();
    
        let input1_bool_vec = input1_gadget.clone().into_iter().collect::<Vec<_>>();
        let input2_bool_vec = input2_gadget.clone().into_iter().collect::<Vec<_>>();
        let input3_bool_vec = public_var.clone().into_iter().collect::<Vec<_>>();
        input1_bool_vec[0].enforce_equal(&a_bits)?;
        input2_bool_vec[0].enforce_equal(&b_bits)?;
        input3_bool_vec[0].enforce_equal(&c_bits)?;
    
        let proof1_gadget = <OuterSNARKGadget as SNARKGadget<
            <MNT6PairingEngine as PairingEngine>::Fr,
            <MNT6PairingEngine as PairingEngine>::Fq,
            OuterSNARK,
        >>::ProofVar::new_witness(ns!(cs, "alloc_proof"), || Ok(self.proof1))
        .unwrap();
        let proof2_gadget = <OuterSNARKGadget as SNARKGadget<
            <MNT6PairingEngine as PairingEngine>::Fr,
            <MNT6PairingEngine as PairingEngine>::Fq,
            OuterSNARK,
        >>::ProofVar::new_witness(ns!(cs, "alloc_proof"), || Ok(self.proof2))
        .unwrap();
        let vk_gadget = <OuterSNARKGadget as SNARKGadget<
            <MNT6PairingEngine as PairingEngine>::Fr,
            <MNT6PairingEngine as PairingEngine>::Fq,
            OuterSNARK,
        >>::VerifyingKeyVar::new_constant(ns!(cs, "alloc_vk"), self.vk.clone())
        .unwrap();
        <OuterSNARKGadget as SNARKGadget<
            <MNT6PairingEngine as PairingEngine>::Fr,
            <MNT6PairingEngine as PairingEngine>::Fq,
            OuterSNARK,
        >>::verify(&vk_gadget, &input1_gadget, &proof1_gadget)
        .unwrap()
        .enforce_equal(&Boolean::constant(true))
        .unwrap();
        OuterSNARKGadget::verify(&vk_gadget, &input2_gadget, &proof2_gadget)
        .unwrap()
        .enforce_equal(&Boolean::constant(true))
        .unwrap();
    
        // println!("Working: {}", cs.is_satisfied().unwrap());
    
        println!("recursive circuit has {} constraints", cs.num_constraints());
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct InnerSetup {
    pub pk: InnerSNARKPK,
    pub hash_pk: InnerSNARKPK,
    pub vk: InnerSNARKVK,
    pub hash_vk: InnerSNARKVK, 
    pub params: PoseidonParameters<Fr>,
}

fn aggregate_level1<C:InstructionCircuit>(a: C, b: C, setup: &InnerSetup) -> InnerAggregationCircuit {
    let mut rng = test_rng();
    let hash1 = a.calc_hash();
    let hash2 = b.calc_hash();

    let hash_circuit = HashCircuit {
        a: hash1,
        b: hash2,
        params: setup.params.clone(),
    };

    let start = Instant::now();
    let proof1 = InnerSNARK::prove(&setup.pk, a.clone(), &mut rng).unwrap();
    let elapsed = start.elapsed();
    println!("proving took {} ms", elapsed.as_millis());
    let start = Instant::now();
    let proof2 = InnerSNARK::prove(&setup.pk, b.clone(), &mut rng).unwrap();
    let elapsed = start.elapsed();
    println!("proving took {} ms", elapsed.as_millis());
    let proof_hash = InnerSNARK::prove(&setup.hash_pk, hash_circuit.clone(), &mut rng).unwrap();

    let hash3 = hash_circuit.calc_hash();

    println!("proof1: {}", InnerSNARK::verify(&setup.vk, &vec![hash1.clone()], &proof1).unwrap());
    println!("proof2: {}", InnerSNARK::verify(&setup.vk, &vec![hash2.clone()], &proof2).unwrap());
    println!(
        "proof hash: {}",
        InnerSNARK::verify(&setup.hash_vk, &vec![hash1.clone(), hash2.clone(), hash3.clone()], &proof_hash).unwrap()
    );

    InnerAggregationCircuit {
        a: hash1,
        b: hash2,
        c: hash3,
        proof1: proof1,
        proof2: proof2,
        proof_hash: proof_hash,
        vk: setup.vk.clone(),
        hash_vk: setup.hash_vk.clone(),
    }
}

#[derive(Debug, Clone)]
pub struct OuterSetup {
    pub pk: OuterSNARKPK,
    pub vk: OuterSNARKVK,
    pub params: PoseidonParameters<Fr>,
}

use std::time::Instant;

fn aggregate_level2<C:InstructionCircuit2>(a: C, b: C, setup: &OuterSetup) -> OuterAggregationCircuit {
    let mut rng = test_rng();
    let hash1 = a.calc_hash();
    let hash2 = b.calc_hash();

    let start = Instant::now();
    let proof1 = OuterSNARK::prove(&setup.pk, a.clone(), &mut rng).unwrap();
    let elapsed = start.elapsed();
    println!("proving took {} ms", elapsed.as_millis());
    let start = Instant::now();
    let proof2 = OuterSNARK::prove(&setup.pk, b.clone(), &mut rng).unwrap();
    let elapsed = start.elapsed();
    println!("proving took {} ms", elapsed.as_millis());

    println!("proof1: {}", OuterSNARK::verify(&setup.vk, &convert_inputs(&vec![hash1.clone()]), &proof1).unwrap());
    println!("proof2: {}", OuterSNARK::verify(&setup.vk, &convert_inputs(&vec![hash2.clone()]), &proof2).unwrap());

    OuterAggregationCircuit {
        a: hash1,
        b: hash2,
        c: hash_pair(&setup.params, &hash1, &hash2),
        proof1: proof1,
        proof2: proof2,
        vk: setup.vk.clone(),
        params: setup.params.clone(),
    }
}

pub fn outer_to_inner<C: InstructionCircuit2>(circuit: &C, setup: &OuterSetup, hash_pk: &InnerSNARKPK, hash_vk: &InnerSNARKVK) ->
    (OuterAggregationCircuit, InnerSetup) {
    let mut rng = test_rng();
    let agg_circuit1 = aggregate_level2(circuit.clone(), circuit.clone(), setup);
    let (pk, vk) = InnerSNARK::setup(agg_circuit1.clone(), &mut rng).unwrap();

    let setup2 = InnerSetup {
        pk,
        vk,
        hash_pk: hash_pk.clone(),
        hash_vk: hash_vk.clone(),
        params: setup.params.clone(),
    };

    (agg_circuit1, setup2)
}

pub fn inner_to_outer<C: InstructionCircuit>(circuit: &C, setup: &InnerSetup) ->
    (InnerAggregationCircuit, OuterSetup) {
    let mut rng = test_rng();
    let agg_circuit1 = aggregate_level1(circuit.clone(), circuit.clone(), setup);
    let (pk, vk) = OuterSNARK::setup(agg_circuit1.clone(), &mut rng).unwrap();

    let setup2 = OuterSetup {
        pk,
        vk,
        params: setup.params.clone(),
    };

    (agg_circuit1, setup2)
}

pub fn aggregate_list2<C: InstructionCircuit2>(circuit: &[C], setup: &OuterSetup) -> Vec<OuterAggregationCircuit> {
    let mut level1 = vec![];
    for i in 0..circuit.len()/2 {
        level1.push(aggregate_level2(circuit[2*i].clone(), circuit[2*i+1].clone(), setup));
    }
    level1
}

pub fn aggregate_list1<C: InstructionCircuit>(circuit: &[C], setup: &InnerSetup) -> Vec<InnerAggregationCircuit> {
    let mut level1 = vec![];
    for i in 0..circuit.len()/2 {
        level1.push(aggregate_level1(circuit[2*i].clone(), circuit[2*i+1].clone(), setup));
    }
    level1
}
