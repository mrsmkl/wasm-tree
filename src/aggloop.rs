
// Aggregating merkle loop circuits

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

#[derive(Debug, Clone)]
struct InnerAggregateLoop {
    start_st : Fr,
    mid_st : Fr,
    end_st : Fr,
    root : Fr,
    proof1: InnerSNARKProof,
    proof2: InnerSNARKProof,
    proof_hash: InnerSNARKProof,
    vk: InnerSNARKVK,
    hash_vk: InnerSNARKVK,
}

/*
impl InnerAggregateLoop {
    fn calc_hash(&self) -> Fr {
        self.c.clone()
    }
}
*/

impl ConstraintSynthesizer<MNT6Fr> for InnerAggregateLoop {
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

        println!("Input vecs {} {} {}", input1_bool_vec[0].len(), input2_bool_vec[0].len(), input3_bool_vec[0].len());

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

fn convert_inputs(inputs: &[Fr]) -> Vec<MNT6Fr> {
    inputs
        .iter()
        .map(|input| {
            MNT6Fr::from_repr(input
                .into_repr()).unwrap()
        })
        .collect::<Vec<_>>()
}

fn mnt6(input: &Fr) -> MNT6Fr {
    MNT6Fr::from_repr(input.into_repr()).unwrap()
}

#[derive(Debug, Clone)]
struct OuterAggregateLoop {
    a : Fr,
    b : Fr,
    c : Fr,
    proof1: OuterSNARKProof,
    proof2: OuterSNARKProof,
    vk: OuterSNARKVK,
    params: PoseidonParameters<Fr>,
}

/*
impl InstructionCircuit for OuterAggregateLoop {
    fn calc_hash(&self) -> Fr {
        self.c.clone()
    }
    fn transition(&self) -> Transition {
        panic!("no transitions here...");
    }
}*/

impl ConstraintSynthesizer<Fr> for OuterAggregateLoop {
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

        let input1_bool_vec = public_var.clone().into_iter().collect::<Vec<_>>();

        println!("Input vecs {}", input1_bool_vec[0].len());

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
