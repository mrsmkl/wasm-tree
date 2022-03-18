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

use ark_mnt4_298::constraints::{G2Var as MNT4G2Var, G1Var as MNT4G1Var};
use ark_r1cs_std::groups::CurveVar;
use ark_ec::AffineCurve;
use ark_groth16::constraints::VerifyingKeyVar;
use ark_r1cs_std::prelude::CondSelectGadget;
use ark_r1cs_std::R1CSVar;

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
use crate::mnt6;
use crate::InstructionCircuit2;
use crate::InstructionCircuit;

#[derive(Debug, Clone)]
pub struct SelectionCircuit {
    pub hash : Fr,
    pub proof: InnerSNARKProof,
    pub keys: Vec<InnerSNARKVK>,
    pub idx: u32,
    // transition: Transition,
}

impl InstructionCircuit2 for SelectionCircuit {
    fn calc_hash(&self) -> Fr {
        self.hash.clone()
    }
}

impl ConstraintSynthesizer<MNT6Fr> for SelectionCircuit {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<MNT6Fr>,
    ) -> Result<(), SynthesisError> {
        let input_gadget = <InnerSNARKGadget as SNARKGadget<
            <MNT4PairingEngine as PairingEngine>::Fr,
            <MNT4PairingEngine as PairingEngine>::Fq,
            InnerSNARK,
        >>::InputVar::new_input(ns!(cs, "new_input"), || Ok(vec![self.hash.clone()]))
        .unwrap();

        let proof_gadget = <InnerSNARKGadget as SNARKGadget<
            <MNT4PairingEngine as PairingEngine>::Fr,
            <MNT4PairingEngine as PairingEngine>::Fq,
            InnerSNARK,
        >>::ProofVar::new_witness(ns!(cs, "alloc_proof"), || Ok(self.proof))
        .unwrap();

        let idx_gadget = FpVar::Var(
            AllocatedFp::<MNT6Fr>::new_witness(cs.clone(), || Ok(MNT6Fr::from(self.idx))).unwrap(),
        );

        let bools = idx_gadget.to_bits_le()?;

        // println!("bools {:?}", bools.value().unwrap());

        let keys : Vec<_> = self.keys.iter().map(|vk| {
            let VerifyingKey {
                alpha_g1,
                beta_g2,
                gamma_g2,
                delta_g2,
                gamma_abc_g1,
            } = vk.clone();
            let alpha_g1 = MNT4G1Var::constant(alpha_g1.into_projective());
            let beta_g2 = MNT4G2Var::constant(beta_g2.into_projective());
            let gamma_g2 = MNT4G2Var::constant(gamma_g2.into_projective());
            let delta_g2 = MNT4G2Var::constant(delta_g2.into_projective());
 
            let gamma_abc_g1 : Vec<MNT4G1Var> = gamma_abc_g1.iter().map(|a| MNT4G1Var::constant(a.into_projective())).collect();
            let vk_gadget : VerifyingKeyVar<MNT4PairingEngine, MNT4PairingVar> = VerifyingKeyVar {
                alpha_g1: alpha_g1,
                beta_g2: beta_g2,
                gamma_g2: gamma_g2,
                delta_g2: delta_g2,
                gamma_abc_g1: gamma_abc_g1,
            };
            vk_gadget
        }).collect();

        let mut bools2 = vec![];
        for i in bools[0..4].iter().rev() {
            bools2.push(i.clone())
        }

        let vk_gadget = VerifyingKeyVar::conditionally_select_power_of_two_vector(&bools2, &keys).unwrap();

        <InnerSNARKGadget as SNARKGadget<
            <MNT4PairingEngine as PairingEngine>::Fr,
            <MNT4PairingEngine as PairingEngine>::Fq,
            InnerSNARK,
        >>::verify(&vk_gadget, &input_gadget, &proof_gadget)
        .unwrap()
        .enforce_equal(&Boolean::constant(true))
        .unwrap();

        // println!("Working: {}", cs.is_satisfied().unwrap());

        println!("recursive circuit has {} constraints", cs.num_constraints());

        Ok(())
    }
}

pub fn make_circuits<C: InstructionCircuit>(circuits: &mut Vec<SelectionCircuit>, lst: &[C], keys: &[(InnerSNARKPK, InnerSNARKVK)], idx: usize) {
    let mut rng = test_rng();
    for i in lst {
        let proof = InnerSNARK::prove(&keys[idx].0, i.clone(), &mut rng).unwrap();
        circuits.push(SelectionCircuit {
            hash : i.calc_hash().clone(),
            proof: proof,
            keys: keys.iter().map(|a| a.1.clone()).collect(),
            idx: idx as u32,
            // transition: i.transition(),
        });
    }
}
