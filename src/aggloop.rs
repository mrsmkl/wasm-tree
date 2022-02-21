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
use crate::OuterSNARKPK;
use crate::InnerSNARKPK;

pub trait LoopCircuit : ConstraintSynthesizer<Fr> + Clone {
    fn get_inputs(&self) -> Vec<Fr>;
    fn get(&self) -> (Fr, Fr, Fr);
}

pub trait LoopCircuit2 : ConstraintSynthesizer<MNT6Fr> + Clone {
    fn get_inputs(&self) -> Vec<MNT6Fr>;
    fn get(&self) -> (Fr, Fr, Fr);
}

#[derive(Debug, Clone)]
pub struct InnerAggregateLoop {
    start_st : Fr,
    mid_st : Fr,
    end_st : Fr,
    root : Fr,
    proof1: InnerSNARKProof,
    proof2: InnerSNARKProof,
    vk: InnerSNARKVK,
}

impl LoopCircuit2 for InnerAggregateLoop {
    fn get_inputs(&self) -> Vec<MNT6Fr> {
        vec![mnt6(&self.start_st), mnt6(&self.end_st), mnt6(&self.root)]
    }
    fn get(&self) -> (Fr,Fr,Fr) {
        (self.start_st.clone(), self.end_st.clone(), self.root.clone())
    }
}

impl ConstraintSynthesizer<MNT6Fr> for InnerAggregateLoop {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<MNT6Fr>,
    ) -> Result<(), SynthesisError> {

        let start_var = FpVar::Var(
            AllocatedFp::<MNT6Fr>::new_input(cs.clone(), || Ok(mnt6(&self.start_st))).unwrap(),
        );
        let end_var = FpVar::Var(
            AllocatedFp::<MNT6Fr>::new_input(cs.clone(), || Ok(mnt6(&self.end_st))).unwrap(),
        );
        let root_var = FpVar::Var(
            AllocatedFp::<MNT6Fr>::new_input(cs.clone(), || Ok(mnt6(&self.root))).unwrap(),
        );

        let input1_gadget = <InnerSNARKGadget as SNARKGadget<
            <MNT4PairingEngine as PairingEngine>::Fr,
            <MNT4PairingEngine as PairingEngine>::Fq,
            InnerSNARK,
        >>::InputVar::new_witness(ns!(cs, "new_input"), || Ok(vec![self.start_st.clone(), self.mid_st.clone(), self.root.clone()]))
        .unwrap();
        let input2_gadget = <InnerSNARKGadget as SNARKGadget<
            <MNT4PairingEngine as PairingEngine>::Fr,
            <MNT4PairingEngine as PairingEngine>::Fq,
            InnerSNARK,
        >>::InputVar::new_witness(ns!(cs, "new_input"), || Ok(vec![self.mid_st.clone(), self.end_st.clone(), self.root.clone()]))
        .unwrap();

        let input1_bool_vec = input1_gadget.clone().into_iter().collect::<Vec<_>>();
        let input2_bool_vec = input2_gadget.clone().into_iter().collect::<Vec<_>>();
    
        let start_bool_vec = start_var.to_bits_le().unwrap();
        let end_bool_vec = end_var.to_bits_le().unwrap();
        let root_bool_vec = root_var.to_bits_le().unwrap();

        input1_bool_vec[0].enforce_equal(&start_bool_vec)?;
        input1_bool_vec[1].enforce_equal(&input2_bool_vec[0])?;
        input1_bool_vec[2].enforce_equal(&root_bool_vec)?;

        input1_bool_vec[0].enforce_equal(&input2_bool_vec[0])?;
        input1_bool_vec[1].enforce_equal(&end_bool_vec)?;
        input1_bool_vec[2].enforce_equal(&root_bool_vec)?;

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
        let vk_gadget = <InnerSNARKGadget as SNARKGadget<
            <MNT4PairingEngine as PairingEngine>::Fr,
            <MNT4PairingEngine as PairingEngine>::Fq,
            InnerSNARK,
        >>::VerifyingKeyVar::new_constant(ns!(cs, "alloc_vk"), self.vk.clone())
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
pub struct OuterAggregateLoop {
    start_st : Fr,
    mid_st : Fr,
    end_st : Fr,
    root : Fr,
    proof1: OuterSNARKProof,
    proof2: OuterSNARKProof,
    vk: OuterSNARKVK,
}

impl LoopCircuit for OuterAggregateLoop {
    fn get_inputs(&self) -> Vec<Fr> {
        vec![self.start_st.clone(), self.end_st.clone(), self.root.clone()]
    }
    fn get(&self) -> (Fr,Fr,Fr) {
        (self.start_st.clone(), self.end_st.clone(), self.root.clone())
    }
}

impl ConstraintSynthesizer<Fr> for OuterAggregateLoop {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<Fr>,
    ) -> Result<(), SynthesisError> {
        let start_var = FpVar::Var(
            AllocatedFp::<Fr>::new_input(cs.clone(), || Ok(self.start_st.clone())).unwrap(),
        );
        let end_var = FpVar::Var(
            AllocatedFp::<Fr>::new_input(cs.clone(), || Ok(self.end_st.clone())).unwrap(),
        );
        let root_var = FpVar::Var(
            AllocatedFp::<Fr>::new_input(cs.clone(), || Ok(self.root.clone())).unwrap(),
        );

        let input1_gadget = <OuterSNARKGadget as SNARKGadget<
            <MNT6PairingEngine as PairingEngine>::Fr,
            <MNT6PairingEngine as PairingEngine>::Fq,
            OuterSNARK,
        >>::InputVar::new_witness(ns!(cs, "new_input"), || Ok(vec![mnt6(&self.start_st), mnt6(&self.mid_st), mnt6(&self.root)]))
        .unwrap();
        let input2_gadget = <OuterSNARKGadget as SNARKGadget<
            <MNT6PairingEngine as PairingEngine>::Fr,
            <MNT6PairingEngine as PairingEngine>::Fq,
            OuterSNARK,
        >>::InputVar::new_witness(ns!(cs, "new_input"), || Ok(vec![mnt6(&self.mid_st), mnt6(&self.end_st), mnt6(&self.root)]))
        .unwrap();

        let input1_bool_vec = input1_gadget.clone().into_iter().collect::<Vec<_>>();
        let input2_bool_vec = input2_gadget.clone().into_iter().collect::<Vec<_>>();
    
        let start_bool_vec = start_var.to_bits_le().unwrap();
        let end_bool_vec = end_var.to_bits_le().unwrap();
        let root_bool_vec = root_var.to_bits_le().unwrap();

        input1_bool_vec[0].enforce_equal(&start_bool_vec)?;
        input1_bool_vec[1].enforce_equal(&input2_bool_vec[0])?;
        input1_bool_vec[2].enforce_equal(&root_bool_vec)?;

        input1_bool_vec[0].enforce_equal(&input2_bool_vec[0])?;
        input1_bool_vec[1].enforce_equal(&end_bool_vec)?;
        input1_bool_vec[2].enforce_equal(&root_bool_vec)?;
    
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
    pub vk: InnerSNARKVK,
}

fn aggregate_level1<C:LoopCircuit>(a: C, b: C, setup: &InnerSetup) -> InnerAggregateLoop {
    let mut rng = test_rng();

    let proof1 = InnerSNARK::prove(&setup.pk, a.clone(), &mut rng).unwrap();
    let proof2 = InnerSNARK::prove(&setup.pk, b.clone(), &mut rng).unwrap();

    println!("proof1: {}", InnerSNARK::verify(&setup.vk, &a.get_inputs(), &proof1).unwrap());
    println!("proof2: {}", InnerSNARK::verify(&setup.vk, &b.get_inputs(), &proof2).unwrap());

    let (start_st,mid_st,root) = a.get();
    let (_,end_st,root) = b.get();

    InnerAggregateLoop {
        start_st,
        mid_st,
        end_st,
        root,
        proof1: proof1,
        proof2: proof2,
        vk: setup.vk.clone(),
    }
}

#[derive(Debug, Clone)]
pub struct OuterSetup {
    pub pk: OuterSNARKPK,
    pub vk: OuterSNARKVK,
}

fn aggregate_level2<C:LoopCircuit2>(a: C, b: C, setup: &OuterSetup) -> OuterAggregateLoop {
    let mut rng = test_rng();

    let proof1 = OuterSNARK::prove(&setup.pk, a.clone(), &mut rng).unwrap();
    let proof2 = OuterSNARK::prove(&setup.pk, b.clone(), &mut rng).unwrap();

    println!("proof1: {}", OuterSNARK::verify(&setup.vk, &a.get_inputs(), &proof1).unwrap());
    println!("proof2: {}", OuterSNARK::verify(&setup.vk, &b.get_inputs(), &proof2).unwrap());

    let (start_st,mid_st,root) = a.get();
    let (_,end_st,root) = b.get();

    OuterAggregateLoop {
        start_st,
        mid_st,
        end_st,
        root,
        proof1: proof1,
        proof2: proof2,
        vk: setup.vk.clone(),
    }
}

pub fn outer_to_inner<C: LoopCircuit2>(circuit: &C, setup: &OuterSetup) -> (OuterAggregateLoop, InnerSetup) {
    let mut rng = test_rng();
    let agg_circuit1 = aggregate_level2(circuit.clone(), circuit.clone(), setup);
    let (pk, vk) = InnerSNARK::setup(agg_circuit1.clone(), &mut rng).unwrap();

    let setup2 = InnerSetup {
        pk,
        vk,
    };

    (agg_circuit1, setup2)
}

pub fn inner_to_outer<C: LoopCircuit>(circuit: &C, setup: &InnerSetup) -> (InnerAggregateLoop, OuterSetup) {
    let mut rng = test_rng();
    let agg_circuit1 = aggregate_level1(circuit.clone(), circuit.clone(), setup);
    let (pk, vk) = OuterSNARK::setup(agg_circuit1.clone(), &mut rng).unwrap();

    let setup2 = OuterSetup {
        pk,
        vk,
    };

    (agg_circuit1, setup2)
}

pub fn aggregate_list2<C: LoopCircuit2>(circuit: &[C], setup: &OuterSetup) -> Vec<OuterAggregateLoop> {
    let mut level1 = vec![];
    for i in 0..circuit.len()/2 {
        level1.push(aggregate_level2(circuit[2*i].clone(), circuit[2*i].clone(), setup));
    }
    level1
}

pub fn aggregate_list1<C: LoopCircuit>(circuit: &[C], setup: &InnerSetup) -> Vec<InnerAggregateLoop> {
    let mut level1 = vec![];
    for i in 0..circuit.len()/2 {
        level1.push(aggregate_level1(circuit[2*i].clone(), circuit[2*i].clone(), setup));
    }
    level1
}