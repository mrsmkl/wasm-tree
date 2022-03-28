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
use ark_relations::r1cs::ConstraintSystem;

use crate::{VM,Transition,hash_list,hash_code};
use crate::InstructionCircuit;

#[derive(Debug, Clone)]
pub struct TestCircuit {
    pub steps: usize,
    pub params: PoseidonParameters<Fr>,
}

impl InstructionCircuit for TestCircuit {
    fn calc_hash(&self) -> Fr {
        panic!("calc hash");
    }
    fn transition(&self) -> Transition {
        panic!("transition")
    }
}

fn generate_step(cs: ConstraintSystemRef<Fr>, params: PoseidonParameters<Fr>, params_g: &CRHParametersVar::<Fr>)
-> Result<FpVar<Fr>, SynthesisError> {
    let var_a = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(1))).unwrap());
    let var_b = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(2))).unwrap());
    let var_c = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(2))).unwrap());
    let var_d = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(2))).unwrap());
    let var_e = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(2))).unwrap());
    let var_f = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(2))).unwrap());

    let mut inputs = Vec::new();
    inputs.push(var_a);
    inputs.push(var_b);
    inputs.push(var_c);
    inputs.push(var_d);
    inputs.push(var_e);
    inputs.push(var_f);
    let hash_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs).unwrap();

    Ok(hash_gadget)
}

impl ConstraintSynthesizer<Fr> for TestCircuit {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<Fr>,
    ) -> Result<(), SynthesisError> {
        let params_g = CRHParametersVar::<Fr>::new_witness(cs.clone(), || Ok(self.params.clone())).unwrap();
        // make each step
        let mut vars = vec![];
        for el in 0..self.steps {
            let var = generate_step(cs.clone(), self.params.clone(), &params_g);
            vars.push(var);
        }
        // println!("num constraints {}, valid {}", cs.num_constraints(), cs.is_satisfied().unwrap());
        println!("num constraints {}", cs.num_constraints());
        Ok(())
    }
}

pub fn test(params: &PoseidonParameters<Fr>) {
    use ark_std::test_rng;
    use crate::InnerSNARK;
    use ark_crypto_primitives::CircuitSpecificSetupSNARK;
    use ark_crypto_primitives::SNARK;
    let cs_sys = ConstraintSystem::<Fr>::new();
    let cs = ConstraintSystemRef::new(cs_sys);
    let circuit = TestCircuit {
        params: params.clone(),
        steps: 100,
    };
    // circuit.generate_constraints(cs);
    let mut rng = test_rng();
    println!("Setting up circuit");
    let (pk, vk) = InnerSNARK::setup(circuit.clone(), &mut rng).unwrap();
    println!("Testing prove");
    let proof = InnerSNARK::prove(&pk, circuit.clone(), &mut rng).unwrap();
}
