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

use crate::{VM,hash_code};
use crate::InstructionCircuit;

#[derive(Debug, Clone)]
pub struct LoopCircuit {
    pub before: VM,
    pub after: VM,
    pub params: PoseidonParameters<Fr>,
}

impl InstructionCircuit for LoopCircuit {
    fn calc_hash(&self) -> Fr {
        let mut inputs = vec![];
        inputs.push(self.before.hash(&self.params));
        inputs.push(self.after.hash(&self.params));
        CRH::<Fr>::evaluate(&self.params, inputs).unwrap()
    }
}

// use ark_r1cs_std::R1CSVar;

impl ConstraintSynthesizer<Fr> for LoopCircuit {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<Fr>,
    ) -> Result<(), SynthesisError> {
        use crate::CodeTree::CLoop;
        let before = self.before.clone();
        let after = self.after.clone();

        println!("before {:?}", before);
        println!("after {:?}", after);

        let cont = match before.pc[0].clone() {
            CLoop(cont) => cont,
            _ => panic!("Wrong instruction"),
        };

        let cont_hash = hash_code(&self.params, &cont);
        let before_pc_hash = hash_code(&self.params, &before.pc);

        let pc_hash = hash_code(&self.params, &after.pc);
        let stack_hash = before.hash_stack(&self.params);
        let locals_hash = before.hash_locals(&self.params);
        let control_hash = before.hash_control(&self.params);

        let public_var = FpVar::Var(
            AllocatedFp::<Fr>::new_input(cs.clone(), || Ok(self.calc_hash())).unwrap(),
        );

        // TODO: these will actually have to be constants...
        let params_g = CRHParametersVar::<Fr>::new_witness(cs.clone(), || Ok(self.params.clone())).unwrap();

        let locals_var = FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(locals_hash)).unwrap(),
        );

        let stack_var = FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(stack_hash)).unwrap(),
        );
        let control_before_var = FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(control_hash)).unwrap(),
        );

        let start_var = FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(before_pc_hash)).unwrap(),
        );
        let cont_var = FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(cont_hash)).unwrap(),
        );
        let hash_pc_after_var = FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(pc_hash)).unwrap(),
        );

        let frame_var = CRHGadget::<Fr>::evaluate(&params_g, &vec![
            FpVar::Constant(Fr::from(1)),
            cont_var.clone(),
            start_var.clone(),
        ]).unwrap();

        let control_after_var = CRHGadget::<Fr>::evaluate(&params_g, &vec![
            frame_var.clone(),
            control_before_var.clone(),
        ]).unwrap();

        let mut inputs_pc = Vec::new();
        inputs_pc.push(FpVar::Constant(Fr::from(8)));
        inputs_pc.push(cont_var.clone());
        inputs_pc.push(hash_pc_after_var.clone());
        let hash_pc_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs_pc).unwrap();
    
        println!("pc hash {}", hash_code(&self.params, &before.pc));
        // println!("pc hash {}", hash_pc_gadget.value().unwrap());
        
        // Compute VM hash before
        let mut inputs_vm_before = Vec::new();
        inputs_vm_before.push(hash_pc_gadget);
        inputs_vm_before.push(stack_var.clone());
        inputs_vm_before.push(locals_var.clone());
        inputs_vm_before.push(control_before_var.clone());
        let hash_vm_before_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs_vm_before).unwrap();

        // Compute VM hash after
        let mut inputs_vm_after = Vec::new();
        inputs_vm_after.push(hash_pc_after_var);
        inputs_vm_after.push(stack_var);
        inputs_vm_after.push(locals_var);
        inputs_vm_after.push(control_after_var.clone());
        let hash_vm_after_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs_vm_after).unwrap();

        let mut inputs_transition = Vec::new();
        inputs_transition.push(hash_vm_before_gadget.clone());
        inputs_transition.push(hash_vm_after_gadget.clone());
        let hash_transition_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs_transition).unwrap();
        hash_transition_gadget.enforce_equal(&public_var)?;
    
        println!("Made circuit");
        println!("before {}, after {}", before.hash(&self.params), after.hash(&self.params));
        // println!("before {}, after {}", hash_vm_before_gadget.value().unwrap(), hash_vm_after_gadget.value().unwrap());

        Ok(())
    }
}

