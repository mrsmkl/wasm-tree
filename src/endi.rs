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

use crate::{VM,Transition,hash_code,InstructionCircuit};

#[derive(Debug, Clone)]
pub struct EndCircuit {
    pub before: VM,
    pub after: VM,
    pub params: PoseidonParameters<Fr>,
}

impl InstructionCircuit for EndCircuit {
    fn calc_hash(&self) -> Fr {
        let mut inputs = vec![];
        inputs.push(self.before.hash(&self.params));
        inputs.push(self.after.hash(&self.params));
        CRH::<Fr>::evaluate(&self.params, inputs).unwrap()
    }
    fn transition(&self) -> Transition {
        Transition { before: self.before.clone(), after: self.after.clone() }
    }
}

// use ark_r1cs_std::R1CSVar;

impl ConstraintSynthesizer<Fr> for EndCircuit {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<Fr>,
    ) -> Result<(), SynthesisError> {
        use crate::ControlFrame::LoopFrame;
        let before = self.before.clone();
        let after = self.after.clone();

        println!("before {:?}", before);
        println!("after {:?}", after);

        let LoopFrame(cont, start) = before.control_stack.last().unwrap().clone();

        let cont_hash = hash_code(&self.params, &cont);
        let start_hash = hash_code(&self.params, &start);

        // let pc_hash = hash_code(&self.params, &after.pc);
        let pc_other_hash = hash_code(&self.params, &before.pc[1..]);
        let stack_hash = before.hash_stack(&self.params);
        let locals_hash = before.hash_locals(&self.params);
        let control_hash_after = after.hash_control(&self.params);

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
        let control_after_var = FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(control_hash_after)).unwrap(),
        );

        let start_var = FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(start_hash)).unwrap(),
        );
        let cont_var = FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(cont_hash)).unwrap(),
        );
        let hash_pc_other_var = FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(pc_other_hash)).unwrap(),
        );

        let frame_var = CRHGadget::<Fr>::evaluate(&params_g, &vec![
            FpVar::Constant(Fr::from(1)),
            cont_var.clone(),
            start_var.clone(),
        ]).unwrap();

        let hash_pc_before_var = CRHGadget::<Fr>::evaluate(&params_g, &vec![
            FpVar::Constant(Fr::from(9)),
            hash_pc_other_var.clone(),
        ]).unwrap();

        let control_before_var = CRHGadget::<Fr>::evaluate(&params_g, &vec![
            frame_var.clone(),
            control_after_var.clone(),
        ]).unwrap();

        println!("pc before hash {}", hash_code(&self.params, &before.pc));
        // println!("pc before hash {}", hash_pc_before_var.value().unwrap());

        // println!("pc other hash {}", hash_pc_other_var.value().unwrap());

        println!("pc after hash {}", hash_code(&self.params, &after.pc));
        // println!("pc after hash {}", cont_var.value().unwrap());
        
        // Compute VM hash before
        let mut inputs_vm_before = Vec::new();
        inputs_vm_before.push(hash_pc_before_var);
        inputs_vm_before.push(stack_var.clone());
        inputs_vm_before.push(locals_var.clone());
        inputs_vm_before.push(control_before_var.clone());
        let hash_vm_before_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs_vm_before).unwrap();

        // Compute VM hash after
        let mut inputs_vm_after = Vec::new();
        inputs_vm_after.push(cont_var);
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

