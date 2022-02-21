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

use crate::{VM,Transition,hash_code};
use crate::InstructionCircuit;

// use ark_r1cs_std::R1CSVar;

#[derive(Debug, Clone)]
pub struct SetCircuit {
    pub before: VM,
    pub after: VM,
    pub params: PoseidonParameters<Fr>,
    pub idx: usize,
}

impl InstructionCircuit for SetCircuit {
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

impl ConstraintSynthesizer<Fr> for SetCircuit {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<Fr>,
    ) -> Result<(), SynthesisError> {
        let before = self.before.clone();
        let after = self.after.clone();

        println!("before {:?}", before);
        println!("after {:?}", after);
    
        let pc_hash = hash_code(&self.params, &after.pc);
        let stack_hash = after.hash_stack(&self.params);
        // let locals_hash = before.hash_locals(&self.params);
        let control_hash = before.hash_control(&self.params);

        let public_var = FpVar::Var(
            AllocatedFp::<Fr>::new_input(cs.clone(), || Ok(self.calc_hash())).unwrap(),
        );

        let params_g = CRHParametersVar::<Fr>::new_witness(cs.clone(), || Ok(self.params.clone())).unwrap();

        let bool_var = Boolean::from(
            AllocatedBool::<Fr>::new_witness(cs.clone(), || Ok(self.idx == 1)).unwrap(),
        );

        let locals_a = FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(before.locals[0]))).unwrap(),
        );
        let locals_b = FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(before.locals[1]))).unwrap(),
        );
        let read_var = FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(after.locals[self.idx]))).unwrap(),
        );
        let locals_after_a = bool_var.select(&locals_a, &read_var).unwrap();
        let locals_after_b = bool_var.select(&read_var, &locals_b).unwrap();

        let stack_after_var = FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(stack_hash)).unwrap(),
        );
        let control_var = FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(control_hash)).unwrap(),
        );

        let hash_pc_after_var = FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(pc_hash)).unwrap(),
        );
    
        let locals_var = CRHGadget::<Fr>::evaluate(&params_g, &vec![locals_a, locals_b]).unwrap();
        let locals_after_var = CRHGadget::<Fr>::evaluate(&params_g, &vec![locals_after_a, locals_after_b]).unwrap();

        let stack_before_var = CRHGadget::<Fr>::evaluate(&params_g, &vec![
            read_var.clone(), stack_after_var.clone()
        ]).unwrap();

        let mut inputs_pc = Vec::new();
        inputs_pc.push(FpVar::Constant(Fr::from(5)));
        inputs_pc.push(From::from(bool_var.clone()));
        inputs_pc.push(hash_pc_after_var.clone());
        let hash_pc_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs_pc).unwrap();
    
        println!("stack before {}", before.hash_stack(&self.params));
        // println!("stack before {}", stack_before_var.value().unwrap());
        
        println!("pc hash {}", hash_code(&self.params, &before.pc));
        // println!("pc hash {}", hash_pc_gadget.value().unwrap());
        
        // Compute VM hash before
        let mut inputs_vm_before = Vec::new();
        inputs_vm_before.push(hash_pc_gadget);
        inputs_vm_before.push(stack_before_var);
        inputs_vm_before.push(locals_var.clone());
        inputs_vm_before.push(control_var.clone());
        let hash_vm_before_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs_vm_before).unwrap();

        // Compute VM hash after
        let mut inputs_vm_after = Vec::new();
        inputs_vm_after.push(hash_pc_after_var);
        inputs_vm_after.push(stack_after_var);
        inputs_vm_after.push(locals_after_var);
        inputs_vm_after.push(control_var.clone());
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

