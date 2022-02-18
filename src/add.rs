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

use crate::{VM,hash_list,hash_code};
use crate::InstructionCircuit;

#[derive(Debug, Clone)]
pub struct AddCircuit {
    pub before: VM,
    pub after: VM,
    pub params: PoseidonParameters<Fr>,
}

impl InstructionCircuit for AddCircuit {
    fn calc_hash(&self) -> Fr {
        let mut inputs = vec![];
        inputs.push(self.before.hash(&self.params));
        inputs.push(self.after.hash(&self.params));
        CRH::<Fr>::evaluate(&self.params, inputs).unwrap()
    }
}

impl ConstraintSynthesizer<Fr> for AddCircuit {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<Fr>,
    ) -> Result<(), SynthesisError> {
        let before = self.before.clone();
        let after = self.after.clone();

        println!("before {:?}", before);
        println!("after {:?}", after);
    
        let elen = before.expr_stack.len();
    
        let pc_hash = hash_code(&self.params, &after.pc);
        let stack_hash = hash_list(&self.params, &before.expr_stack[..elen-2].iter().map(|a| Fr::from(*a)).collect::<Vec<Fr>>());
        let locals_hash = before.hash_locals(&self.params);
        let control_hash = before.hash_control(&self.params);

        let p1 = before.expr_stack[elen - 1];
        let p2 = before.expr_stack[elen - 2];

        let public_var = FpVar::Var(
            AllocatedFp::<Fr>::new_input(cs.clone(), || Ok(self.calc_hash())).unwrap(),
        );
    
        println!("p1 {}, p2 {}", p1, p2);
    
        let params_g = CRHParametersVar::<Fr>::new_witness(cs.clone(), || Ok(self.params.clone())).unwrap();
    
        let var_a = FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(p1))).unwrap(),
        );
        let var_b = FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(p2))).unwrap(),
        );
    
        let locals_var = FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(locals_hash)).unwrap(),
        );
        let control_var = FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(control_hash)).unwrap(),
        );
    
        let hash_pc_after_var = FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(pc_hash)).unwrap(),
        );
    
        let mut inputs_pc = Vec::new();
        inputs_pc.push(FpVar::Constant(Fr::from(1)));
        inputs_pc.push(hash_pc_after_var.clone());
        let hash_pc_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs_pc).unwrap();
    
        println!("pc hash {}", hash_code(&self.params, &before.pc));
//        println!("pc hash {}", hash_pc_gadget.value().unwrap());
    
        let mut inputs_stack_before2 = Vec::new();
        inputs_stack_before2.push(var_b.clone());
        inputs_stack_before2.push(FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(stack_hash)).unwrap(),
        ));
        let hash_stack_before2_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs_stack_before2).unwrap();
    
        println!("stack before2 {}", hash_list(&self.params, &before.expr_stack[..elen-1].iter().map(|a| Fr::from(*a)).collect::<Vec<Fr>>()));
//        println!("stack before2 {}", hash_stack_before2_gadget.value().unwrap());
    
        let mut inputs_stack_before = Vec::new();
        inputs_stack_before.push(var_a.clone());
        inputs_stack_before.push(hash_stack_before2_gadget);
        let hash_stack_before_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs_stack_before).unwrap();
    
        println!("stack before {}", hash_list(&self.params, &before.expr_stack.iter().map(|a| Fr::from(*a)).collect::<Vec<Fr>>()));
//        println!("stack before {}", hash_stack_before_gadget.value().unwrap());

        let mut inputs_stack_after = Vec::new();
        // TODO: check that 32-bit
        inputs_stack_after.push(var_a.clone() + var_b.clone());
        inputs_stack_after.push(FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(stack_hash)).unwrap(),
        ));
        let hash_stack_after_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs_stack_after).unwrap();
    
        println!("stack after {}", hash_list(&self.params, &after.expr_stack.iter().map(|a| Fr::from(*a)).collect::<Vec<Fr>>()));
//        println!("stack after {}", hash_stack_after_gadget.value().unwrap());

        // Compute VM hash before
        let mut inputs_vm_before = Vec::new();
        inputs_vm_before.push(hash_pc_gadget);
        inputs_vm_before.push(hash_stack_before_gadget);
        inputs_vm_before.push(locals_var.clone());
        inputs_vm_before.push(control_var.clone());
        let hash_vm_before_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs_vm_before).unwrap();
    
        // Compute VM hash after
        let mut inputs_vm_after = Vec::new();
        inputs_vm_after.push(hash_pc_after_var);
        inputs_vm_after.push(hash_stack_after_gadget);
        inputs_vm_after.push(locals_var.clone());
        inputs_vm_after.push(control_var.clone());
        let hash_vm_after_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs_vm_after).unwrap();

        let mut inputs_transition = Vec::new();
        inputs_transition.push(hash_vm_before_gadget.clone());
        inputs_transition.push(hash_vm_after_gadget.clone());
        let hash_transition_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs_transition).unwrap();
        hash_transition_gadget.enforce_equal(&public_var)?;
    
        println!("Made circuit");
        println!("before {}, after {}", before.hash(&self.params), after.hash(&self.params));
//        println!("before {}, after {}", hash_vm_before_gadget.value().unwrap(), hash_vm_after_gadget.value().unwrap());

        Ok(())
    }
}

