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
pub struct MemoryCircuit {
    pub before: VM,
    pub after: VM,
    pub params: PoseidonParameters<Fr>,
    pub idx: usize,
}

/*
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
*/

struct MemoryState {
    addr: FpVar<Fr>,
    step: FpVar<Fr>,
    value: FpVar<Fr>,
}

fn generate_step(
    cs: ConstraintSystemRef<Fr>,
    params: &PoseidonParameters<Fr>,
    params_g: &CRHParametersVar::<Fr>,
    before: VM,
    after: VM,
    state: MemoryState,
    idx: usize, // memory index
    is_set: bool, // is get or set
) -> Result<(FpVar<Fr>, MemoryState), SynthesisError> {
    // Generate variables
    let step_var = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(before.step_counter as u32))).unwrap());
    let step_after_var = step_var.clone() + FpVar::Constant(Fr::from(0));

    let read_before_var = state.value.clone();
    let read_after_var = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(after.locals[idx]))).unwrap());

    let stack_base_hash = if is_set {
        after.hash_stack(&params)
    } else {
        before.hash_stack(&params)
    };
    let control_hash = before.hash_control(&params);
    let stack_base_var = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(stack_base_hash)).unwrap());
    let control_var = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(control_hash)).unwrap());

    let pc_after_hash = hash_code(&params, &after.pc);
    let pc_after_var = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(pc_after_hash)).unwrap());

    let idx_var = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(idx as u32))).unwrap());

    let bool_var = Boolean::from(AllocatedBool::<Fr>::new_witness(cs.clone(), || Ok(is_set)).unwrap());

    // Generate set
    let stack_after_set = stack_base_var.clone();
    let stack_before_set = CRHGadget::<Fr>::evaluate(&params_g, &vec![
        read_after_var.clone(), stack_base_var.clone()
    ]).unwrap();
    let hash_pc_before_set = CRHGadget::<Fr>::evaluate(&params_g, &vec![
        FpVar::Constant(Fr::from(5)), idx_var.clone(), pc_after_var.clone()
    ]).unwrap();

    // Validity of set
    // Two cases, default value or stored value
    // let default_var = FpVar::Constant(Fr::from(0));

    // Generate get
    let stack_before_get = stack_base_var.clone();
    let stack_after_get = CRHGadget::<Fr>::evaluate(&params_g, &vec![
        read_after_var.clone(), stack_base_var.clone()
    ]).unwrap();
    let hash_pc_before_get = CRHGadget::<Fr>::evaluate(&params_g, &vec![
        FpVar::Constant(Fr::from(4)), idx_var.clone(), pc_after_var.clone()
    ]).unwrap();

    // Select set or get
    let stack_before_var = bool_var.select(&stack_before_set, &stack_before_get).unwrap();
    let stack_after_var = bool_var.select(&stack_after_set, &stack_after_get).unwrap();
    let hash_pc_before_var = bool_var.select(&hash_pc_before_set, &hash_pc_before_get).unwrap();

    // Compute VM hash before
    let mut inputs_vm_before = Vec::new();
    inputs_vm_before.push(hash_pc_before_var);
    inputs_vm_before.push(stack_before_var);
    inputs_vm_before.push(step_var.clone());
    inputs_vm_before.push(control_var.clone());
    let hash_vm_before_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs_vm_before).unwrap();

    // Compute VM hash after
    let mut inputs_vm_after = Vec::new();
    inputs_vm_after.push(pc_after_var);
    inputs_vm_after.push(stack_after_var);
    inputs_vm_after.push(step_after_var);
    inputs_vm_after.push(control_var.clone());
    let hash_vm_after_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs_vm_after).unwrap();

    let mut inputs_transition = Vec::new();
    inputs_transition.push(hash_vm_before_gadget.clone());
    inputs_transition.push(hash_vm_after_gadget.clone());
    let hash_transition_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs_transition).unwrap();

    println!("Made memory op");
    println!("before {}, after {}", before.hash(&params), after.hash(&params));
    // println!("before {}, after {}", hash_vm_before_gadget.value().unwrap(), hash_vm_after_gadget.value().unwrap());

    let next_state = MemoryState {
        addr: idx_var,
        step: step_var,
        value: read_after_var,
    };

    Ok((hash_transition_gadget, next_state))
    
}

/*
impl ConstraintSynthesizer<Fr> for MemoryCircuit {
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
*/