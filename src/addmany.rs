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
pub struct AddManyCircuit {
    pub steps: Vec<(VM,VM)>,
    pub params: PoseidonParameters<Fr>,
}

impl InstructionCircuit for AddManyCircuit {
    fn calc_hash(&self) -> Fr {
        panic!("calc hash");
    }
    fn transition(&self) -> Transition {
        panic!("transition")
    }
}

fn generate_step(cs: ConstraintSystemRef<Fr>, params: PoseidonParameters<Fr>, params_g: &CRHParametersVar::<Fr>, before: VM, after: VM)
-> Result<FpVar<Fr>, SynthesisError> {
    let elen = before.expr_stack.len();

    let pc_hash = hash_code(&params, &after.pc);
    let stack_hash = hash_list(&params, &before.expr_stack[..elen-2].iter().map(|a| Fr::from(*a)).collect::<Vec<Fr>>());
    let locals_hash = before.hash_locals(&params);
    let control_hash = before.hash_control(&params);

    let p1 = before.expr_stack[elen - 1];
    let p2 = before.expr_stack[elen - 2];

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

    let mut inputs_stack_before2 = Vec::new();
    inputs_stack_before2.push(var_b.clone());
    inputs_stack_before2.push(FpVar::Var(
        AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(stack_hash)).unwrap(),
    ));
    let hash_stack_before2_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs_stack_before2).unwrap();

    let mut inputs_stack_before = Vec::new();
    inputs_stack_before.push(var_a.clone());
    inputs_stack_before.push(hash_stack_before2_gadget);
    let hash_stack_before_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs_stack_before).unwrap();

    let mut inputs_stack_after = Vec::new();
    // TODO: check that 32-bit
    inputs_stack_after.push(var_a.clone() + var_b.clone());
    inputs_stack_after.push(FpVar::Var(
        AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(stack_hash)).unwrap(),
    ));
    let hash_stack_after_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs_stack_after).unwrap();

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

    Ok(hash_transition_gadget)
}

impl ConstraintSynthesizer<Fr> for AddManyCircuit {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<Fr>,
    ) -> Result<(), SynthesisError> {
        let params_g = CRHParametersVar::<Fr>::new_witness(cs.clone(), || Ok(self.params.clone())).unwrap();
        // make each step
        let mut vars = vec![];
        for el in self.steps {
            let var = generate_step(cs.clone(), self.params.clone(), &params_g, el.0, el.1);
            vars.push(var);
        }
        // println!("num constraints {}, valid {}", cs.num_constraints(), cs.is_satisfied().unwrap());
        println!("num constraints {}", cs.num_constraints());
        Ok(())
    }
}

pub fn test(params: &PoseidonParameters<Fr>, step: (VM, VM)) {
    use ark_std::test_rng;
    use crate::InnerSNARK;
    use ark_crypto_primitives::CircuitSpecificSetupSNARK;
    use ark_crypto_primitives::SNARK;
    let cs_sys = ConstraintSystem::<Fr>::new();
    let cs = ConstraintSystemRef::new(cs_sys);
    let mut steps = vec![];
    for i in 0..16 {
        steps.push(step.clone())
    }
    let circuit = AddManyCircuit {
        params: params.clone(),
        steps,
    };
    // circuit.generate_constraints(cs);
    let mut rng = test_rng();
    println!("Setting up circuit");
    let (pk, vk) = InnerSNARK::setup(circuit.clone(), &mut rng).unwrap();
    println!("Testing prove");
    let proof = InnerSNARK::prove(&pk, circuit.clone(), &mut rng).unwrap();
}
