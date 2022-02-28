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
use std::cmp::Ordering;

use crate::{VM,Transition,hash_code};
use crate::InstructionCircuit;
use crate::CodeTree;

use ark_r1cs_std::R1CSVar;

#[derive(Debug, Clone)]
pub struct MemoryCircuit {
    pub transitions: Vec<Transition>,
    pub params: PoseidonParameters<Fr>,
    pub start_addr: u32,
    pub start_step: u32,
    pub start_value: u32,

    pub end_addr: u32,
    pub end_step: u32,
    pub end_value: u32,
}

fn get_info(vm: &VM) -> (u32, bool) {
    match vm.pc[0].clone() {
        CodeTree::CSetLocal(i) => (i, true),
        CodeTree::CGetLocal(i) => (i, false),
        _ => panic!("Not a memory instruction")
    }
}

#[derive(Debug, Clone)]
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
    idx: u32, // memory index
    is_set: bool, // is get or set
) -> Result<(FpVar<Fr>, MemoryState), SynthesisError> {
    // Generate variables
    let step_var = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(before.step_counter as u32))).unwrap());
    let step_after_var = step_var.clone() + FpVar::Constant(Fr::from(0));

    let read_after_var = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(after.locals[idx as usize]))).unwrap());

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

    //// Validity of set
    // Two cases, same address or new address (larger)
    let same_address_var = state.addr.is_eq(&idx_var).unwrap();
    // Check if step counter is larger
    let step_counter_larger = step_var.is_cmp(&state.step, Ordering::Greater, false)?;
    let address_greater = idx_var.is_cmp(&state.addr, Ordering::Greater, false).unwrap();

    let valid_set = same_address_var.and(&step_counter_larger).unwrap().or(&address_greater)?;

    // Generate get
    let stack_before_get = stack_base_var.clone();
    let stack_after_get = CRHGadget::<Fr>::evaluate(&params_g, &vec![
        read_after_var.clone(), stack_base_var.clone()
    ]).unwrap();
    let hash_pc_before_get = CRHGadget::<Fr>::evaluate(&params_g, &vec![
        FpVar::Constant(Fr::from(4)), idx_var.clone(), pc_after_var.clone()
    ]).unwrap();

    // Validity of get
    // Two cases, default value (new address) or stored value
    let default_var = FpVar::Constant(Fr::from(0));
    let check_var = same_address_var.select(&state.value, &default_var)?;
    let valid_get = check_var.is_eq(&read_after_var)?.and(&valid_set)?;

    // Select set or get
    let stack_before_var = bool_var.select(&stack_before_set, &stack_before_get).unwrap();
    let stack_after_var = bool_var.select(&stack_after_set, &stack_after_get).unwrap();
    let hash_pc_before_var = bool_var.select(&hash_pc_before_set, &hash_pc_before_get).unwrap();

    let valid_var = bool_var.select(&valid_set, &valid_get).unwrap();
    valid_var.enforce_equal(&Boolean::constant(true))?;

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
    println!("before {}, after {}", before.hash_mem(&params), after.hash_mem(&params));
    println!("before {}, after {}", hash_vm_before_gadget.value().unwrap(), hash_vm_after_gadget.value().unwrap());

    let next_state = MemoryState {
        addr: idx_var,
        step: step_var,
        value: read_after_var,
    };

    Ok((hash_transition_gadget, next_state))
    
}

use crate::hash_pair;

fn hash_tree(params: &PoseidonParameters<Fr>, trs: Vec<Transition>) -> Fr {
    let mut tree = vec![];
    for tr in trs {
        tree.push(hash_pair(&params, &tr.before.hash_mem(&params), &tr.after.hash_mem(&params)));
    }
    while tree.len() > 1 {
        let mut next_vars = vec![];
        for i in 0..tree.len()/2 {
            let hash_var = hash_pair(&params, &tree[2*i].clone(), &tree[2*i+1].clone());
            next_vars.push(hash_var);
        }
        tree= next_vars;
    }
    tree[0]
}

impl ConstraintSynthesizer<Fr> for MemoryCircuit {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<Fr>,
    ) -> Result<(), SynthesisError> {
        let params_g = CRHParametersVar::<Fr>::new_witness(cs.clone(), || Ok(self.params.clone())).unwrap();
        ////
        let first_step_var = FpVar::Var(AllocatedFp::<Fr>::new_input(cs.clone(), || Ok(Fr::from(self.start_step))).unwrap());
        let first_addr_var = FpVar::Var(AllocatedFp::<Fr>::new_input(cs.clone(), || Ok(Fr::from(self.start_addr))).unwrap());
        let first_value_var = FpVar::Var(AllocatedFp::<Fr>::new_input(cs.clone(), || Ok(Fr::from(self.start_value))).unwrap());
        let end_step_var = FpVar::Var(AllocatedFp::<Fr>::new_input(cs.clone(), || Ok(Fr::from(self.end_step))).unwrap());
        let end_addr_var = FpVar::Var(AllocatedFp::<Fr>::new_input(cs.clone(), || Ok(Fr::from(self.end_addr))).unwrap());
        let end_value_var = FpVar::Var(AllocatedFp::<Fr>::new_input(cs.clone(), || Ok(Fr::from(self.end_value))).unwrap());

        let root_hash = hash_tree(&self.params, self.transitions.clone());
        let root_var = FpVar::Var(AllocatedFp::<Fr>::new_input(cs.clone(), || Ok(root_hash)).unwrap());

        let mut state = MemoryState {
            step: first_step_var,
            addr: first_addr_var,
            value: first_value_var,
        };
        let mut tr_vars = vec![];
        for tr in self.transitions.clone() {
            let (idx, is_set) = get_info(&tr.before);
            let (tr_var, next_state) = generate_step(cs.clone(), &self.params, &params_g, tr.before, tr.after, state, idx, is_set)?;
            state = next_state;
            tr_vars.push(tr_var);
        }

        // Check end state
        end_step_var.enforce_equal(&state.step)?;
        end_addr_var.enforce_equal(&state.addr)?;
        end_value_var.enforce_equal(&state.value)?;

        // Generate merkle tree
        while tr_vars.len() > 1 {
            let mut next_vars = vec![];
            for i in 0..tr_vars.len()/2 {
                let hash_var = CRHGadget::<Fr>::evaluate(&params_g, &vec![tr_vars[2*i].clone(), tr_vars[2*i+1].clone()]).unwrap();
                next_vars.push(hash_var);
            }
            tr_vars = next_vars;
        }
        root_var.enforce_equal(&tr_vars[0])?;

        Ok(())
    }
}

// Sorting memory ops

struct MemOp {
    tr: Transition,
    idx: u32,
    step: u32,
}

fn get_memory(ts: Vec<Transition>) -> Vec<Transition> {
    let mut res = vec![];
    for t in ts {
        match t.before.pc[0] {
            CodeTree::CSetLocal(idx) => res.push(MemOp {tr: t.clone(), idx, step: t.before.step_counter as u32}),
            CodeTree::CGetLocal(idx) => res.push(MemOp {tr: t.clone(), idx, step: t.before.step_counter as u32}),
            _ => {},
        }
    };
    res.sort_by(|a, b| ((a.idx,a.step)).cmp(&(b.idx,b.step)));
    res.iter().map(|a| a.tr.clone()).collect()
}

fn get_last_value(ts: &Vec<Transition>) -> u32 {
    for tr in ts.iter().rev() {
        match tr.before.pc[0] {
            CodeTree::CSetLocal(_) => return *tr.before.expr_stack.last().unwrap(),
            _ => {},
        }
    };
    return 0;
}

pub fn test_memory(params: &PoseidonParameters<Fr>, ts: Vec<Transition>) {
    let transitions = get_memory(ts);
    let last = transitions.last().unwrap().clone();
    let first = transitions[0].clone();
    let end_value = get_last_value(&transitions);
    let circuit = MemoryCircuit {
        transitions,
        params: params.clone(),
        start_addr: 0,
        start_step: first.before.step_counter as u32,
        start_value: 0,
    
        end_addr: 1,
        end_step: last.before.step_counter as u32,
        end_value,
    };
    crate::test_circuit(circuit);
}

