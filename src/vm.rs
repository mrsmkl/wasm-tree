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
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::boolean::AllocatedBool;
use ark_r1cs_std::select::CondSelectGadget;
use ark_r1cs_std::fields::FieldVar;

use crate::hash::{Params,poseidon,poseidon_gadget,generate_params};

// New version of VM

#[derive(Debug, Clone)]
pub struct VM {
    pub registers: Vec<u64>,
    pub params: Params,
    pub control_pointer: usize,
    pub frame_pointer: usize,
    pub mem_counter: usize,
    // pub pc: Vec<CodeTree>,
    pub pc: Vec<u64>,
}

#[derive(Debug, Clone)]
pub struct VMVar {
    pub registers: Vec<FpVar<Fr>>,
    pub control_pointer: FpVar<Fr>,
    pub frame_pointer: FpVar<Fr>,
    pub mem_counter: FpVar<Fr>,
    pub pc_hash: FpVar<Fr>,
}

#[derive(Debug, Clone)]
pub struct MemOpVar {
    pub counter: FpVar<Fr>,
    pub address: FpVar<Fr>,
    pub value: FpVar<Fr>,
    pub is_set: Boolean<Fr>,
}

fn hash_memop(params: &Params, memop: MemOpVar) -> FpVar<Fr> {
    poseidon_gadget(params, vec![
        memop.counter,
        memop.address,
        memop.value,
        From::from(memop.is_set),
    ])
}

fn hash_code(params: &Params, code: &[u64]) -> Fr {
    let mut res = Fr::from(0);
    for op in code.iter().rev() {
        // println!("hashing {:?}", op);
        let mut inputs = vec![];
        inputs.push(Fr::from(*op));
        inputs.push(res);
        res = poseidon(&params, inputs);
    }
    res
}

fn decode(a: u64, n: usize) -> Vec<bool> {
    let mut res = vec![];
    let mut a = a;
    for _i in 0..n {
        let x = a%2;
        res.push(if x == 0 { false } else { true });
        a = a/2;
    }
    res
}

fn decode_var(cs: &ConstraintSystemRef<Fr>, a: u64, n: usize) -> Vec<Boolean<Fr>> {
    decode(a, n).iter().map(|b| Boolean::from(AllocatedBool::<Fr>::new_witness(cs.clone(), || Ok(b)).unwrap())).collect::<Vec<_>>()
}

fn decode2(a: u128, n: usize) -> Vec<bool> {
    let mut res = vec![];
    let mut a = a;
    for _i in 0..n {
        let x = a%2;
        res.push(if x == 0 { false } else { true });
        a = a/2;
    }
    res
}

fn decode_var2(cs: &ConstraintSystemRef<Fr>, a: u128, n: usize) -> Vec<Boolean<Fr>> {
    decode2(a, n).iter().map(|b| Boolean::from(AllocatedBool::<Fr>::new_witness(cs.clone(), || Ok(b)).unwrap())).collect::<Vec<_>>()
}

fn decode_op(a: u64) -> (u64, usize, usize) {
    (a%16, ((a/16)%4) as usize, ((a/(16*4))%4) as usize)
}

fn compute(op: u64, a: u64, b: u64) -> u128 {
    if op == 0 {
        (a as u128) + (b as u128)
    } else if op == 1 {
        (a as u128) * (b as u128)
    } else /* if op == 2 */ {
        (1u128 << 64) + (a as u128) - (b as u128)
    }
}

fn generate_step(cs: &ConstraintSystemRef<Fr>, before: VM, before_var: VMVar) -> Result<VMVar, SynthesisError> {
    // For PC, just make the hash
    let params = &before.params;
    let inst = before.pc[0];
    let inst_bools = decode_var(cs, inst, 16);
    let next_pc_hash = hash_code(params, &before.pc[1..]);
    let next_hash = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(next_pc_hash))).unwrap());
    // Instruction comes from boolean wires...
    let inst_var = Boolean::le_bits_to_fp_var(&inst_bools).unwrap();
    let prev_hash = poseidon_gadget(params, vec![inst_var, next_hash.clone()]);
    before_var.pc_hash.enforce_equal(&prev_hash).unwrap();

    // Select registers
    let a_var = FpVar::conditionally_select_power_of_two_vector(&inst_bools[0..2], &before_var.registers).unwrap();
    let b_var = FpVar::conditionally_select_power_of_two_vector(&inst_bools[2..4], &before_var.registers).unwrap();

    let add_var = a_var.clone() + b_var.clone();
    let mul_var = a_var.clone() * b_var.clone();
    let minus_var = (a_var.clone() - b_var.clone()) + FpVar::constant(Fr::from(1u128 << 64));
    let neg_var = FpVar::constant(Fr::from(1u128 << 64)) - a_var.clone();

    // result will have 64 bits
    // or for multiplication there will be 128 bits
    let (op, r1, r2) = decode_op(inst);
    let result = compute(op, before.registers[r1], before.registers[r2]);
    let result_bools = decode_var2(cs, result, 128);
    let result_var = Boolean::le_bits_to_fp_var(&result_bools[0..64]).unwrap();
    let over_var = Boolean::le_bits_to_fp_var(&result_bools[64..128]).unwrap();
    let combined_var = result_var.clone() + FpVar::constant(Fr::from(1u128 << 64)) * over_var.clone();

    let ops = vec![add_var, mul_var, minus_var, neg_var];
    let selected = FpVar::conditionally_select_power_of_two_vector(&inst_bools[4..6], &ops).unwrap();

    combined_var.enforce_equal(&selected).unwrap();

    // Then need to select the result registers
    let r1var = FpVar::conditionally_select_power_of_two_vector(&inst_bools[6..7], &vec![before_var.registers[0].clone(), selected.clone()]).unwrap();
    let r2var = FpVar::conditionally_select_power_of_two_vector(&inst_bools[7..8], &vec![before_var.registers[1].clone(), selected.clone()]).unwrap();
    let r3var = FpVar::conditionally_select_power_of_two_vector(&inst_bools[8..9], &vec![before_var.registers[2].clone(), selected.clone()]).unwrap();
    let r4var = FpVar::conditionally_select_power_of_two_vector(&inst_bools[9..10], &vec![before_var.registers[3].clone(), selected.clone()]).unwrap();

    Ok(VMVar {
        registers: vec![r1var, r2var, r3var, r4var],
        control_pointer: before_var.control_pointer.clone(),
        frame_pointer: before_var.frame_pointer.clone(),
        mem_counter: before_var.mem_counter.clone(),
        pc_hash: next_hash,
    })
}

fn generate_memop(cs: &ConstraintSystemRef<Fr>, before: VM, before_var: VMVar, control_stack: &Vec<Fr>) -> Result<(VMVar, MemOpVar), SynthesisError> {
    // For PC, just make the hash
    let params = &before.params;
    let inst = before.pc[0];
    let inst_bools = decode_var(cs, inst, 32);
    let next_pc_hash = hash_code(params, &before.pc[1..]);
    let next_hash = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(next_pc_hash))).unwrap());
    // Instruction comes from boolean wires...
    let inst_var = Boolean::le_bits_to_fp_var(&inst_bools).unwrap();
    let prev_hash = poseidon_gadget(params, vec![inst_var, next_hash.clone()]);
    before_var.pc_hash.enforce_equal(&prev_hash).unwrap();

    // Select registers
    let a_var = FpVar::conditionally_select_power_of_two_vector(&inst_bools[0..2], &before_var.registers).unwrap();
    let b_var = FpVar::conditionally_select_power_of_two_vector(&inst_bools[2..4], &before_var.registers).unwrap();

    // Operations: save PC, jump, read memory, write memory

    // All will inc mem counter
    let mem_counter = before_var.mem_counter.clone() + FpVar::constant(Fr::from(1));

    // Save PC
    let save_control_pointer = before_var.control_pointer.clone() + FpVar::constant(Fr::from(1));
    let save_address = save_control_pointer.clone() + FpVar::constant(Fr::from(1u64 << 32));
    let save_value = next_hash.clone();
    // let save_is_set = Boolean::constant(true);
    // TODO: actually there should be somekind of branching point (given as immediate?)

    // Jump
    let jump_var = Boolean::le_bits_to_fp_var(&inst_bools[4..10]).unwrap();
    let jump_control_pointer = before_var.control_pointer.clone() - jump_var.clone();
    // TODO: compute correct location
    let jump_pc = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(control_stack[0].clone())).unwrap());
    let jump_address = jump_control_pointer.clone() + FpVar::constant(Fr::from(1u64 << 32));
    let jump_value = jump_pc.clone();
    // let jump_is_set = Boolean::constant(false);
    // TODO: jump control (check from register b)

    // Read
    let read_address = a_var.clone();
    // TODO: actual memory
    let read_value = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(control_stack[0].clone())).unwrap());
    // let read_is_set = Boolean::constant(false);

    // Write
    let write_address = a_var.clone();
    // TODO: actual memory
    let write_value = b_var;
    // let write_is_set = Boolean::constant(true);

    let selected = write_value.clone();

    // Then need to select the result registers
    let r1var = FpVar::conditionally_select_power_of_two_vector(&inst_bools[10..11], &vec![before_var.registers[0].clone(), selected.clone()]).unwrap();
    let r2var = FpVar::conditionally_select_power_of_two_vector(&inst_bools[11..12], &vec![before_var.registers[1].clone(), selected.clone()]).unwrap();
    let r3var = FpVar::conditionally_select_power_of_two_vector(&inst_bools[12..13], &vec![before_var.registers[2].clone(), selected.clone()]).unwrap();
    let r4var = FpVar::conditionally_select_power_of_two_vector(&inst_bools[13..14], &vec![before_var.registers[3].clone(), selected.clone()]).unwrap();

    let control_pointer = FpVar::conditionally_select_power_of_two_vector(&inst_bools[14..16], &vec![before_var.control_pointer.clone(), save_control_pointer, jump_control_pointer.clone(), jump_control_pointer]).unwrap();

    let pc_hash = FpVar::conditionally_select_power_of_two_vector(
        &inst_bools[16..17],
        &vec![next_hash, jump_pc],
    ).unwrap();

    let after = VMVar {
        registers: vec![r1var, r2var, r3var, r4var],
        control_pointer,
        frame_pointer: before_var.frame_pointer.clone(),
        mem_counter: mem_counter.clone(),
        pc_hash,
    };

    let address = FpVar::conditionally_select_power_of_two_vector(
        &inst_bools[18..20],
        &vec![save_address, jump_address, read_address, write_address],
    ).unwrap();

    let value = FpVar::conditionally_select_power_of_two_vector(
        &inst_bools[20..22],
        &vec![save_value, jump_value, read_value, write_value],
    ).unwrap();

    let memop = MemOpVar {
        counter: mem_counter,
        address,
        value,
        is_set: inst_bools[17].clone(),
    };

    Ok((after, memop))
}

fn vmvar(cs: &ConstraintSystemRef<Fr>, params: &Params, vm: VM) -> VMVar {
    let r1var = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(vm.registers[0]))).unwrap());
    let r2var = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(vm.registers[1]))).unwrap());
    let r3var = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(vm.registers[2]))).unwrap());
    let r4var = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(vm.registers[3]))).unwrap());
    let control_pointer = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(vm.control_pointer as u64))).unwrap());
    let frame_pointer = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(vm.mem_counter as u64))).unwrap());
    let mem_counter = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(vm.mem_counter as u64))).unwrap());
    let pc_hash = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(hash_code(params, &vm.pc))).unwrap());
    VMVar {
        registers: vec![r1var, r2var, r3var, r4var],
        control_pointer,
        frame_pointer,
        mem_counter,
        pc_hash,
    }
}

pub fn test() {
    let cs_sys = ConstraintSystem::<Fr>::new();
    let cs = ConstraintSystemRef::new(cs_sys);
    let params = generate_params();
    let vm = VM {
        params: params.clone(),
        mem_counter: 0,
        frame_pointer: 0,
        control_pointer: 0,
        pc: vec![0,0,0,0,0],
        registers: vec![0,0,0,0],
    };
    let vm_var = vmvar(&cs, &params, vm.clone());
    generate_step(&cs, vm, vm_var).unwrap();
    // println!("gadget {}", res.value().unwrap());
    println!("constraints {}", cs.num_constraints());
}
