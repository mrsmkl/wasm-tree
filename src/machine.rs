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
use ark_r1cs_std::fields::FieldVar;
use ark_r1cs_std::ToBitsGadget;

use crate::{VM,Transition,hash_code};
use crate::InstructionCircuit;
use crate::hash::{Params, poseidon_gadget, Proof, make_path};

#[derive(Debug, Clone)]
pub struct Machine {
    valueStack : FpVar<Fr>,
    internalStack : FpVar<Fr>,
    blockStack : FpVar<Fr>,
    frameStack : FpVar<Fr>,

    globalStateHash : FpVar<Fr>,
    moduleIdx : FpVar<Fr>,
    functionIdx : FpVar<Fr>,
    functionPc : FpVar<Fr>,
    modulesRoot : FpVar<Fr>,
}

pub fn hash_machine(params: &Params, mach: &Machine) -> FpVar<Fr> {
    poseidon_gadget(&params, vec![
        mach.valueStack.clone(),
        mach.internalStack.clone(),
        mach.blockStack.clone(),
        mach.frameStack.clone(),
        mach.globalStateHash.clone(),
        mach.moduleIdx.clone(),
        mach.functionIdx.clone(),
        mach.functionPc.clone(),
        mach.modulesRoot.clone(),
    ])
}

#[derive(Debug, Clone)]
pub struct Module {
    globalsMerkleRoot: FpVar<Fr>,
    moduleMemory: FpVar<Fr>,
    tablesMerkleRoot: FpVar<Fr>,
    functionsMerkleRoot: FpVar<Fr>,
    internalsOffset: FpVar<Fr>,
}

pub fn hash_module(params: &Params, mach: &Module) -> FpVar<Fr> {
    poseidon_gadget(&params, vec![
        mach.globalsMerkleRoot.clone(),
        mach.moduleMemory.clone(),
        mach.tablesMerkleRoot.clone(),
        mach.functionsMerkleRoot.clone(),
        mach.internalsOffset.clone(),
    ])
}

#[derive(Debug, Clone)]
pub struct Instruction {
    opcode: FpVar<Fr>,
    argumentData: FpVar<Fr>,
}

fn hash_instruction(params: &Params, inst: &Instruction) -> FpVar<Fr> {
    poseidon_gadget(&params, vec![
        inst.opcode.clone(),
        inst.argumentData.clone(),
    ])
}

#[derive(Debug, Clone)]
pub struct Value {
    value: FpVar<Fr>,
    ty: FpVar<Fr>,
}

fn hash_value(params: &Params, inst: &Value) -> FpVar<Fr> {
    poseidon_gadget(&params, vec![
        inst.value.clone(),
        inst.ty.clone(),
    ])
}

pub fn prove_instr(
    cs: ConstraintSystemRef<Fr>,
    params : &Params,
    machine: &Machine,
    mole: &Module,
    inst: Fr,
    mod_proof: &Proof,
    inst_proof: &Proof,
    func_proof: &Proof,
) -> FpVar<Fr> {
    let mole_hash = hash_module(params, mole);
    let (mole_root, mole_idx) = make_path(cs.clone(), 16, params, mole_hash, mod_proof);
    mole_root.enforce_equal(&machine.modulesRoot).unwrap();
    mole_idx.enforce_equal(&machine.moduleIdx).unwrap();
    let inst_var = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(inst.clone())).unwrap());
    let (inst_root, inst_idx) = make_path(cs.clone(), 20, params, inst_var.clone(), inst_proof);
    inst_idx.enforce_equal(&machine.functionPc).unwrap();
    let (func_root, func_idx) = make_path(cs.clone(), 16, params, inst_root, func_proof);
    func_root.enforce_equal(&mole.functionsMerkleRoot).unwrap();
    func_idx.enforce_equal(&machine.functionIdx).unwrap();

    inst_var
}

#[derive(Debug, Clone)]
pub struct Stack {
    values: Vec<FpVar<Fr>>,
    base: FpVar<Fr>,
}

// stack: perhaps there should just be several alternatives for different length stacks ...
pub fn hash_stack(
    params : &Params,
    stack: &Stack
) -> FpVar<Fr> {
    // compute root from base
    let mut root = stack.base.clone();
    for el in stack.values.iter().rev() {
        root = poseidon_gadget(&params, vec![
            el.clone(),
            root.clone(),
        ])
    }
    root
}

impl Stack {
    fn push(&mut self, v: FpVar<Fr>) {
        self.values.push(v.clone());
    }
    fn pop(&mut self) -> FpVar<Fr> {
        self.values.pop().unwrap()
    }
    fn based(v: FpVar<Fr>) -> Self {
        Stack {
            values: vec![],
            base: v,
        }
    }
}

#[derive(Debug, Clone)]
pub struct MachineWithStack {
    valueStack : Stack,
    internalStack : Stack,
    blockStack : Stack,
    frameStack : Stack,

    globalStateHash : FpVar<Fr>,
    moduleIdx : FpVar<Fr>,
    functionIdx : FpVar<Fr>,
    functionPc : FpVar<Fr>,
    modulesRoot : FpVar<Fr>,

    valid: Boolean<Fr>,
}

// There can be savings by sharing the hashing of stacks ...
pub fn elim_stack(params : &Params, mach: &MachineWithStack) -> Machine {
    Machine {
        valueStack : hash_stack(params, &mach.valueStack),
        internalStack : hash_stack(params, &mach.internalStack),
        blockStack : hash_stack(params, &mach.blockStack),
        frameStack : hash_stack(params, &mach.frameStack),
    
        globalStateHash : mach.globalStateHash.clone(),
        moduleIdx : mach.moduleIdx.clone(),
        functionIdx : mach.functionIdx.clone(),
        functionPc : mach.functionPc.clone(),
        modulesRoot : mach.modulesRoot.clone(),
    }
}

pub fn check_instruction(mach: &MachineWithStack, expected: u32, inst: &Instruction) -> MachineWithStack {
    let expected = FpVar::constant(Fr::from(expected));
    let mut mach = mach.clone();
    mach.valid = mach.valid.and(&inst.opcode.is_eq(&expected).unwrap()).unwrap();
    mach
}

pub fn execute_const(params: &Params, mach: &MachineWithStack, ty: u32, inst: &Instruction) -> MachineWithStack {
    let mut mach = mach.clone();
    let v = Value {
        value: inst.argumentData.clone(),
        ty: FpVar::constant(Fr::from(ty)),
    };
    mach.valueStack.push(hash_value(params, &v));
    mach
}

pub fn enforce_i32(v: FpVar<Fr>) {
    let bits = v.to_bits_le().unwrap();
    let res = Boolean::le_bits_to_fp_var(&bits[0..32]).unwrap();
    res.enforce_equal(&v).unwrap();
}

pub fn execute_drop(_params: &Params, mach: &MachineWithStack) -> MachineWithStack {
    let mut mach = mach.clone();
    let _popped = mach.valueStack.pop();
    mach
}

pub fn execute_select(_params: &Params, mach: &MachineWithStack) -> MachineWithStack {
    let mut mach = mach.clone();
    let selector = mach.valueStack.pop();
    let b = mach.valueStack.pop();
    let a = mach.valueStack.pop();

    let sel_bool = selector.is_eq(&FpVar::constant(Fr::from(0))).unwrap();
    let a_b = sel_bool.select(&a, &b).unwrap();
    mach.valueStack.push(a_b);
    mach
}

pub fn execute_block(_params: &Params, mach: &MachineWithStack, _inst: &Instruction) -> MachineWithStack {
    let mut mach = mach.clone();
    let target_pc = mach.functionPc.clone();
    enforce_i32(target_pc.clone());
    mach.blockStack.push(target_pc);
    mach
}

pub fn execute_branch(_params: &Params, mach: &MachineWithStack) -> MachineWithStack {
    let mut mach = mach.clone();
    mach.functionPc = mach.blockStack.pop();
    mach
}

pub fn execute_branch_if(params: &Params, mach: &MachineWithStack) -> MachineWithStack {
    let mut mach = mach.clone();
    let selector = mach.valueStack.pop();

    let sel_bool = selector.is_eq(&FpVar::constant(Fr::from(0))).unwrap();
    // There are two alternative block stacks, they have to be computed here
    let mut bs_1 = mach.blockStack.clone();
    let bs_2 = mach.blockStack.clone();
    let _popped = bs_1.pop();

    mach.functionPc = sel_bool.select(&mach.blockStack.pop(), &mach.functionPc).unwrap();
    mach.blockStack = Stack::based(sel_bool.select(&hash_stack(params, &bs_1), &hash_stack(params, &bs_2)).unwrap());
    mach
}

#[derive(Debug, Clone)]
pub struct StackFrame {
    returnPc: Value,
    localsMerkleRoot: FpVar<Fr>,
    callerModule: FpVar<Fr>,
    callerModuleInternals: FpVar<Fr>,
}

fn hash_stack_frame(params: &Params, frame: &StackFrame) -> FpVar<Fr> {
    poseidon_gadget(&params, vec![
        hash_value(params, &frame.returnPc),
        frame.localsMerkleRoot.clone(),
        frame.callerModule.clone(),
        frame.callerModuleInternals.clone(),
    ])
}

pub fn execute_return(params: &Params, mach: &MachineWithStack, frame: &StackFrame, internal_ref_ty: u32) -> MachineWithStack {
    let mut mach = mach.clone();
    let type_eq = frame.returnPc.ty.is_eq(&FpVar::constant(Fr::from(internal_ref_ty))).unwrap();
    let frame_hash = mach.frameStack.pop();
    let hash_eq = frame_hash.is_eq(&hash_stack_frame(&params, frame)).unwrap();
    mach.valid = mach.valid.and(&hash_eq).unwrap().and(&type_eq).unwrap();
    let data = frame.returnPc.value.to_bits_le().unwrap();
    mach.functionPc = Boolean::le_bits_to_fp_var(&data[0..32]).unwrap();
    mach.functionIdx = Boolean::le_bits_to_fp_var(&data[32..64]).unwrap();
    mach.moduleIdx = Boolean::le_bits_to_fp_var(&data[64..96]).unwrap();
    mach
}

const INTERNAL_TYPE_REF = 6u32;

fn create_return_value(mach: &MachineWithStack) -> FpVar<Fr> {
    let value = mach.functionPc + mach.functionIdx * FpVar::constant(Fr::from(1 << 32));
    Value {
        value,
        ty: FpVar::constant(Fr::from(INTERNAL_TYPE_REF)),
    }
}

