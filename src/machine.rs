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
use crate::hash::{Params, poseidon_gadget, Proof, make_path, poseidon};

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

#[derive(Debug, Clone)]
pub struct MachineHint {
    valueStack : Fr,
    internalStack : Fr,
    blockStack : Fr,
    frameStack : Fr,

    globalStateHash : Fr,
    moduleIdx : Fr,
    functionIdx : Fr,
    functionPc : Fr,
    modulesRoot : Fr,
}

fn witness(cs: &ConstraintSystemRef<Fr>, default: &Fr) -> FpVar<Fr> {
    FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(default.clone())).unwrap())
}

impl MachineHint {
    fn convert(&self, cs: ConstraintSystemRef<Fr>) -> Machine {
        Machine {
            valueStack : witness(&cs, &self.valueStack),
            internalStack : witness(&cs, &self.internalStack),
            blockStack : witness(&cs, &self.blockStack),
            frameStack : witness(&cs, &self.frameStack),
        
            globalStateHash : witness(&cs, &self.globalStateHash),
            moduleIdx : witness(&cs, &self.moduleIdx),
            functionIdx : witness(&cs, &self.functionIdx),
            functionPc : witness(&cs, &self.functionPc),
            modulesRoot : witness(&cs, &self.modulesRoot),
        }
    }
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

#[derive(Debug, Clone)]
pub struct ValueHint {
    value: u64,
    ty: u32,
}

#[derive(Debug, Clone)]
pub struct InstructionHint {
    opcode: u64,
    argumentData: u64,
}

impl Value {
    fn default() -> Self {
        Value {
            value: FpVar::constant(Fr::from(0)),
            ty: FpVar::constant(Fr::from(0)),
        }
    }
}

impl ValueHint {
    fn hash(&self, params: &Params) -> Fr {
        poseidon(&params, vec![
            Fr::from(self.value.clone()),
            Fr::from(self.ty.clone()),
        ])
    }
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
    for el in stack.values.iter() {
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
    fn peek(&mut self) -> FpVar<Fr> {
        self.values[self.values.len()-1].clone()
    }
    fn based(v: FpVar<Fr>) -> Self {
        Stack {
            values: vec![],
            base: v,
        }
    }
    fn empty() -> Self {
        Stack {
            values: vec![],
            base: FpVar::constant(Fr::from(0)),
        }
    }
}

const I32_TYPE : u32 = 0u32;
const INTERNAL_TYPE_REF : u32 = 6u32;

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
    inst: Instruction, // Must be the correct instruction
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

fn intro_stack(mach: &Machine, inst: &Instruction) -> MachineWithStack {
    MachineWithStack {
        valueStack : Stack::based(mach.valueStack.clone()),
        internalStack : Stack::based(mach.internalStack.clone()),
        blockStack : Stack::based(mach.blockStack.clone()),
        frameStack : Stack::based(mach.frameStack.clone()),
    
        globalStateHash : mach.globalStateHash.clone(),
        moduleIdx : mach.moduleIdx.clone(),
        functionIdx : mach.functionIdx.clone(),
        functionPc : mach.functionPc.clone(),
        modulesRoot : mach.modulesRoot.clone(),

        valid: Boolean::constant(true),
        inst: inst.clone(),
    }
}

pub fn check_instruction(mach: &MachineWithStack, expected: u32) -> MachineWithStack {
    let expected = FpVar::constant(Fr::from(expected));
    let mut mach = mach.clone();
    mach.valid = mach.valid.and(&mach.inst.opcode.is_eq(&expected).unwrap()).unwrap();
    mach
}

pub fn execute_const(params: &Params, mach: &MachineWithStack, ty: u32) -> MachineWithStack {
    let mut mach = mach.clone();
    let v = Value {
        value: inst.argumentData.clone(),
        ty: FpVar::constant(Fr::from(ty)),
    };
    mach.valueStack.push(hash_value(params, &v));
    mach
}

trait Inst {
    fn execute(&self, params: &Params, mach: &MachineWithStack) -> (MachineWithStack, MachineWithStack);
}

struct InstConstHint {
    inst: InstructionHint,
}

struct InstConst {
    inst: Instruction,
    ty: u32,
}

impl InstConstHint {
    fn default() -> Self {
        let inst = InstructionHint {
            opcode: 0,
            argumentData: 0,
        };
        InstConstHint { inst }
    }
    fn convert(&self, cs: ConstraintSystemRef<Fr>, ty: u32) -> InstConst {
        let inst = Instruction {
            opcode: FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(self.inst.opcode))).unwrap()),
            argumentData: FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(self.inst.argumentData))).unwrap()),
        };
        InstConst {
            ty,
            inst,
        }
    }
}

impl Inst for InstConst {
    fn execute(&self, params: &Params, mach: &MachineWithStack) -> (MachineWithStack, MachineWithStack) {
        let before = mach.clone();
        let after = execute_const(params, mach, self.ty, &self.inst);
        (before, after)
    }
}

/*
fn empty_machine() -> MachineWithStack {
    MachineWithStack {
        valueStack: Stack::empty(),
        internalStack: Stack::empty(),
        blockStack: Stack::empty(),
        frameStack: Stack::empty(),

        globalStateHash: FpVar::constant(Fr::from(0)),
        moduleIdx: FpVar::constant(Fr::from(0)),
        functionIdx: FpVar::constant(Fr::from(0)),
        functionPc: FpVar::constant(Fr::from(0)),
        modulesRoot: FpVar::constant(Fr::from(0)),

        valid: Boolean::constant(false),
    }    
}
*/

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

struct InstDropHint {
    val: u64,
}

struct InstDrop {
    val: FpVar<Fr>,
}

impl Inst for InstDrop {
    fn execute(&self, params: &Params, mach: &MachineWithStack) -> (MachineWithStack, MachineWithStack) {
        let mut mach = mach.clone();
        mach.valueStack.push(self.val.clone());
        let before = mach.clone();
        let after = execute_drop(params, &mach);
        (before, after)
    }
}

impl InstDropHint {
    pub fn default() -> Self {
        InstDropHint {
            val: 0,
        }
    }
}

impl InstDropHint {
    fn convert(&self, cs: ConstraintSystemRef<Fr>) -> InstDrop {
        InstDrop {
            val: FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(self.val))).unwrap()),
        }
    }
}

/*
fn drop_default_machine() -> MachineWithStack {
    let mut mach = empty_machine();
    mach.valueStack.push(FpVar::constant(Fr::from(0)));
    mach
}
*/

/* Combining instructions, how should it work.
   Probably need a lot of witness variables...
*/

enum InstProof {
    ConstI32(InstConstHint),
    ConstI64(InstConstHint),
    ConstF32(InstConstHint),
    ConstF64(InstConstHint),
    Drop(InstDropHint),
}

struct InstWitness {
    const_i32: InstConst,
    const_i64: InstConst,
    const_f32: InstConst,
    const_f64: InstConst,
    drop: InstDrop,
}

fn proof_to_witness(proof: InstProof, cs: ConstraintSystemRef<Fr>) -> InstWitness {
    let mut hint_const_i32 = InstConstHint::default();
    let mut hint_const_i64 = InstConstHint::default();
    let mut hint_const_f32 = InstConstHint::default();
    let mut hint_const_f64 = InstConstHint::default();
    let mut hint_drop = InstDropHint::default();
    use crate::machine::InstProof::*;
    match proof {
        ConstI32(hint) => {
            hint_const_i32 = hint;
        }
        ConstI64(hint) => {
            hint_const_i64 = hint;
        }
        ConstF32(hint) => {
            hint_const_f32 = hint;
        }
        ConstF64(hint) => {
            hint_const_f64 = hint;
        }
        Drop(hint) => {
            hint_drop = hint;
        }
    };
    InstWitness {
        const_i32: hint_const_i32.convert(cs.clone(), 0),
        const_i64: hint_const_i64.convert(cs.clone(), 1),
        const_f32: hint_const_f32.convert(cs.clone(), 2),
        const_f64: hint_const_f64.convert(cs.clone(), 3),
        drop: hint_drop.convert(cs.clone()),
    }
}

/*
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

struct InstSelectHint {
    val1: FpVar<Fr>,
    val2: FpVar<Fr>,
    val3: FpVar<Fr>,
}

impl InstHint for InstSelectHint {
    fn execute(&self, params: &Params, mach: &MachineWithStack) -> (MachineWithStack, MachineWithStack) {
        let mut mach = mach.clone();
        mach.valueStack.push(self.val1.clone());
        mach.valueStack.push(self.val2.clone());
        mach.valueStack.push(self.val3.clone());
        let before = mach.clone();
        let after = execute_select(params, &mach);
        (before, after)
    }
}

impl InstSelectHint {
    pub fn default() -> Self {
        InstSelectHint {
            val1: FpVar::constant(Fr::from(0)),
            val2: FpVar::constant(Fr::from(0)),
            val3: FpVar::constant(Fr::from(0)),
        }
    }
}

pub fn execute_block(_params: &Params, mach: &MachineWithStack) -> MachineWithStack {
    let mut mach = mach.clone();
    let target_pc = mach.functionPc.clone();
    enforce_i32(target_pc.clone());
    mach.blockStack.push(target_pc);
    mach
}

struct InstBlockHint {
}

impl InstHint for InstBlockHint {
    fn execute(&self, params: &Params, mach: &MachineWithStack) -> (MachineWithStack, MachineWithStack) {
        let before = mach.clone();
        let after = execute_drop(params, &mach);
        (before, after)
    }
}

impl InstBlockHint {
    pub fn default() -> Self {
        InstBlockHint {
        }
    }
}

pub fn execute_branch(_params: &Params, mach: &MachineWithStack) -> MachineWithStack {
    let mut mach = mach.clone();
    mach.functionPc = mach.blockStack.pop();
    mach
}

struct InstBranchHint {
    val: FpVar<Fr>,
}

impl InstHint for InstBranchHint {
    fn execute(&self, params: &Params, mach: &MachineWithStack) -> (MachineWithStack, MachineWithStack) {
        let mut mach = mach.clone();
        mach.valueStack.push(self.val.clone());
        let before = mach.clone();
        let after = execute_branch(params, &mach);
        (before, after)
    }
}

impl InstBranchHint {
    pub fn default() -> Self {
        InstBranchHint {
            val: FpVar::constant(Fr::from(0)),
        }
    }
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

struct InstBranchIfHint {
    val1: FpVar<Fr>,
    val2: FpVar<Fr>,
    block: FpVar<Fr>,
}

impl InstHint for InstBranchIfHint {
    fn execute(&self, params: &Params, mach: &MachineWithStack) -> (MachineWithStack, MachineWithStack) {
        let mut mach = mach.clone();
        mach.valueStack.push(self.val1.clone());
        mach.valueStack.push(self.val2.clone());
        mach.blockStack.push(self.block.clone());
        let before = mach.clone();
        let after = execute_branch_if(params, &mach);
        (before, after)
    }
}

impl InstBranchIfHint {
    pub fn default() -> Self {
        InstBranchIfHint {
            val1: FpVar::constant(Fr::from(0)),
            val2: FpVar::constant(Fr::from(0)),
            block: FpVar::constant(Fr::from(0)),
        }
    }
}

#[derive(Debug, Clone)]
pub struct StackFrame {
    returnPc: Value,
    localsMerkleRoot: FpVar<Fr>,
    callerModule: FpVar<Fr>,
    callerModuleInternals: FpVar<Fr>,
}

impl StackFrame {
    fn default() -> Self {
        StackFrame {
            returnPc: Value::default(),
            localsMerkleRoot: FpVar::constant(Fr::from(0)),
            callerModule: FpVar::constant(Fr::from(0)),
            callerModuleInternals: FpVar::constant(Fr::from(0)),
        }
    }
}

fn hash_stack_frame(params: &Params, frame: &StackFrame) -> FpVar<Fr> {
    poseidon_gadget(&params, vec![
        hash_value(params, &frame.returnPc),
        frame.localsMerkleRoot.clone(),
        frame.callerModule.clone(),
        frame.callerModuleInternals.clone(),
    ])
}

pub fn execute_return(params: &Params, mach: &MachineWithStack, frame: &StackFrame) -> MachineWithStack {
    let mut mach = mach.clone();
    let type_eq = frame.returnPc.ty.is_eq(&FpVar::constant(Fr::from(INTERNAL_TYPE_REF))).unwrap();
    let frame_hash = mach.frameStack.pop();
    let hash_eq = frame_hash.is_eq(&hash_stack_frame(&params, frame)).unwrap();
    mach.valid = mach.valid.and(&hash_eq).unwrap().and(&type_eq).unwrap();
    let data = frame.returnPc.value.to_bits_le().unwrap();
    mach.functionPc = Boolean::le_bits_to_fp_var(&data[0..32]).unwrap();
    mach.functionIdx = Boolean::le_bits_to_fp_var(&data[32..64]).unwrap();
    mach.moduleIdx = Boolean::le_bits_to_fp_var(&data[64..96]).unwrap();
    mach
}

struct InstReturnHint {
    frame: StackFrame,
}

impl InstHint for InstReturnHint {
    fn execute(&self, params: &Params, mach: &MachineWithStack) -> (MachineWithStack, MachineWithStack) {
        let mut mach = mach.clone();
        mach.frameStack.push(hash_stack_frame(&params, &self.frame));
        let before = mach.clone();
        let after = execute_return(params, &mach, &self.frame);
        (before, after)
    }
}

impl InstReturnHint {
    pub fn default() -> Self {
        InstReturnHint { frame: StackFrame::default() }
    }
}

fn create_return_value(mach: &MachineWithStack) -> Value {
    let value =
        mach.functionPc.clone() +
        mach.functionIdx.clone() * FpVar::constant(Fr::from(1 << 32)) +
        mach.moduleIdx.clone() * FpVar::constant(Fr::from(1 << 64));
    Value {
        value,
        ty: FpVar::constant(Fr::from(INTERNAL_TYPE_REF)),
    }
}

fn create_i32_value(value: FpVar<Fr>) -> Value {
    enforce_i32(value.clone());
    Value { value, ty: FpVar::constant(Fr::from(I32_TYPE)) }
}

pub fn execute_call(params: &Params, mach: &MachineWithStack, frame: &StackFrame, inst: &Instruction) -> MachineWithStack {
    let mut mach = mach.clone();
    mach.valueStack.push(hash_value(params, &create_return_value(&mach)));
    mach.frameStack.peek().enforce_equal(&hash_stack_frame(params, frame)).unwrap();
    mach.valueStack.push(hash_value(params, &create_i32_value(frame.callerModule.clone())));
    mach.valueStack.push(hash_value(params, &create_i32_value(frame.callerModuleInternals.clone())));
    mach.functionIdx = inst.argumentData.clone();
    enforce_i32(inst.argumentData.clone());
    mach.functionPc = FpVar::constant(Fr::from(0));
    mach
}

struct InstCallHint {
    frame: StackFrame,

}

impl InstHint for InstReturnHint {
    fn execute(&self, params: &Params, mach: &MachineWithStack) -> (MachineWithStack, MachineWithStack) {
        let mut mach = mach.clone();
        mach.frameStack.push(hash_stack_frame(&params, &self.frame));
        let before = mach.clone();
        let after = execute_return(params, &mach, &self.frame);
        (before, after)
    }
}

impl InstReturnHint {
    pub fn default() -> Self {
        InstReturnHint { frame: StackFrame::default() }
    }
}


pub fn execute_cross_module_call(params: &Params, mach: &MachineWithStack, inst: &Instruction, mole: &Module) -> MachineWithStack {
    let mut mach = mach.clone();
    mach.valueStack.push(hash_value(params, &create_return_value(&mach)));
    mach.valueStack.push(hash_value(params, &create_i32_value(mach.moduleIdx.clone())));
    mach.valueStack.push(hash_value(params, &create_i32_value(mole.internalsOffset.clone())));
    let data = inst.argumentData.to_bits_le().unwrap();
    mach.functionIdx = Boolean::le_bits_to_fp_var(&data[0..32]).unwrap();
    mach.moduleIdx = Boolean::le_bits_to_fp_var(&data[32..64]).unwrap();
    mach.functionPc = FpVar::constant(Fr::from(0));
    mach
}

pub fn execute_local_get(cs: ConstraintSystemRef<Fr>, params: &Params, mach: &MachineWithStack, inst: &Instruction, proof: &Proof, var: &ValueHint, frame: &StackFrame) -> MachineWithStack {
    let mut mach = mach.clone();
    let var = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(var.hash(params))).unwrap());
    let (root, idx) = make_path(cs.clone(), 20, params, var.clone(), proof);
    mach.frameStack.peek().enforce_equal(&hash_stack_frame(params, frame)).unwrap();
    mach.valid = mach.valid.and(&root.is_eq(&frame.localsMerkleRoot).unwrap()).unwrap();
    mach.valid = mach.valid.and(&idx.is_eq(&inst.argumentData).unwrap()).unwrap();
    mach.valueStack.push(var);
    mach
}

pub fn execute_local_set(cs: ConstraintSystemRef<Fr>, params: &Params, mach: &MachineWithStack, inst: &Instruction, proof: &Proof, old_var: &ValueHint, frame: &StackFrame) -> MachineWithStack {
    let mut mach = mach.clone();
    let old_var = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(old_var.hash(params))).unwrap());
    let var = mach.valueStack.pop();
    let (root, idx) = make_path(cs.clone(), 20, params, old_var.clone(), proof);
    mach.frameStack.pop().enforce_equal(&hash_stack_frame(params, frame)).unwrap();
    mach.valid = mach.valid.and(&root.is_eq(&frame.localsMerkleRoot).unwrap()).unwrap();
    mach.valid = mach.valid.and(&idx.is_eq(&inst.argumentData).unwrap()).unwrap();
    let (root2, idx2) = make_path(cs.clone(), 20, params, var.clone(), proof);
    idx2.enforce_equal(&idx).unwrap();
    let mut frame = frame.clone();
    frame.localsMerkleRoot = root2;
    mach.frameStack.push(hash_stack_frame(params, &frame));
    mach
}

pub fn execute_global_get(cs: ConstraintSystemRef<Fr>, params: &Params, mach: &MachineWithStack, inst: &Instruction, proof: &Proof, var: &ValueHint, mole: &Module) -> MachineWithStack {
    let mut mach = mach.clone();
    let var = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(var.hash(params))).unwrap());
    let (root, idx) = make_path(cs.clone(), 20, params, var.clone(), proof);
    mach.valid = mach.valid.and(&root.is_eq(&mole.globalsMerkleRoot).unwrap()).unwrap();
    mach.valid = mach.valid.and(&idx.is_eq(&inst.argumentData).unwrap()).unwrap();
    mach.valueStack.push(var);
    mach
}

pub fn execute_global_set(cs: ConstraintSystemRef<Fr>, params: &Params, mach: &MachineWithStack, inst: &Instruction, proof: &Proof, old_var: &ValueHint, mole: &Module) -> (MachineWithStack, Module) {
    let mut mach = mach.clone();
    let old_var = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(old_var.hash(params))).unwrap());
    let var = mach.valueStack.pop();
    let (root, idx) = make_path(cs.clone(), 20, params, old_var.clone(), proof);
    mach.valid = mach.valid.and(&root.is_eq(&mole.globalsMerkleRoot).unwrap()).unwrap();
    mach.valid = mach.valid.and(&idx.is_eq(&inst.argumentData).unwrap()).unwrap();
    let (root2, idx2) = make_path(cs.clone(), 20, params, var.clone(), proof);
    idx2.enforce_equal(&idx).unwrap();
    let mut mole = mole.clone();
    mole.globalsMerkleRoot = root2;
    (mach, mole)
}

pub fn execute_init_frame(cs: ConstraintSystemRef<Fr>, params: &Params, mach: &MachineWithStack, inst: &Instruction, returnPc: &ValueHint) -> MachineWithStack {
    let mut mach = mach.clone();
    let callerModuleInternals = mach.valueStack.pop();
    let callerModule = mach.valueStack.pop();
    let returnPcHash = mach.valueStack.pop();
    let returnPc = Value {
        value: FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(returnPc.value))).unwrap()),
        ty: FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(returnPc.ty))).unwrap()),
    };
    hash_value(params, &returnPc).enforce_equal(&returnPcHash).unwrap();
    let frame = StackFrame {
        callerModuleInternals,
        callerModule,
        returnPc,
        localsMerkleRoot: inst.argumentData.clone(),
    };
    mach.frameStack.push(hash_stack_frame(params, &frame));
    mach
}
*/

/*
combining all instructions...
in the end, maybe just select a valid alternative
*/
