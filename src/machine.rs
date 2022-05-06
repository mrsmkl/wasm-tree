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

// stack: perhaps there should just be several alternatives for different length stacks ...
pub fn check_stack(
    cs: ConstraintSystemRef<Fr>,
    params : &Params,
    vars: Vec<FpVar<Fr>>,
    base: FpVar<Fr>,
) -> FpVar<Fr> {
    // compute root from base
    let mut root = base.clone();
    for el in vars.iter().rev() {
        root = poseidon_gadget(&params, vec![
            el.clone(),
            root.clone(),
        ])
    }
    root
}

