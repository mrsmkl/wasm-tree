use parity_wasm::elements::Instruction::*;
use parity_wasm::elements::*;
use std::fs::File;
use std::io::Read;
use ark_crypto_primitives::crh::poseidon::{ /* TwoToOneCRH, */ CRH};
use ark_crypto_primitives::crh::poseidon::constraints::{CRHGadget, CRHParametersVar};
use ark_sponge::poseidon::PoseidonParameters;
// use ark_bls12_377::Fr;
use ark_std::UniformRand;
use ark_std::Zero;
use ark_crypto_primitives::CRHScheme;
use ark_relations::r1cs::ConstraintSystem;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::{
    fields::fp::{AllocatedFp, FpVar},
    R1CSVar,
};
use ark_crypto_primitives::CRHSchemeGadget;
use ark_relations::r1cs::ConstraintSystemRef;
use ark_relations::r1cs::SynthesisError;
use ark_relations::r1cs::ConstraintSynthesizer;
use ark_relations::r1cs::Field;
use ark_ff::PrimeField;
use ark_sponge::Absorb;

use ark_mnt4_298::{
    constraints::PairingVar as MNT4PairingVar, Fr, MNT4_298 as MNT4PairingEngine,
};
use ark_mnt6_298::Fr as MNT6Fr;
use ark_groth16::Groth16;
use ark_groth16::constraints::Groth16VerifierGadget;
use ark_std::test_rng;

trait HashField : Absorb + PrimeField {
}

fn get_file(fname: String) -> Vec<u8> {
    let mut file = File::open(&fname).unwrap();
    let mut buffer = Vec::<u8>::new();
    file.read_to_end(&mut buffer).unwrap();
    buffer
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
enum CodeTree {
    CLoop (Vec<CodeTree>),
    CConst (u32),
    CAdd,
    CSub,
    CGt,
    CEnd,
    CBreakIf (u32),
    CSetLocal (u32),
    CGetLocal (u32),
}

use CodeTree::*;

fn block_start(op: &Instruction) -> bool {
    match &*op {
        Loop(_) => true,
        _ => false,
    }
}

fn find_end(code: &[Instruction]) -> &[Instruction] {
    let mut depth = 0;
    for (i, op) in code.iter().enumerate() {
        // println!("scanning {}", op);
        if block_start(op) {
            depth = depth + 1;
        } else if *op == End && depth == 0{
            return &code[i+1..];
        } else if *op == End {
            depth = depth - 1
        }
    }
    panic!("Cannot find end");
}

fn process_code(code: &[Instruction]) -> Vec<CodeTree> {
    let mut res = vec![];
    for (i, op) in code.iter().enumerate() {
        // println!("op {}", op);
        match &*op {
            Loop(_) => {
                let cont = find_end(&code[i+1..]);
                res.push(CLoop(process_code(cont)))
            }
            I32Add => res.push(CAdd),
            I32Sub => res.push(CSub),
            I32GtU => res.push(CGt),
            GetLocal(x) => res.push(CGetLocal(*x as u32)),
            SetLocal(x) => res.push(CSetLocal(*x as u32)),
            I32Const(x) => res.push(CConst(*x as u32)),
            BrIf(x) => res.push(CBreakIf(*x as u32)),
            End => {
                res.push(CEnd);
                return res;
            }
            _ => println!("Unknown op"),
        }
    }
    res
}

fn hash_list(params: &PoseidonParameters<Fr>, lst: &[Fr]) -> Fr {
    let mut res = Fr::zero();
    for elem in lst.iter() {
        let mut inputs = vec![];
        inputs.push(elem.clone());
        inputs.push(res);
        res = CRH::<Fr>::evaluate(&params, inputs).unwrap();
    }
    res
}

fn hash_code(params: &PoseidonParameters<Fr>, code: &Vec<CodeTree>) -> Fr {
    let mut res = Fr::zero();
    for op in code.iter().rev() {
        // println!("hashing {:?}", op);
        match &*op {
            CAdd => {
                let mut inputs = vec![];
                inputs.push(Fr::from(1));
                inputs.push(res);
                res = CRH::<Fr>::evaluate(&params, inputs).unwrap();
            }
            CSub => {
                let mut inputs = vec![];
                inputs.push(Fr::from(2));
                inputs.push(res);
                res = CRH::<Fr>::evaluate(&params, inputs).unwrap();
            }
            CGt => {
                let mut inputs = vec![];
                inputs.push(Fr::from(3));
                inputs.push(res);
                res = CRH::<Fr>::evaluate(&params, inputs).unwrap();
            }
            CEnd => {
                let mut inputs = vec![];
                inputs.push(Fr::from(9));
                inputs.push(res);
                res = CRH::<Fr>::evaluate(&params, inputs).unwrap();
            }
            CGetLocal(x) => {
                let mut inputs = vec![];
                inputs.push(Fr::from(4));
                inputs.push(Fr::from(*x));
                inputs.push(res);
                res = CRH::<Fr>::evaluate(&params, inputs).unwrap();
            }
            CSetLocal(x) => {
                let mut inputs = vec![];
                inputs.push(Fr::from(5));
                inputs.push(Fr::from(*x));
                inputs.push(res);
                res = CRH::<Fr>::evaluate(&params, inputs).unwrap();
            }
            CConst(x) => {
                let mut inputs = vec![];
                inputs.push(Fr::from(6));
                inputs.push(Fr::from(*x));
                inputs.push(res);
                res = CRH::<Fr>::evaluate(&params, inputs).unwrap();
            }
            CBreakIf(x) => {
                let mut inputs = vec![];
                inputs.push(Fr::from(7));
                inputs.push(Fr::from(*x));
                inputs.push(res);
                res = CRH::<Fr>::evaluate(&params, inputs).unwrap();
            }
            CLoop(cont) => {
                let mut inputs = vec![];
                inputs.push(Fr::from(8));
                inputs.push(hash_code(&params, cont));
                inputs.push(res);
                res = CRH::<Fr>::evaluate(&params, inputs).unwrap();
            }
        }
    }
    res
}

fn generate_hash() -> PoseidonParameters<Fr> {
    let mut test_rng = ark_std::test_rng();

    // TODO: The following way of generating the MDS matrix is incorrect
    // and is only for test purposes.

    let mut mds = vec![vec![]; 3];
    for i in 0..3 {
        for _ in 0..3 {
            mds[i].push(Fr::rand(&mut test_rng));
        }
    }

    let mut ark = vec![vec![]; 8 + 24];
    for i in 0..8 + 24 {
        for _ in 0..3 {
            ark[i].push(Fr::rand(&mut test_rng));
        }
    }

    let mut test_a = Vec::new();
    let mut test_b = Vec::new();
    for _ in 0..3 {
        test_a.push(Fr::rand(&mut test_rng));
        test_b.push(Fr::rand(&mut test_rng));
    }
    PoseidonParameters::<Fr>::new(8, 24, 31, mds, ark)

}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
enum ControlFrame {
    LoopFrame(Vec<CodeTree>, Vec<CodeTree>)
}

impl ControlFrame {
    fn hash(&self, params: &PoseidonParameters<Fr>) -> Fr {
        match self {
            ControlFrame::LoopFrame(a, b) => {
                let mut inputs = vec![];
                inputs.push(Fr::from(1));
                inputs.push(hash_code(&params, &a));
                inputs.push(hash_code(&params, &b));
                CRH::<Fr>::evaluate(&params, inputs).unwrap()
            }
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
struct VM {
    pub expr_stack : Vec<u32>,
    pub locals : Vec<u32>,
    pub control_stack: Vec<ControlFrame>,
    pub pc: Vec<CodeTree>,
}

#[derive(Debug, Clone)]
struct AddCircuit {
    before: VM,
    after: VM,
    params: PoseidonParameters<Fr>,
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
        let locals_hash = hash_list(&self.params, &before.locals.iter().map(|a| Fr::from(*a)).collect::<Vec<Fr>>());
        let control_hash = hash_list(&self.params, &before.control_stack.iter().map(|a| a.hash(&self.params)).collect::<Vec<Fr>>());

        let p1 = before.expr_stack[elen - 1];
        let p2 = before.expr_stack[elen - 2];
    
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
        println!("pc hash {}", hash_pc_gadget.value().unwrap());
    
        let mut inputs_stack_before2 = Vec::new();
        inputs_stack_before2.push(var_b.clone());
        inputs_stack_before2.push(FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(stack_hash)).unwrap(),
        ));
        let hash_stack_before2_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs_stack_before2).unwrap();
    
        println!("stack before2 {}", hash_list(&self.params, &before.expr_stack[..elen-1].iter().map(|a| Fr::from(*a)).collect::<Vec<Fr>>()));
        println!("stack before2 {}", hash_stack_before2_gadget.value().unwrap());
    
        let mut inputs_stack_before = Vec::new();
        inputs_stack_before.push(var_a.clone());
        inputs_stack_before.push(hash_stack_before2_gadget);
        let hash_stack_before_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs_stack_before).unwrap();
    
        println!("stack before {}", hash_list(&self.params, &before.expr_stack.iter().map(|a| Fr::from(*a)).collect::<Vec<Fr>>()));
        println!("stack before {}", hash_stack_before_gadget.value().unwrap());
    
        let mut inputs_stack_after = Vec::new();
        inputs_stack_after.push(var_a.clone() + var_b.clone());
        inputs_stack_after.push(FpVar::Var(
            AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(stack_hash)).unwrap(),
        ));
        let hash_stack_after_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs_stack_after).unwrap();
    
        println!("stack after {}", hash_list(&self.params, &after.expr_stack.iter().map(|a| Fr::from(*a)).collect::<Vec<Fr>>()));
        println!("stack after {}", hash_stack_after_gadget.value().unwrap());
    
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
    
        println!("Made circuit");
        println!("before {}, after {}", before.hash(&self.params), after.hash(&self.params));
        println!("before {}, after {}", hash_vm_before_gadget.value().unwrap(), hash_vm_after_gadget.value().unwrap());

        Ok(())
    }
}

impl VM {
    fn new(code: Vec<CodeTree>) -> Self {
        VM {
            pc: code,
            expr_stack: vec![],
            control_stack: vec![],
            locals: vec![0; 10],
        }
    }
    fn hash(&self, params: &PoseidonParameters<Fr>) -> Fr {
        let mut inputs = vec![];
        inputs.push(hash_code(&params, &self.pc));
        inputs.push(hash_list(&params, &self.expr_stack.iter().map(|a| Fr::from(*a)).collect::<Vec<Fr>>()));
        inputs.push(hash_list(&params, &self.locals.iter().map(|a| Fr::from(*a)).collect::<Vec<Fr>>()));
        inputs.push(hash_list(&params, &self.control_stack.iter().map(|a| a.hash(&params)).collect::<Vec<Fr>>()));
        CRH::<Fr>::evaluate(&params, inputs).unwrap()
    }

    fn incr_pc(&mut self) {
        self.pc = self.pc[1..].iter().map(|a| a.clone()).collect::<Vec<CodeTree>>();
    }

    fn step(&mut self, params: &PoseidonParameters<Fr>, adds : &mut Vec<AddCircuit>) {
        if self.pc.len() == 0 {
            return
        }
        let elen = self.expr_stack.len();
        let clen = self.control_stack.len();
        match &self.pc[0] {
            CAdd => {
                let before = self.clone();
                let p1 = self.expr_stack[elen - 1];
                let p2 = self.expr_stack[elen - 2];
                self.expr_stack[elen - 2] = p1 + p2;
                self.expr_stack.pop();
                self.incr_pc();
                let after = self.clone();
                adds.push(AddCircuit{
                    before,
                    after,
                    params: params.clone(),
                })
            }
            CSub => {
                let p1 = self.expr_stack[elen - 1];
                let p2 = self.expr_stack[elen - 2];
                self.expr_stack[elen - 2] = p2 - p1;
                self.expr_stack.pop();
                self.incr_pc()
            }
            CGt => {
                let p1 = self.expr_stack[elen - 1];
                let p2 = self.expr_stack[elen - 2];
                let res = if p1 < p2 { 1 } else { 0 };
                self.expr_stack[elen - 2] = res;
                self.expr_stack.pop();
                self.incr_pc()
            }
            CConst(a) => {
                self.expr_stack.push(*a);
                self.incr_pc()
            }
            CGetLocal(a) => {
                self.expr_stack.push(self.locals[*a as usize]);
                self.incr_pc()
            }
            CSetLocal(a) => {
                self.locals[*a as usize] = self.expr_stack[elen - 1];
                self.expr_stack.pop();
                self.incr_pc()
            }
            CLoop(cont) => {
                self.control_stack.push(ControlFrame::LoopFrame(cont.clone(), self.pc.clone()));
                self.incr_pc()
            }
            CEnd => {
                if clen == 0 {
                    return
                }
                let ControlFrame::LoopFrame(c1, _) = self.control_stack[clen - 1].clone();
                self.control_stack.pop();
                self.pc = c1
            }
            CBreakIf(num) => {
                let num = *num as usize;
                let p1 = self.expr_stack[elen - 1];
                self.expr_stack.pop();
                if p1 == 1 {
                    let ControlFrame::LoopFrame(_, c1) = self.control_stack[clen - 1 - num].clone();
                    for _i in 0..=num {
                        self.control_stack.pop();
                    }
                    self.pc = c1
                } else {
                    self.incr_pc()
                }
            }
        }
    } 
}

type InnerSNARK = Groth16<MNT4PairingEngine>;
type InnerSNARKGadget = Groth16VerifierGadget<MNT4PairingEngine, MNT4PairingVar>;

fn handle_recursive_groth(a: Vec<AddCircuit>) {
    let first = a[0].clone();
    let mut rng = test_rng();
}

fn main() {

    let buffer = get_file("test.wasm".into());

    let module = parity_wasm::deserialize_buffer::<Module>(&buffer).unwrap();
    assert!(module.code_section().is_some());

    let code_section = module.code_section().unwrap(); // Part of the module with functions code

    let params = generate_hash();

    for f in code_section.bodies().iter() {
        let code = process_code(f.code().elements());
        println!("{:?}", code);
        let res = hash_code(&params, &code);
        println!("hash {}", res);
        let mut vm = VM::new(code);
        println!("vm init {}", vm.hash(&params));
        let mut adds = vec![];
        for i in 0..20 {
            vm.step(&params, &mut adds);
            println!("{}: vm hash {}", i, vm.hash(&params));
            // println!("vm state {:?}", vm);
        }
    }

}

