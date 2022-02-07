
use parity_wasm::elements::Instruction::*;
use parity_wasm::elements::*;
use std::fs::File;
use std::io::Read;

fn get_file(fname: String) -> Vec<u8> {
    let mut file = File::open(&fname).unwrap();
    let mut buffer = Vec::<u8>::new();
    file.read_to_end(&mut buffer).unwrap();
    buffer
}

enum CodeTree {
    CLoop (Vec<CodeTree>),
    CConst (u32),
    CAdd,
    CSub,
    CGt,
    CBreakIf (usize),
    CSetLocal (usize),
    CGetLocal (usize),
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
        println!("scanning {}", op);
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
        println!("op {}", op);
        match &*op {
            Loop(_) => {
                let cont = find_end(&code[i+1..]);
                res.push(CLoop(process_code(cont)))
            }
            I32Add => res.push(CAdd),
            I32Sub => res.push(CSub),
            I32GtU => res.push(CGt),
            GetLocal(x) => res.push(CGetLocal(*x as usize)),
            SetLocal(x) => res.push(CSetLocal(*x as usize)),
            I32Const(x) => res.push(CConst(*x as u32)),
            BrIf(x) => res.push(CBreakIf(*x as usize)),
            End => return res,
            _ => println!("Unknown op"),
        }
    }
    res
}

fn process_function(func: &FuncBody) {
    process_code(func.code().elements());
}

fn main() {

    let buffer = get_file("test.wasm".into());

    let module = parity_wasm::deserialize_buffer::<Module>(&buffer).unwrap();
    assert!(module.code_section().is_some());

    let code_section = module.code_section().unwrap(); // Part of the module with functions code

    for f in code_section.bodies().iter() {
        process_function(&f);
    }
}

