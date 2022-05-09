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

use ark_std::UniformRand;
use ark_ff::Field;
use ark_r1cs_std::fields::FieldVar;
use ark_r1cs_std::R1CSVar;
use ark_r1cs_std::boolean::Boolean;

use crate::{VM,Transition,hash_list,hash_code};
use crate::InstructionCircuit;
use ark_r1cs_std::boolean::AllocatedBool;

fn shr_bool(a: &[Boolean<Fr>], r: usize) -> Vec<Boolean<Fr>> {
    let mut out = vec![];
    for i in 0..a.len() {
        out.push(if i+r >= 64 { Boolean::FALSE } else { a[i+r].clone() })
    }
    out
}

fn shl_bool(a: &[Boolean<Fr>], r: usize) -> Vec<Boolean<Fr>> {
    let mut out = vec![];
    for i in 0..a.len() {
        out.push(if i < r { Boolean::FALSE } else { a[i-r].clone() })
    }
    out
}

fn or_bool(a: &[Boolean<Fr>], b: &[Boolean<Fr>]) -> Vec<Boolean<Fr>> {
    let mut out = vec![];
    for i in 0..a.len() {
        out.push(a[i].clone().or(&b[i]).unwrap())
    }
    out
}

fn xor_bool(a: &[Boolean<Fr>], b: &[Boolean<Fr>]) -> Vec<Boolean<Fr>> {
    let mut out = vec![];
    for i in 0..a.len() {
        out.push(a[i].clone().xor(&b[i]).unwrap())
    }
    out
}

fn not_bool(a: &[Boolean<Fr>]) -> Vec<Boolean<Fr>> {
    let mut out = vec![];
    for i in 0..a.len() {
        out.push(a[i].clone().not())
    }
    out
}

fn and_bool(a: &[Boolean<Fr>], b: &[Boolean<Fr>]) -> Vec<Boolean<Fr>> {
    let mut out = vec![];
    for i in 0..a.len() {
        out.push(a[i].clone().and(&b[i]).unwrap())
    }
    out
}

fn xor5_bool(a: &[Boolean<Fr>], b: &[Boolean<Fr>], c: &[Boolean<Fr>], d: &[Boolean<Fr>], e: &[Boolean<Fr>]) -> Vec<Boolean<Fr>> {
    let mut out = vec![];
    for i in 0..a.len() {
        out.push(a[i].clone().xor(&b[i]).unwrap().xor(&c[i]).unwrap().xor(&d[i]).unwrap().xor(&e[i]).unwrap())
    }
    out
}

fn perm_d(a: &Vec<Boolean<Fr>>, b: &Vec<Boolean<Fr>>, shl: usize, shr: usize) -> Vec<Boolean<Fr>> {
    // d = b ^ (a<<shl | a>>shr)

    let aux0 = shr_bool(a, shr);
    let aux1 = shl_bool(a, shl);

    let aux2 = or_bool(&aux0, &aux1);
    xor_bool(&b, &aux2)
}

fn theta(inp: Vec<Boolean<Fr>>) -> Vec<Boolean<Fr>> {
    let mut r = vec![vec![]; 25];

    // println!("here {}", inp.len());

    let c0 = xor5_bool(&inp[0..64], &inp[5*64..6*64], &inp[10*64..11*64], &inp[15*64..16*64], &inp[20*64..21*64]);
    let c1 = xor5_bool(&inp[64..2*64], &inp[6*64..7*64], &inp[11*64..12*64], &inp[16*64..17*64], &inp[21*64..22*64]);
    let c2 = xor5_bool(&inp[2*64..3*64], &inp[7*64..8*64], &inp[12*64..13*64], &inp[17*64..18*64], &inp[22*64..23*64]);
    let c3 = xor5_bool(&inp[3*64..4*64], &inp[8*64..9*64], &inp[13*64..14*64], &inp[18*64..19*64], &inp[23*64..24*64]);
    let c4 = xor5_bool(&inp[4*64..5*64], &inp[9*64..10*64], &inp[14*64..15*64], &inp[19*64..20*64], &inp[24*64..25*64]);

    // d = c4 ^ (c1<<1 | c1>>(64-1))
    let d0 = perm_d(&c1, &c4, 1, 64-1);

    // r[0] = a[0] ^ d
    r[0] = xor_bool(&inp[0..64], &d0);
    r[5] = xor_bool(&inp[5*64..6*64], &d0);
    r[10] = xor_bool(&inp[10*64..11*64], &d0);
    r[15] = xor_bool(&inp[15*64..16*64], &d0);
    r[20] = xor_bool(&inp[20*64..21*64], &d0);

    // d = c0 ^ (c2<<1 | c2>>(64-1))
    let d1 = perm_d(&c2, &c0, 1, 64-1);
    r[1] = xor_bool(&inp[1*64..2*64], &d1);
    r[6] = xor_bool(&inp[6*64..7*64], &d1);
    r[11] = xor_bool(&inp[11*64..12*64], &d1);
    r[16] = xor_bool(&inp[16*64..17*64], &d1);
    r[21] = xor_bool(&inp[21*64..22*64], &d1);

    let d2 = perm_d(&c3, &c1, 1, 64-1);
    r[2] = xor_bool(&inp[2*64..3*64], &d2);
    r[7] = xor_bool(&inp[7*64..8*64], &d2);
    r[12] = xor_bool(&inp[12*64..13*64], &d2);
    r[17] = xor_bool(&inp[17*64..18*64], &d2);
    r[22] = xor_bool(&inp[22*64..23*64], &d2);

    let d3 = perm_d(&c4, &c2, 1, 64-1);
    r[3] = xor_bool(&inp[3*64..4*64], &d3);
    r[8] = xor_bool(&inp[8*64..9*64], &d3);
    r[13] = xor_bool(&inp[13*64..14*64], &d3);
    r[18] = xor_bool(&inp[18*64..19*64], &d3);
    r[23] = xor_bool(&inp[23*64..24*64], &d3);

    let d4 = perm_d(&c0, &c3, 1, 64-1);
    r[4] = xor_bool(&inp[4*64..5*64], &d4);
    r[9] = xor_bool(&inp[9*64..10*64], &d4);
    r[14] = xor_bool(&inp[14*64..15*64], &d4);
    r[19] = xor_bool(&inp[19*64..20*64], &d4);
    r[24] = xor_bool(&inp[24*64..25*64], &d4);

    let mut out = vec![];

    for i in 0..25 {
        for j in 0..64 {
            out.push(r[i][j].clone())
        }
    }
    // print_bytes(&out);
    out
}

fn step_rho_pi(a: &[Boolean<Fr>], shl: usize, shr: usize) -> Vec<Boolean<Fr>> {
    // out = a<<shl|a>>shr
    let aux0 = shr_bool(a, shr);
    let aux1 = shl_bool(a, shl);

    or_bool(&aux0, &aux1)

}

fn rho_pi(inp: Vec<Boolean<Fr>>) -> Vec<Boolean<Fr>> {
    let mut r = vec![vec![]; 25];

    r[10] = step_rho_pi(&inp[1*64..2*64], 1, 64-1);
    r[7] = step_rho_pi(&inp[10*64..11*64], 3, 64-3);
    r[11] = step_rho_pi(&inp[7*64..8*64], 6, 64-6);
    r[17] = step_rho_pi(&inp[11*64..12*64], 10, 64-10);
    r[18] = step_rho_pi(&inp[17*64..18*64], 15, 64-15);

    r[3] = step_rho_pi(&inp[18*64..19*64], 21, 64-21);
    r[5] = step_rho_pi(&inp[3*64..4*64], 28, 64-28);
    r[16] = step_rho_pi(&inp[5*64..6*64], 36, 64-36);
    r[8] = step_rho_pi(&inp[16*64..17*64], 45, 64-45);
    r[21] = step_rho_pi(&inp[8*64..9*64], 55, 64-55);

    r[24] = step_rho_pi(&inp[21*64..22*64], 2, 64-2);
    r[4] = step_rho_pi(&inp[24*64..25*64], 14, 64-14);
    r[15] = step_rho_pi(&inp[4*64..5*64], 27, 64-27);
    r[23] = step_rho_pi(&inp[15*64..16*64], 41, 64-41);
    r[19] = step_rho_pi(&inp[23*64..24*64], 56, 64-56);

    r[13] = step_rho_pi(&inp[19*64..20*64], 8, 64-8);
    r[12] = step_rho_pi(&inp[13*64..14*64], 25, 64-25);
    r[2] = step_rho_pi(&inp[12*64..13*64], 43, 64-43);
    r[20] = step_rho_pi(&inp[2*64..3*64], 62, 64-62);
    r[14] = step_rho_pi(&inp[20*64..21*64], 18, 64-18);

    r[22] = step_rho_pi(&inp[14*64..15*64], 39, 64-39);
    r[9] = step_rho_pi(&inp[22*64..23*64], 61, 64-61);
    r[6] = step_rho_pi(&inp[9*64..10*64], 20, 64-20);
    r[1] = step_rho_pi(&inp[6*64..7*64], 44, 64-44);

    r[0] = inp[0..64].to_vec();

    let mut out = vec![];

    for i in 0..25 {
        for j in 0..64 {
            out.push(r[i][j].clone())
        }
    }
    // print_bytes(&out);
    out
}

fn step_chi(a: &[Boolean<Fr>], b: &[Boolean<Fr>], c: &[Boolean<Fr>]) -> Vec<Boolean<Fr>> {
    let b_xor = not_bool(b);
    let bc = and_bool(&b_xor, c);
    xor_bool(a, &bc)
}

fn chi(inp: Vec<Boolean<Fr>>) -> Vec<Boolean<Fr>> {
    let mut r = vec![vec![]; 25];

    r[0] = step_chi(&inp[0*64..1*64], &inp[1*64..2*64], &inp[2*64..3*64]);
    r[1] = step_chi(&inp[1*64..2*64], &inp[2*64..3*64], &inp[3*64..4*64]);
    r[2] = step_chi(&inp[2*64..3*64], &inp[3*64..4*64], &inp[4*64..5*64]);
    r[3] = step_chi(&inp[3*64..4*64], &inp[4*64..5*64], &inp[0*64..1*64]);
    r[4] = step_chi(&inp[4*64..5*64], &inp[0*64..1*64], &inp[1*64..2*64]);

    r[5] = step_chi(&inp[5*64..6*64], &inp[6*64..7*64], &inp[7*64..8*64]);
    r[6] = step_chi(&inp[6*64..7*64], &inp[7*64..8*64], &inp[8*64..9*64]);
    r[7] = step_chi(&inp[7*64..8*64], &inp[8*64..9*64], &inp[9*64..10*64]);
    r[8] = step_chi(&inp[8*64..9*64], &inp[9*64..10*64], &inp[5*64..6*64]);
    r[9] = step_chi(&inp[9*64..10*64], &inp[5*64..6*64], &inp[6*64..7*64]);

    r[10] = step_chi(&inp[10*64..11*64], &inp[11*64..12*64], &inp[12*64..13*64]);
    r[11] = step_chi(&inp[11*64..12*64], &inp[12*64..13*64], &inp[13*64..14*64]);
    r[12] = step_chi(&inp[12*64..13*64], &inp[13*64..14*64], &inp[14*64..15*64]);
    r[13] = step_chi(&inp[13*64..14*64], &inp[14*64..15*64], &inp[10*64..11*64]);
    r[14] = step_chi(&inp[14*64..15*64], &inp[10*64..11*64], &inp[11*64..12*64]);

    r[15] = step_chi(&inp[15*64..16*64], &inp[16*64..17*64], &inp[17*64..18*64]);
    r[16] = step_chi(&inp[16*64..17*64], &inp[17*64..18*64], &inp[18*64..19*64]);
    r[17] = step_chi(&inp[17*64..18*64], &inp[18*64..19*64], &inp[19*64..20*64]);
    r[18] = step_chi(&inp[18*64..19*64], &inp[19*64..20*64], &inp[15*64..16*64]);
    r[19] = step_chi(&inp[19*64..20*64], &inp[15*64..16*64], &inp[16*64..17*64]);

    r[20] = step_chi(&inp[20*64..21*64], &inp[21*64..22*64], &inp[22*64..23*64]);
    r[21] = step_chi(&inp[21*64..22*64], &inp[22*64..23*64], &inp[23*64..24*64]);
    r[22] = step_chi(&inp[22*64..23*64], &inp[23*64..24*64], &inp[24*64..25*64]);
    r[23] = step_chi(&inp[23*64..24*64], &inp[24*64..25*64], &inp[20*64..21*64]);
    r[24] = step_chi(&inp[24*64..25*64], &inp[20*64..21*64], &inp[21*64..22*64]);

    let mut out = vec![];
    for i in 0..25 {
        for j in 0..64 {
            out.push(r[i][j].clone())
        }
    }
    // print_bytes(&out);
    out
}

fn iota(inp: Vec<Boolean<Fr>>, r: usize) -> Vec<Boolean<Fr>> {

    let rc_arr = vec![
        0x0000000000000001u64, 0x0000000000008082, 0x800000000000808A,
        0x8000000080008000, 0x000000000000808B, 0x0000000080000001,
        0x8000000080008081, 0x8000000000008009, 0x000000000000008A,
        0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
        0x000000008000808B, 0x800000000000008B, 0x8000000000008089,
        0x8000000000008003, 0x8000000000008002, 0x8000000000000080,
        0x000000000000800A, 0x800000008000000A, 0x8000000080008081,
        0x8000000000008080, 0x0000000080000001, 0x8000000080008008
    ];

    let mut rc = vec![];
    for i in 0..64 {
        rc.push(Boolean::constant(((rc_arr[r] >> i) & 1) == 1));
    }

    let mut res = xor_bool(&inp[0..64], &rc);
    for i in 64..25*64 {
        res.push(inp[i].clone())
    }
    // println!("iota {}", res.len());
    res
}

fn pad(inp: Vec<Boolean<Fr>>) -> Vec<Boolean<Fr>> {
    let blockSize = 136*8;

    let mut out2 = vec![];

    for el in inp.clone() {
        out2.push(el)
    }

    let domain = 0x01;
    for i in 0..8 {
        out2.push(Boolean::constant(((domain >> i) & 1) == 1))
    }

    for _i in 8+inp.len() .. blockSize {
        out2.push(Boolean::FALSE)
    }

    let mut last_mask = vec![];
    for i in 0..8 {
        last_mask.push(Boolean::constant(((0x80 >> i) & 1) == 1));
    }

    let last = or_bool(&last_mask, &out2[blockSize-8 .. blockSize]);

    let mut out = vec![];

    for i in 0..blockSize-8 {
        out.push(out2[i].clone())
    }

    for i in 0..8 {
        out.push(last[i].clone())
    }

    out
}

/*
A:0, b:0: true
A:1, b:0: true
A:0, b:1: false
A:1, b:1: true
*/
fn correct_sel(sel: &[Boolean<Fr>]) {
    // Sequence of booleans becomes false at some point?
    for i in 0..sel.len()-1 {
        sel[i].or(&sel[i+1].not()).unwrap().enforce_equal(&Boolean::TRUE).unwrap();
    }
    sel[sel.len()-1].enforce_equal(&Boolean::FALSE).unwrap();
}

/*
A:0, b:0: true
A:1, b:0: false
A:0, b:1: true
A:1, b:1: true
*/
fn correct_sel_inv(sel: &[Boolean<Fr>]) {
    // Sequence of booleans becomes false at some point?
    for i in 0..sel.len()-1 {
        sel[i+1].or(&sel[i].not()).unwrap().enforce_equal(&Boolean::TRUE).unwrap();
    }
    sel[sel.len()-1].enforce_equal(&Boolean::TRUE).unwrap();
}

// select bytes
fn pad_var(inp: &[Boolean<Fr>], sel: &[Boolean<Fr>]) -> Vec<Boolean<Fr>> {

    correct_sel(sel);

    let blockSize = 136*8;

    let mut out2 = vec![];

    for i in 0..136 {
        if i == 0 {
            out2.push(sel[i].and(&inp[i*8]).unwrap().or(&sel[i].not()).unwrap());
        } else {
            out2.push(sel[i].and(&inp[i*8]).unwrap().or(&sel[i-1].and(&sel[i].not()).unwrap()).unwrap());
        }
        for j in 1..8 {
            out2.push(sel[i].and(&inp[i*8+j]).unwrap())
        }
    }

    let mut last_mask = vec![];
    for i in 0..8 {
        last_mask.push(Boolean::constant(((0x80 >> i) & 1) == 1));
    }

    let last = or_bool(&last_mask, &out2[blockSize-8 .. blockSize]);

    let mut out = vec![];

    for i in 0..blockSize-8 {
        out.push(out2[i].clone())
    }

    for i in 0..8 {
        out.push(last[i].clone())
    }

    out
}

fn keccacf_round(inp: Vec<Boolean<Fr>>, r: usize) -> Vec<Boolean<Fr>> {
    let r1 = theta(inp);
    let r2 = rho_pi(r1);
    let r3 = chi(r2);
    iota(r3, r)
}

fn keccakf(inp: Vec<Boolean<Fr>>) -> Vec<Boolean<Fr>> {
    let mut res = inp;
    for i in 0..24 {
        res = keccacf_round(res, i);
    }
    res
}

fn absorb(block: &[Boolean<Fr>], s: Vec<Boolean<Fr>>) -> Vec<Boolean<Fr>> {
    let blockSizeBytes = 136;

    let mut inp = xor_bool(&block, &s[0..8*blockSizeBytes]);
    // println!("first {}, block {}", inp.len(), block.len());

    for i in blockSizeBytes*8 .. 25*64 {
        inp.push(s[i].clone())
    }
    // println!("first {}, block {}", inp.len(), block.len());

    print_bytes(&inp);


    keccakf(inp)
}

fn finalize(inp: Vec<Boolean<Fr>>, s: Vec<Boolean<Fr>>) -> Vec<Boolean<Fr>> {
    let block = pad(inp);
    absorb(&block, s)
}

fn finalize_var(cs: ConstraintSystemRef<Fr>, inp: Vec<Boolean<Fr>>, sel: Vec<Boolean<Fr>>) -> Vec<Boolean<Fr>> {
    let block = pad_var(&inp, &sel);
    let mut init = vec![];
    for _i in 0..1600 {
        let bool_var = Boolean::from(AllocatedBool::<Fr>::new_witness(cs.clone(), || Ok(false)).unwrap());
        init.push(bool_var)
    }
    absorb(&block, init)
}

fn finalize_double(cs: ConstraintSystemRef<Fr>, inp: Vec<Boolean<Fr>>, sel: Vec<Boolean<Fr>>) -> Vec<Boolean<Fr>> {
    let block1 = &inp[0..136*8];
    let block2 = pad_var(&inp[136*8..136*8*2], &sel);
    let mut init = vec![];
    for _i in 0..1600 {
        let bool_var = Boolean::from(AllocatedBool::<Fr>::new_witness(cs.clone(), || Ok(false)).unwrap());
        init.push(bool_var)
    }
    let s = absorb(block1, init);
    absorb(&block2, s)
}

fn count(sel: &[Boolean<Fr>]) -> FpVar<Fr> {
    let mut acc = FpVar::Constant(Fr::from(0));
    for el in sel.iter() {
        let v : FpVar<Fr> = From::from(el.clone());
        acc = acc + v;
    }
    acc
}

fn count_bytes(sel: &Vec<Boolean<Fr>>, blocks: &Vec<Boolean<Fr>>) -> FpVar<Fr> {
    let a = count(sel);
    let b = count(&blocks[0..blocks.len()-1]);
    let block_size = FpVar::constant(Fr::from(136));
    a + b * block_size
}

fn finalize_blocks(cs: ConstraintSystemRef<Fr>, inp: Vec<Boolean<Fr>>, sel: Vec<Boolean<Fr>>, blocks: Vec<Boolean<Fr>>) -> Vec<Boolean<Fr>> {
    correct_sel_inv(&blocks);
    let mut init = vec![];
    for _i in 0..1600 {
        let bool_var = Boolean::from(AllocatedBool::<Fr>::new_witness(cs.clone(), || Ok(false)).unwrap());
        init.push(bool_var)
    }
    let mut s = init.clone();
    
    for i in 0..blocks.len() - 1 {
        let aux = absorb(&inp[i*136*8 .. (i+1)*136*8], s);
        s = vec![];
        // select block
        for j in 0..1600 {
            s.push(blocks[i].select(&aux[j], &init[j]).unwrap());
        }
    }
    let last_block = pad_var(&inp[136*8*(blocks.len()-1)..136*8*blocks.len()], &sel);
    absorb(&last_block, s)
}

#[derive(Debug, Clone)]
pub struct TestCircuit {
    pub steps: usize,
}

impl ConstraintSynthesizer<Fr> for TestCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        for _i in 0..self.steps {
            let mut inp = vec![];
            for _j in 0..136*8 {
                let bool_var = Boolean::from(AllocatedBool::<Fr>::new_witness(cs.clone(), || Ok(false)).unwrap());
                inp.push(bool_var)
            }
            let mut init = vec![];
            for _j in 0..1600 {
                let bool_var = Boolean::from(AllocatedBool::<Fr>::new_witness(cs.clone(), || Ok(false)).unwrap());
                init.push(bool_var)
            }
            finalize(inp, init);
        }
        // println!("num constraints {}, valid {}", cs.num_constraints(), cs.is_satisfied().unwrap());
        println!("num constraints {}", cs.num_constraints());
        Ok(())
    }
}

fn reverse<T: Clone>(a: &[T]) -> Vec<T> {
    let mut res : Vec<T> = vec![];
    for el in a.iter().rev() {
        res.push(el.clone())
    }
    res
}

fn print_bytes(v: &[Boolean<Fr>]) {
    let mut res = "".to_string();
    for i in 0..200 {
        let mut h1 = 0;
        for j in 0..4 {
            let x = if v[i*8+3-j].value().unwrap() { 1 } else { 0 };
            h1 = 2*h1 + x;
        }
        let mut h2 = 0;
        for j in 0..4 {
            let x = if v[i*8+4+3-j].value().unwrap() { 1 } else { 0 };
            h2 = 2*h2 + x;
        }
        res = format!("{}{:x}{:x}", res, h2, h1)
    }
    println!("{}", res)
}

pub fn test() {
    use ark_std::test_rng;
    use crate::InnerSNARK;
    use ark_crypto_primitives::CircuitSpecificSetupSNARK;
    use ark_crypto_primitives::SNARK;
    let cs_sys = ConstraintSystem::<Fr>::new();
    let cs = ConstraintSystemRef::new(cs_sys);

    let mut inp = vec![];
    for i in 0..136*8*3 {
        let b = (i % 8) == 0;
        let bool_var = Boolean::from(AllocatedBool::<Fr>::new_witness(cs.clone(), || Ok(b)).unwrap());
        inp.push(bool_var)
    }
    let mut sel = vec![];
    for i in 0..136 {
        let res = if i < 10 { true } else { false };
        let bool_var = Boolean::from(AllocatedBool::<Fr>::new_witness(cs.clone(), || Ok(res)).unwrap());
        sel.push(bool_var)
    }
    let mut blocks = vec![];
    blocks.push(Boolean::from(AllocatedBool::<Fr>::new_witness(cs.clone(), || Ok(false)).unwrap()));
    blocks.push(Boolean::from(AllocatedBool::<Fr>::new_witness(cs.clone(), || Ok(true)).unwrap()));
    blocks.push(Boolean::from(AllocatedBool::<Fr>::new_witness(cs.clone(), || Ok(true)).unwrap()));
    let res = count_bytes(&sel, &blocks);
    let bits = finalize_blocks(cs.clone(), inp, sel, blocks);
    print_bytes(&bits);

    // let res = Boolean::le_bits_to_fp_var(&reverse(&bits[0..256])).unwrap();
    println!("num constraints {} satified {}, res {}", cs.is_satisfied().unwrap(), cs.num_constraints(), res.value().unwrap());
    // println!("num constraints {} {}", cs.num_constraints(), cs.is_satisfied().unwrap());

    /*
    let circuit = TestCircuit {
        steps: 181,
    };
    let mut rng = test_rng();
    println!("Setting up circuit");
    let (pk, vk) = InnerSNARK::setup(circuit.clone(), &mut rng).unwrap();
    println!("Testing prove");
    let proof = InnerSNARK::prove(&pk, circuit.clone(), &mut rng).unwrap();
    */
}
