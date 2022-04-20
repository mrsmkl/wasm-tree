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

fn shr_bool(a: &[Boolean<Fr>], r: usize) -> Vec<Boolean<Fr>> {
    let mut out = vec![];
    for i in 0..a.len() {
        out.push(if i+r >= 64 { Boolean::FALSE } else { a[i-r].clone() })
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

fn or_bool(a: Vec<Boolean<Fr>>, b: Vec<Boolean<Fr>>) -> Vec<Boolean<Fr>> {
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

    let aux2 = or_bool(aux0, aux1);
    xor_bool(&b, &aux2)
}

fn perm_theta(inp: Vec<Boolean<Fr>>) -> Vec<Boolean<Fr>> {
    let mut r = vec![vec![]; 25];

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
    out
}

fn step_rho_pi(a: &[Boolean<Fr>], shl: usize, shr: usize) -> Vec<Boolean<Fr>> {
    // out = a<<shl|a>>shr
    let aux0 = shr_bool(a, shr);
    let aux1 = shl_bool(a, shl);

    or_bool(aux0, aux1)

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
    out
}

fn step_chi(a: &[Boolean<Fr>], b: &[Boolean<Fr>], c: &[Boolean<Fr>]) -> Vec<Boolean<Fr>> {
    let b_xor = not_bool(b);
    let bc = and_bool(&b, c);
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
        rc.push(Boolean::constant((rc_arr[r] >> i) == 1));
    }

    let mut res = xor_bool(&inp[0..64], &rc);
    for i in 64..25*54 {
        res.push(inp[i].clone())
    }
    res
}

