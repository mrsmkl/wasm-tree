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

use crate::{VM,Transition,hash_list,hash_code};
use crate::InstructionCircuit;
use ark_r1cs_std::boolean::AllocatedBool;
use ark_r1cs_std::boolean::Boolean;

#[derive(Debug, Clone)]
pub struct Params {
    c: Vec<Fr>,
    m: Vec<Vec<Fr>>,
}

pub fn generate_params() -> Params {
    let mut test_rng = ark_std::test_rng();
    let mut c = vec![];
    for i in 0..1000 {
        c.push(Fr::rand(&mut test_rng))
    }
    let mut m = vec![];
    for i in 0..20 {
        let mut a = vec![];
        for j in 0..20 {
            a.push(Fr::rand(&mut test_rng))
        }
        m.push(a)
    }
    Params { c, m }
}

fn sigma(a: Fr) -> Fr {
    let a2 = a.square();
    let a4 = a2.square();
    a4*a
}

fn ark(v: Vec<Fr>, c: &Vec<Fr>, round: usize) -> Vec<Fr> {
    let mut res = vec![];

    for i in 0..v.len() {
        res.push(v[i] + c[i + round]);
    }
    res
}

fn mix(v: Vec<Fr>, m: &Vec<Vec<Fr>>) -> Vec<Fr> {
    let mut res = vec![];
    for i in 0..v.len() {
        let mut lc = Fr::from(0);
        for j in 0..v.len() {
            lc += m[i][j]*v[j];
        }
        res.push(lc)
    }
    res
}

pub fn poseidon(params: &Params, inputs: Vec<Fr>) -> Fr {
    let n_rounds_p: Vec<usize> = vec![56, 57, 56, 60, 60, 63, 64, 63, 60, 66, 60, 65, 70, 60, 64, 68];
    let t = inputs.len() + 1;
    let nRoundsF = 8;
    let nRoundsP = n_rounds_p[t - 2];

    let mut mix_out = vec![];
    for j in 0..t {
        if j > 0 {
            mix_out.push(inputs[j-1])
        } else {
            mix_out.push(Fr::from(0));
        }
    }
    for i in 0..(nRoundsF + nRoundsP) {
        let ark_out = ark(mix_out.clone(), &params.c, t*i);
        let mut mix_in = vec![];
        if i < nRoundsF/2 || i >= nRoundsP + nRoundsF/2 {
            for j in 0..t {
                mix_in.push(sigma(ark_out[j]))
            }
        } else {
            mix_in.push(sigma(ark_out[0]));
            for j in 1..t {
                mix_in.push(ark_out[j])
            }
        }
        mix_out = mix(mix_in, &params.m);
    }
    mix_out[0]
}

fn sigma_gadget(a: FpVar<Fr>) -> FpVar<Fr> {
    let a2 = a.square().unwrap();
    let a4 = a2.square().unwrap();
    a4*a
}

fn ark_gadget(v: Vec<FpVar<Fr>>, c: &Vec<Fr>, round: usize) -> Vec<FpVar<Fr>> {
    let mut res = vec![];

    for i in 0..v.len() {
        res.push(v[i].clone() + FpVar::Constant(c[i + round]));
    }
    res
}

fn mix_gadget(v: Vec<FpVar<Fr>>, m: &Vec<Vec<Fr>>) -> Vec<FpVar<Fr>> {
    let mut res = vec![];
    for i in 0..v.len() {
        let mut lc = FpVar::Constant(m[i][0])*v[0].clone();
        for j in 1..v.len() {
            lc += FpVar::Constant(m[i][j])*v[j].clone();
        }
        res.push(lc)
    }
    res
}

pub fn poseidon_gadget(params: &Params, inputs: Vec<FpVar<Fr>>) -> FpVar<Fr> {
    let n_rounds_p: Vec<usize> = vec![56, 57, 56, 60, 60, 63, 64, 63, 60, 66, 60, 65, 70, 60, 64, 68];
    let t = inputs.len() + 1;
    let nRoundsF = 8;
    let nRoundsP = n_rounds_p[t - 2];

    let mut mix_out = vec![];
    for j in 0..t {
        if j > 0 {
            mix_out.push(inputs[j-1].clone())
        } else {
            mix_out.push(FpVar::Constant(Fr::from(0)));
        }
    }
    for i in 0..(nRoundsF + nRoundsP) {
        let ark_out = ark_gadget(mix_out.clone(), &params.c, t*i);
        let mut mix_in = vec![];
        if i < nRoundsF/2 || i >= nRoundsP + nRoundsF/2 {
            for j in 0..t {
                mix_in.push(sigma_gadget(ark_out[j].clone()))
            }
        } else {
            mix_in.push(sigma_gadget(ark_out[0].clone()));
            for j in 1..t {
                mix_in.push(ark_out[j].clone())
            }
        }
        mix_out = mix_gadget(mix_in, &params.m);
    }
    mix_out[0].clone()
}

#[derive(Debug, Clone)]
pub struct TestCircuit {
    pub steps: usize,
    pub params: PoseidonParameters<Fr>,
}

impl InstructionCircuit for TestCircuit {
    fn calc_hash(&self) -> Fr {
        panic!("calc hash");
    }
    fn transition(&self) -> Transition {
        panic!("transition")
    }
}

fn generate_step(cs: ConstraintSystemRef<Fr>, params: PoseidonParameters<Fr>, params_g: &CRHParametersVar::<Fr>)
-> Result<FpVar<Fr>, SynthesisError> {
    let var_a = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(1))).unwrap());
    let var_b = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(2))).unwrap());
    let var_c = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(2))).unwrap());
    let var_d = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(2))).unwrap());
    let var_e = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(2))).unwrap());
    let var_f = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(2))).unwrap());

    let mut inputs = Vec::new();
    inputs.push(var_a);
    inputs.push(var_b);
    inputs.push(var_c);
    inputs.push(var_d);
    inputs.push(var_e);
    inputs.push(var_f);
    let hash_gadget = CRHGadget::<Fr>::evaluate(&params_g, &inputs).unwrap();

    Ok(hash_gadget)
}

impl ConstraintSynthesizer<Fr> for TestCircuit {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<Fr>,
    ) -> Result<(), SynthesisError> {
        let params_g = CRHParametersVar::<Fr>::new_witness(cs.clone(), || Ok(self.params.clone())).unwrap();
        // make each step
        let mut vars = vec![];
        for el in 0..self.steps {
            let var = generate_step(cs.clone(), self.params.clone(), &params_g);
            vars.push(var);
        }
        // println!("num constraints {}, valid {}", cs.num_constraints(), cs.is_satisfied().unwrap());
        println!("num constraints {}", cs.num_constraints());
        Ok(())
    }
}

// gadget for variable length merkle tree
// returns the root and index of first elem
fn make_path(cs: ConstraintSystemRef<Fr>, num: usize, params : &Params, elem: FpVar<Fr>, path: &[Fr], selectors: &[bool]) -> (FpVar<Fr>, FpVar<Fr>) {
    let mut acc = elem.clone();
    let mut idx = FpVar::constant(Fr::from(0));
    for i in 0..num {
        let elem = if path.len() > i { path[i] } else { Fr::from(0) };
        let sel = if selectors.len() > i { selectors[i] } else { false };
        let skip = selectors.len() <= i;
        let sel_bool = Boolean::from(AllocatedBool::<Fr>::new_witness(cs.clone(), || Ok(sel)).unwrap());
        let skip_bool = Boolean::from(AllocatedBool::<Fr>::new_witness(cs.clone(), || Ok(skip)).unwrap());
        let new_idx = idx.clone()+idx.clone() + FpVar::from(sel_bool.clone());
        let elem_var = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(elem.clone())).unwrap());
        let leaf1 = sel_bool.select(&elem_var, &acc).unwrap();
        let leaf2 = sel_bool.select(&acc, &elem_var).unwrap();

        let new_acc = poseidon_gadget(&params, vec![leaf1, leaf2]);

        acc = skip_bool.select(&acc, &new_acc).unwrap();
        idx = skip_bool.select(&idx, &new_idx).unwrap();
    }
    (acc, idx)
}

pub fn test(params: &PoseidonParameters<Fr>) {
    use ark_std::test_rng;
    use crate::InnerSNARK;
    use ark_crypto_primitives::CircuitSpecificSetupSNARK;
    use ark_crypto_primitives::SNARK;
    let cs_sys = ConstraintSystem::<Fr>::new();
    let cs = ConstraintSystemRef::new(cs_sys);
    let circuit = TestCircuit {
        params: params.clone(),
        steps: 100,
    };
    let params = generate_params();
    println!("hash {}", poseidon(&params, vec![Fr::from(123), Fr::from(123), Fr::from(123)]));
    let v1 = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(123))).unwrap());
    let v2 = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(123))).unwrap());
    let v3 = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(123))).unwrap());
    let v4 = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(123))).unwrap());
    let v5 = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(123))).unwrap());
    let v6 = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(123))).unwrap());
    let v7 = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(123))).unwrap());
    let res = poseidon_gadget(&params, vec![v1, v2, v3, v4, v5, v6]);
    println!("gadget {}", res.value().unwrap());
    println!("constraints {}", cs.num_constraints());
    // circuit.generate_constraints(cs);
    /*
    let mut rng = test_rng();
    println!("Setting up circuit");
    let (pk, vk) = InnerSNARK::setup(circuit.clone(), &mut rng).unwrap();
    println!("Testing prove");
    let proof = InnerSNARK::prove(&pk, circuit.clone(), &mut rng).unwrap();
    */
}
