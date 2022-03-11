use crate::as_waksman::IntegerPermutation;
use crate::as_waksman::AsWaksmanRoute;
use crate::as_waksman::AsWaksmanTopology;
use crate::Transition;

use ark_mnt4_298::Fr;
use ark_crypto_primitives::crh::poseidon::constraints::CRHGadget;
use ark_r1cs_std::fields::fp::FpVar;
use ark_crypto_primitives::crh::poseidon::constraints::CRHParametersVar;
use ark_crypto_primitives::CRHSchemeGadget;
use ark_sponge::poseidon::PoseidonParameters;
use ark_relations::r1cs::ConstraintSystemRef;
use ark_r1cs_std::prelude::CondSelectGadget;
use ark_r1cs_std::boolean::AllocatedBool;
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::fp::AllocatedFp;
use ark_relations::r1cs::ConstraintSystem;

#[derive(Debug, Clone)]
struct Step {
    a: usize,
    b: usize,
    c: usize,
    input: i32,
}

fn make_bools(cs: &ConstraintSystemRef<Fr>, mem_size: usize, a: usize) -> Vec<Boolean<Fr>> {
    let mut a_bools = vec![];
    for i in 0..mem_size {
        let is_set = (a >> i) % 2 == 1;
        let bool_var = Boolean::from(AllocatedBool::<Fr>::new_witness(cs.clone(), || Ok(is_set)).unwrap());
        a_bools.push(bool_var)
    }
    a_bools
}

fn hash_step(
    cs: &ConstraintSystemRef<Fr>,
    step: Step,
    params: &PoseidonParameters<Fr>,
    params_g: &CRHParametersVar::<Fr>,
    vars: &[FpVar<Fr>], // memory
    var_sums: &[FpVar<Fr>], // memory
    input: FpVar<Fr>, // input from permutation
    input_sum: FpVar<Fr>, // input from permutation
    mem_size: usize,
) -> (Vec<FpVar<Fr>>, Vec<FpVar<Fr>>) { // output memory
    let mut inputs = vec![];
    for v in vars.iter() {
        inputs.push(v.clone());
    }
    inputs.push(input);
    let mut input_sums = vec![];
    for v in var_sums.iter() {
        input_sums.push(v.clone());
    }
    input_sums.push(input_sum);

    let a_bools = make_bools(cs, mem_size, step.a);
    let b_bools = make_bools(cs, mem_size, step.b);

    let a_var = FpVar::conditionally_select_power_of_two_vector(&a_bools, &inputs).unwrap();
    let b_var = FpVar::conditionally_select_power_of_two_vector(&b_bools, &inputs).unwrap();

    let a_sum_var = FpVar::conditionally_select_power_of_two_vector(&a_bools, &input_sums).unwrap();
    let b_sum_var = FpVar::conditionally_select_power_of_two_vector(&b_bools, &input_sums).unwrap();

    let c_var = CRHGadget::<Fr>::evaluate(&params_g, &vec![a_var.clone(), b_var.clone()]).unwrap();
    // let c_var = a_var + b_var;
    // let c_sum_var = a_var + b_var;
    let c_sum_var = a_sum_var + b_sum_var;

    let mut outputs = vec![];
    let mut output_sums = vec![];
    let c_idx_var = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(step.c as u32))).unwrap());
    for (i,v) in vars.iter().enumerate() {
        let idx_var = FpVar::Constant(Fr::from(i as u32));
        let bool_var = idx_var.is_eq(&c_idx_var).unwrap();
        let out_var = bool_var.select(&c_var, &v).unwrap();
        let out_sum_var = bool_var.select(&c_sum_var, &var_sums[i]).unwrap();
        outputs.push(out_var);
        output_sums.push(out_sum_var);
    };
    (outputs, output_sums)
}

fn route_steps(steps: &Vec<Step>) -> IntegerPermutation {
    let mut list : Vec<i32> = vec![-1; steps.len()];
    let mut num = 0;
    for (i,step) in steps.iter().enumerate() {
        list[i] = step.input;
        if step.input >= 0 {
            num += 1
        }
    };
    // route zeroes
    for i in 0..list.len() {
        if list[i] == -1 {
            list[i] = num as i32;
            num += 1;
        }
    }
    // create permutation
    let mut perm = IntegerPermutation::new(steps.len());
    for i in 0..list.len() {
        perm.set(i, list[i] as usize);
    }
    perm
}

fn hash_steps(
    cs: &ConstraintSystemRef<Fr>,
    steps: Vec<Step>,
    params: &PoseidonParameters<Fr>,
    params_g: &CRHParametersVar::<Fr>,
    vars: Vec<FpVar<Fr>>, // memory
    var_sums: Vec<FpVar<Fr>>, // memory sums (probably zeros)
    inputs: Vec<FpVar<Fr>>, // inputs, make permutation
    input_sums: Vec<FpVar<Fr>>, // inputs, make permutation
    mem_size: usize,
) -> (FpVar<Fr>, FpVar<Fr>) {
    // first permute inputs
    let route = route_steps(&steps);
    // actually both have to be permuted the same way...
    let mut inputs_with_sums = vec![];
    for i in 0..inputs.len() {
        inputs_with_sums.push(vec![inputs[i].clone(), input_sums[i].clone()])
    }
    let inputs_with_sums = crate::permutation::permutation_list(cs.clone(), inputs_with_sums, route);
    let mut vars = vars.clone();
    let mut var_sums = var_sums.clone();
    for (i, step) in steps.iter().enumerate() {
        let a = hash_step(cs, step.clone(), params, params_g, &vars, &var_sums, inputs_with_sums[i][0].clone(), inputs_with_sums[i][1].clone(), mem_size);
        vars = a.0;
        var_sums = a.1;
    }
    (vars[0].clone(), var_sums[0].clone())
}

pub fn test_tree(params: &PoseidonParameters<Fr>) {
    let cs_sys = ConstraintSystem::<Fr>::new();
    let cs = ConstraintSystemRef::new(cs_sys);
    let params_g = CRHParametersVar::<Fr>::new_witness(cs.clone(), || Ok(params.clone())).unwrap();

    let size = 1024*2;
    let mem_size_bits = 4;
    let mem_size = 1 << mem_size_bits;

    let mut vars = vec![];
    let mut inputs = vec![];
    let mut var_sums = vec![];
    let mut input_sums = vec![];
    let mut steps = vec![];
    for i in 0..size {
        let var = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(i as u32))).unwrap());
        inputs.push(var);
        let var = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(i as u32))).unwrap());
        input_sums.push(var);
        steps.push(Step {
            a: 0,
            b: 0,
            c: 0,
            input: -1,
        });
    }
    for i in 0..mem_size-1 {
        let var = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(i as u32))).unwrap());
        vars.push(var);
        let var = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(Fr::from(i as u32))).unwrap());
        var_sums.push(var);
    }
    hash_steps(&cs, steps, &params, &params_g,
        vars,
        var_sums, // memory sums (probably zeros)
        inputs, // inputs, make permutation
        input_sums, // inputs, make permutation
        mem_size_bits,
    );
    println!("num constraints {}, valid {}", cs.num_constraints(), cs.is_satisfied().unwrap());
}
