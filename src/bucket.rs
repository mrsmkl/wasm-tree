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

// use ark_r1cs_std::R1CSVar;

#[derive(Debug, Clone)]
struct Bucket {
    list: Vec<usize>,
    idx: usize,
    slice_start: usize,
    slice_size: usize,
}

impl Bucket {
    fn new(idx: usize) -> Self {
        Bucket {
            list: vec![],
            idx,
            slice_start: 0,
            slice_size: 0,
        }
    }
    fn set_slice(&self, slice_start: usize, slice_size: usize) -> Self {
        Bucket {
            list: self.list.clone(),
            idx: self.idx,
            slice_start,
            slice_size,
        }
    }
    fn size(&self) -> usize {
        self.list.len()
    }
}

fn make_buckets(trs: &Vec<Transition>, bucket_size: usize, num_buckets: usize) -> Vec<Bucket> {
    let mut buckets = vec![];
    for i in 0..num_buckets {
        buckets.push(Bucket::new(i));
    };
    for (i, tr) in trs.iter().enumerate() {
        let c = tr.before.step_counter;
        let bucket_idx = c / bucket_size;
        buckets[bucket_idx].list.push(i);
    };
    buckets
}

#[derive(Debug, Clone)]
struct Slices {
    slices: Vec<(usize,usize)>
}

impl Slices {
    fn new(num: usize) -> Self {
        let mut num = num;
        let mut slices = vec![];
        let mut acc = 0;
        while num > 0 {
            slices.push((num, acc));
            acc += num;
            num = num / 2;
        };
        Slices { slices }
    }

    fn reserve(&mut self, num: usize) -> (usize, usize) {
        // find first that is large enough
        // if too large, split it first
        for i in 0..self.slices.len() {
            let (sz, idx) = self.slices[i].clone();
            let mut sz = sz;
            if num < sz {
                let mut next_idx = idx + sz/2;
                while num < sz/2 {
                    sz = sz/2;
                    self.slices.push((sz, next_idx));
                    next_idx = next_idx - sz/2;
                };
                self.slices[i] = (0,0);
                return (sz, idx)
            }
        }
        panic!("Cannot find slice");
    }
}


fn make_bucket_slices(mut buckets: Vec<Bucket>) -> Vec<Bucket> {
    // sort buckets by size
    buckets.sort_by(|a, b| (a.list.len()).cmp(&b.list.len()));
    let mut slices = Slices::new(buckets.len());
    let mut res = vec![];
    for b in buckets.iter() {
        let (start, idx) = slices.reserve(b.size());
        res.push(b.set_slice(start, idx));
    };
    res
}

// route buckets to the bottom of the tree
// elems is the number of elems in the buckets
fn route_bucket_contents(buckets: &Vec<Bucket>, elems: usize) -> IntegerPermutation {
    let mut list : Vec<i32> = vec![-1; elems*2-1];
    for bucket in buckets.iter() {
        let start = bucket.slice_start;
        for (i, idx) in bucket.list.iter().enumerate() {
            list[start+i] = *idx as i32;
        }
    };
    let mut acc = elems;
    // route zeroes
    for i in 0..list.len() {
        if list[i] == -1 {
            list[i] = acc as i32;
            acc += 1;
        }
    }
    // create permutation
    let mut perm = IntegerPermutation::new(elems*2-1);
    for i in 0..list.len() {
        perm.set(i, list[i] as usize);
    }
    perm
}

////// route buckets from the merkle tree

// compute idx of bucket in the tree
// bottom level has lowest indices
fn compute_idx(b: &Bucket, elems: usize) -> i32 {
    let mut sz = b.slice_size;
    let mut level_idx = b.slice_start;
    let mut elems = elems;
    let mut level_acc = 0;
    while sz > 1 {
        sz = sz/2;
        level_acc += elems*2-1;
        elems = elems/2;
        level_idx = level_idx/2;
    }
    (level_idx + level_acc) as i32
}

fn total_size(elems: usize) -> usize {
    let mut elems = elems;
    let mut size = 0;
    while elems > 0 {
        size += elems*2-1;
        elems = elems/2;
    }
    size
}

fn route_buckets(buckets: &Vec<Bucket>, elems: usize) -> IntegerPermutation {
    let size = total_size(elems);
    let mut list : Vec<i32> = vec![-1; size];
    for bucket in buckets.iter() {
        list[bucket.idx] = compute_idx(bucket, elems);
    };
    let mut acc = buckets.len();
    // route zeroes
    for i in 0..list.len() {
        if list[i] == -1 {
            list[i] = acc as i32;
            acc += 1;
        }
    }
    // create permutation
    let mut perm = IntegerPermutation::new(size);
    for i in 0..list.len() {
        perm.set(i, list[i] as usize);
    }
    perm
}

// make merkle tree from variables
fn hash_tree(
    _cs: &ConstraintSystemRef<Fr>,
    _params: &PoseidonParameters<Fr>,
    params_g: &CRHParametersVar::<Fr>,
    vars: &[FpVar<Fr>],
) -> Vec<FpVar<Fr>> {
    let mut tree = vec![];
    for v in vars.iter() {
        tree.push(v.clone());
    }
    let mut level : Vec<_> = vars.iter().map(|a| a.clone()).collect();
    while level.len() > 1 {
        let mut next_level = vec![];
        for i in 0..level.len()/2 {
            let var = CRHGadget::<Fr>::evaluate(&params_g, &vec![
                level[2*i].clone(), level[2*i+1].clone()
            ]).unwrap();
            tree.push(var.clone());
            next_level.push(var);
        }
        // tree.push(next_level.clone());
        level = next_level;
    }
    tree
}

// zero sized buckets will also have a slice, they will get constant zero as input

fn compute_buckets(
    cs: ConstraintSystemRef<Fr>,
    params: &PoseidonParameters<Fr>,
    params_g: &CRHParametersVar::<Fr>,
    vars: Vec<FpVar<Fr>>,
    trs: &Vec<Transition>,
    bucket_size: usize,
    num_buckets: usize,
) -> FpVar<Fr> {
    let elems = trs.len();
    let buckets = make_buckets(trs, bucket_size, num_buckets);
    let buckets = make_bucket_slices(buckets);
    let perm1 = route_bucket_contents(&buckets, elems);
    // use permutation
    let mut vars = vars.clone();
    let zero_var = FpVar::Constant(Fr::from(0));
    while vars.len() < elems*2-1 {
        vars.push(zero_var.clone());
    }
    let tree_bottom = crate::permutation::permutation(cs.clone(), vars, perm1);
    let tree_vars = hash_tree(&cs, &params, &params_g, &tree_bottom);
    // use second permutation
    let perm2 = route_buckets(&buckets, elems);
    let bucket_vars = crate::permutation::permutation(cs.clone(), tree_vars, perm2);
    let bucket_tree_vars = hash_tree(&cs, &params, &params_g, &bucket_vars[0..num_buckets]);
    bucket_tree_vars.last().unwrap().clone()
}

