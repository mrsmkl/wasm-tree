use crate::as_waksman::IntegerPermutation;
use crate::as_waksman::AsWaksmanRoute;
use crate::as_waksman::AsWaksmanTopology;
use crate::Transition;

// use ark_r1cs_std::R1CSVar;

#[derive(Debug, Clone)]
struct Bucket {
    list: Vec<usize>,
    idx: usize,
}

impl Bucket {
    fn new(idx: usize) -> Self {
        Bucket {
            list: vec![],
            idx,
        }
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
                }
                return (sz, idx)
            }
        }
        panic!("Cannot find slice");
    }
}

