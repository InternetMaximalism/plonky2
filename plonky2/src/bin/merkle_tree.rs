use plonky2::hash::hash_types::RichField;
use plonky2::hash::merkle_tree::MerkleTree;

const LOG_N: usize = 15; // For Poseidon-12

fn random_data<F: RichField>(n: usize, k: usize) -> Vec<Vec<F>> {
    (0..n).map(|_| vec![F::ZERO; k]).collect()
    // (0..n).map(|_| F::rand_vec(k)).collect()
}

pub(crate) fn main() {
    // use plonky2::field::types::Sample;
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};

    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    let log_n = LOG_N;
    let n = 1 << log_n;

    let leaves = random_data::<F>(n, 2720);

    let cap_height = 3;

    // let leaves = (0..n).map(|_| vec![F::rand()]).collect::<Vec<_>>();

    let tree = MerkleTree::<F, <C as GenericConfig<D>>::Hasher>::new(leaves.clone(), cap_height);

    // for (i, l) in tree.leaves.iter().enumerate() {
    //     println!("leave{} is {:x?}", i, l);
    // }

    // let digests: <C as GenericConfig<D>>::Hasher = tree.digests;
    // for (i, d) in tree.digests.iter().enumerate() {
    //     println!("digest{} is {:x?}", i, d);
    // }
    for (i, c) in tree.cap.0.iter().enumerate() {
        println!("cap{} is {:x?}", i, c);
    }
}
