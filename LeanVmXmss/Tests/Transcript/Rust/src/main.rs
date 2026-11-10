use fiat_shamir::{merkle::{hash_leaf, hash_pair, hash_to_scalars}, transcript::ProverState};
use primitives::field::F192;

pub use verifier::VerifierError;

pub fn require(valid: bool, error: VerifierError) -> Result<(), VerifierError> {
    if valid { Ok(()) } else { Err(error) }
}

#[path = "../../../../../references/leanVM/crates/verifier/src/field.rs"]
mod field;
#[path = "../../../../../references/leanVM/crates/verifier/src/hash.rs"]
mod hash;
#[path = "../../../../../references/leanVM/crates/verifier/src/merkle.rs"]
mod merkle;
#[path = "../../../../../references/leanVM/crates/verifier/src/multilinear.rs"]
mod multilinear;
#[path = "../../../../../references/leanVM/crates/verifier/src/transcript.rs"]
mod transcript;

#[path = "../../../../../references/leanVM/crates/pcs/src/merkle.rs"]
mod pcs_merkle;

fn bytes(b: &[u8]) {
    println!("{}", b.iter().map(|b| b.to_string()).collect::<Vec<_>>().join(" "));
}

fn scalar(x: F192) {
    println!("{} {} {}", x.c0, x.c1, x.c2);
}

fn pattern(n: usize) -> Vec<u8> {
    (0..n).map(|i| (i * 7 + 3) as u8).collect()
}

fn main() {
    for n in [0, 1, 135, 136, 137, 272, 1000] {
        bytes(&primitives::hash::hash(&pattern(n)));
    }
    let abc = primitives::hash::hash(b"abc");
    bytes(&abc);
    for x in hash_to_scalars(&abc) { scalar(x); }
    for width in [1, 2, 4, 8] {
        let mut levels = vec![(0..width).map(|i| {
            let words: [u64; 5] = [0, 0, 0, i + 1, i * 11];
            hash_leaf(&words.iter().flat_map(|w| w.to_le_bytes()).collect::<Vec<_>>())
        }).collect::<Vec<_>>()];
        while levels.last().unwrap().len() > 1 {
            let next = levels.last().unwrap().chunks_exact(2).map(|c| hash_pair(&c[0], &c[1])).collect();
            levels.push(next);
        }
        bytes(&levels.last().unwrap()[0]);
        let rows = (0..width).map(|i| vec![primitives::field::F64(i + 1), primitives::field::F64(i * 11)]).collect::<Vec<_>>();
        let builder = pcs_merkle::MerkleBuilder::new(width as usize, 2, 5);
        builder.absorb(0, &rows.iter().flatten().copied().collect::<Vec<_>>());
        let tree = builder.finish();
        assert_eq!(tree.root(), levels.last().unwrap()[0]);
        let queries = if width == 1 { vec![0, 0] } else { vec![width as usize - 1, 0, 1, 0] };
        let pruned = tree.prune(&queries, 2, 5,
            &queries.iter().copied().collect::<std::collections::BTreeSet<_>>().into_iter().flat_map(|q| rows[q].clone()).collect::<Vec<_>>(),
            |q| &rows[q]);
        let batch = merkle::PrunedMerklePaths {
            leaf_data: pruned.leaf_data.iter().map(|r| r.iter().map(|w| field::K(w.0)).collect()).collect(),
            sibling_hashes: pruned.sibling_hashes.clone(),
        };
        let qs = queries.iter().map(|&q| q as u64).collect::<Vec<_>>();
        let depth = (width as usize).ilog2() as usize;
        let (root, paths) = batch.expand(depth, &qs, 2, 5).unwrap();
        assert_eq!(root.0, tree.root());
        for path in paths { assert_eq!(path.root(), root); }
        let mut extra = batch.clone(); extra.sibling_hashes.push([0;32]);
        assert!(extra.expand(depth, &qs, 2, 5).is_err());
        let mut bad_rows = batch.clone(); bad_rows.leaf_data[0].push(field::K(1));
        assert!(bad_rows.expand(depth, &qs, 2, 5).is_err());
        assert!(batch.expand(depth, &[width], 2, 5).is_err());
        assert!(batch.expand(depth, &[], 2, 5).is_err());
        let proof = transcript::Proof { stream: vec![], merkle_openings: merkle::MerkleOpenings::Pruned(vec![batch]) };
        let zero = hash::Digest([0;32]);
        let mut replay = transcript::Transcript::new(&proof, zero, zero, true);
        replay.merkle(root, width, &qs, 2, 5).unwrap();
        assert_eq!(replay.finish().unwrap().len(), qs.len());
        assert!(transcript::Transcript::new(&proof, zero, zero, true).finish().is_err());
        for i in 0..width as usize {
            let words: [u64; 5] = [0, 0, 0, i as u64 + 1, i as u64 * 11];
            let mut opening = words.iter().flat_map(|w| w.to_le_bytes()).collect::<Vec<_>>();
            for (level, nodes) in levels.iter().take(levels.len() - 1).enumerate() {
                bytes(&nodes[(i >> level) ^ 1]);
                opening.extend_from_slice(&nodes[(i >> level) ^ 1]);
            }
            let proof = transcript::Proof { stream: vec![], merkle_openings: merkle::MerkleOpenings::Raw(opening) };
            let zero = hash::Digest([0; 32]);
            let mut t = transcript::Transcript::new(&proof, zero, zero, true);
            t.merkle(hash::Digest(levels.last().unwrap()[0]), width, &[i as u64], 2, 5).unwrap();
            assert_eq!(t.finish().unwrap().len(), 1);
        }
    }
    let mut p = ProverState::from_label(b"shard-b");
    let mut challenges = Vec::new();
    for i in 0..11 {
        p.add_scalar(F192::new(i + 1, i * 17, i * 31));
        if i % 3 == 2 {
            let x = p.sample();
            scalar(x);
            challenges.push(x);
        }
    }
    p.add_root(&abc);
    p.add_round_poly(&[F192::new(1, 2, 3), F192::new(4, 5, 6), F192::new(7, 8, 9)], false);
    p.add_round_poly(&[F192::new(11, 12, 13), F192::new(14, 15, 16), F192::new(17, 18, 19)], true);
    let mut nonces = Vec::new();
    for bits in [0, 4, 8] {
        p.grind(bits);
        let challenge = p.sample();
        nonces.push((bits, challenge));
    }
    let proof = p.into_proof();
    let wire = proof.stream.iter().flat_map(|x| [x.c0, x.c1, x.c2].into_iter().flat_map(|w| w.to_le_bytes())).collect::<Vec<_>>();
    let replay_proof = transcript::Proof::load(&wire, &[]).unwrap();
    let iv = hash::keccak_hash(b"shard-b");
    let mut replay = transcript::Transcript::new(&replay_proof, iv, hash::Digest([0; 32]), true);
    for i in 0..11 {
        replay.next_scalar().unwrap();
        if i % 3 == 2 {
            let x = replay.sample();
            let want = challenges[(i / 3) as usize];
            assert_eq!((x.c0, x.c1, x.c2), (want.c0, want.c1, want.c2));
        }
    }
    replay.next_scalars(2).unwrap();
    let plain = replay.sumcheck_round_poly(3, field::E::new(3, 13, 15), None).unwrap();
    assert_eq!(plain, vec![field::E::new(1,2,3), field::E::new(4,5,6), field::E::new(7,8,9)]);
    let eq = replay.sumcheck_round_poly(3, field::E::new(20,17,14), Some(field::E::new(1,0,0))).unwrap();
    assert_eq!(eq, vec![field::E::new(11,12,13), field::E::new(14,15,16), field::E::new(17,18,19)]);
    for (bits, want) in &nonces {
        replay.grind_check(*bits).unwrap();
        let x = replay.sample();
        assert_eq!((x.c0, x.c1, x.c2), (want.c0, want.c1, want.c2));
    }
    replay.finish().unwrap();
    for (j, (_, challenge)) in nonces.iter().enumerate() {
        println!("{}", proof.stream[17 + j].c0);
        scalar(*challenge);
    }
    bytes(&wire);
}
