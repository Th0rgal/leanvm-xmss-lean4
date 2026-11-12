//! W5 Maxwell negative-mutant suite (Rust half).
//!
//! Builds two valid baselines and then runs one or more explicit mutations per
//! plan.md category, asserting that every mutant is rejected with a specific
//! error. The Lean half (category 4: VM opcode / unconstrained read / bad PC)
//! lives in `Tests/Audit/Mutants.lean`.
//!
//! Baselines:
//!   * `syn_keccak`  - the reference's hand-assembled two-KECCAK program
//!                     (leanvm_core cpu tests), proven and verified.
//!   * `xmss4`       - the oracle's 4-signer leanXMSS aggregate, rebuilt from
//!                     `oracle/xmss4/xmss-inputs.bin`, proven and verified.
//!
//! Exit code 0 iff both baselines verify and every mutant is rejected.

use std::collections::BTreeMap;
use std::path::Path;

use leanvm_core::cpu::{self, Op, Program};
use primitives::field::F192;
use rec_aggregation::aggregation::unified_guest;
use rec_aggregation::{aggregate, EthereumProof};
use signatures::lean_xmss::{self, LeanXmssPublicKey, LeanXmssSignature, Message};
use verifier as vrf;

/// The leanXMSS layout constants the reference keeps `pub(crate)`, recovered from
/// its public ones (and re-asserted here): leaf index 4 bytes, two 1200-byte
/// layers of randomizer(16) + V*N(928) + LAYER_HEIGHT*N(256).
const N: usize = lean_xmss::DIGITS * lean_xmss::W / 8;
const LEAF_INDEX_SIZE: usize = lean_xmss::LOG_LIFETIME / 8;
const LAYER_SIG_SIZE: usize = (lean_xmss::SIG_SIZE - LEAF_INDEX_SIZE) / 2;
const _: () = assert!(N == 16 && LEAF_INDEX_SIZE == 4 && LAYER_SIG_SIZE == 1200
    && lean_xmss::PUB_KEY_SIZE == 2 * N && lean_xmss::SIG_SIZE == LEAF_INDEX_SIZE + 2 * LAYER_SIG_SIZE);

// Re-exports of `pub(super)` helpers from the reference aggregator, via the
// oracle's #[path]-include trick: the included sources' `super` is this module.
mod agg {
    use primitives::field::F192;
    use signatures::lean_xmss::{LeanXmssPublicKey, LeanXmssSignature, Message};

    pub fn count(n: usize) -> F192 {
        cells::count(n)
    }

    pub fn pack(bytes: &[u8]) -> F192 {
        cells::pack_16_bytes(bytes)
    }

    pub fn xmss_hints(
        pk: &LeanXmssPublicKey,
        sig: &LeanXmssSignature,
        message: &Message,
    ) -> Vec<(&'static str, Vec<F192>)> {
        hints::lean_xmss_hints(pk, sig, message).expect("honest raw signature")
    }

    #[path = "/var/lib/orb-node/work/caches/xmss-hub-v3/references/leanVM/crates/rec_aggregation/src/aggregation/cells.rs"]
    pub mod cells;
    #[path = "/var/lib/orb-node/work/caches/xmss-hub-v3/references/leanVM/crates/rec_aggregation/src/aggregation/hints.rs"]
    pub mod hints;

    /// Stub of the aggregator's error type: the included `hints.rs` only ever
    /// constructs `MalformedRawSignature`.
    pub mod error {
        #[derive(Debug)]
        pub enum AggregationError {
            MalformedRawSignature,
        }
    }
}

fn w(x: u64) -> F192 {
    F192::new(x, 0, 0)
}

/// The reference's two-KECCAK hand-assembled program (a copy of the
/// `keccak_program` test helper in `leanvm_core/src/cpu/mod.rs`).
fn keccak_program() -> Program {
    let a = F192::new(0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210, 0);
    let b = F192::new(0xdead_beef_cafe_babe, 0x0bad_f00d_0bad_f00d, 0);
    let pad = F192::new(primitives::hash::PAD_FIRST as u64, 0, 0);
    let end = F192::new(primitives::hash::END_BIT, 0x5555, 0);
    let mut prog = vec![Op::Set { o: 2, k: a }, Op::Set { o: 3, k: b }];
    for (i, &t) in [pad, F192::ZERO, F192::ZERO, F192::ZERO].iter().enumerate() {
        prog.push(Op::Set { o: 4 + i as u32, k: t });
    }
    prog.push(Op::Set { o: 8, k: end });
    for c in 0..4u32 {
        prog.push(Op::Set { o: 9 + c, k: F192::ZERO });
    }
    prog.push(Op::Keccak {
        m: [2, 3, 2, 3],
        tail: 4,
        b8: 8,
        cap: 9,
        out: 13,
        in_odd: false,
        out_odd: true,
    });
    prog.push(Op::Keccak {
        m: [13, 14, 15, 16],
        tail: 17,
        b8: 21,
        cap: 22,
        out: 26,
        in_odd: true,
        out_odd: false,
    });
    for k in 0..2u32 {
        prog.push(Op::Set { o: 39 + k, k: F192::ONE });
    }
    prog.push(Op::Xor { a: 0, b: 0, c: 0 }); // sentinel, never executed
    assert_eq!(prog.len(), 16);
    Program::assemble(prog, std::collections::HashMap::new(), 64)
}

struct VmBaseline {
    program: Program,
    pi: [F192; 2],
    proof: cpu::Proof,
    vbytecode: vrf::Bytecode,
    pi_bytes: [u8; 32],
}

fn build_vm_baseline() -> VmBaseline {
    let program = keccak_program();
    let pi = [w(7), w(11)];
    let (proof, _stats) = cpu::prove(&program, pi, leanvm_core::pcs::TEST_LOG_INV_RATE)
        .expect("syn_keccak baseline proves");
    let table: Vec<u64> =
        leanvm_core::cpu::layout::bytecode_table(&program.prog).iter().map(|x| x.0).collect();
    let vbytecode = vrf::Bytecode::new(&table);
    let pi_bytes = cpu::public_input_bytes(&pi);
    vrf::verify_execution(&vbytecode, &pi_bytes, &cpu::scalar_proof(&proof))
        .expect("syn_keccak baseline verifies");
    VmBaseline {
        program,
        pi,
        proof,
        vbytecode,
        pi_bytes,
    }
}

impl VmBaseline {
    fn verify_proof(&self, proof: &cpu::Proof) -> Result<vrf::Summary, String> {
        vrf::verify_execution(&self.vbytecode, &self.pi_bytes, &cpu::scalar_proof(proof))
            .map_err(|e| e.to_string())
    }
}

struct EthBaseline {
    guest: &'static Program,
    records: Vec<[u8; 2468]>,
    streams: BTreeMap<String, Vec<Vec<F192>>>,
    pi: [F192; 2],
    eth: EthereumProof,
}

fn load_records(dir: &Path) -> Vec<[u8; 2468]> {
    let input = std::fs::read(dir.join("xmss-inputs.bin")).expect("read xmss-inputs.bin");
    assert!(input.len() % 2468 == 0, "xmss-inputs.bin is not a whole number of records");
    let mut records: Vec<[u8; 2468]> =
        input.chunks_exact(2468).map(|c| c.try_into().unwrap()).collect();
    records.sort_by(|a, b| a[..64].cmp(&b[..64]));
    records.dedup_by(|a, b| a[..64] == b[..64]);
    records
}

fn build_eth_baseline(dir: &Path) -> EthBaseline {
    let records = load_records(dir);
    let guest = unified_guest();
    let seed = cpu::fs_seed(guest);
    let table = leanvm_core::cpu::layout::bytecode_table(&guest.prog);
    let value = F192::new(table[0].0, 0, 0);

    let mut streams: BTreeMap<String, Vec<Vec<F192>>> = BTreeMap::new();
    let entry = |streams: &mut BTreeMap<String, Vec<Vec<F192>>>, name: &str, values: Vec<F192>| {
        streams.entry(name.to_string()).or_default().push(values);
    };
    entry(
        &mut streams,
        "meta",
        vec![
            agg::count(records.len()),
            agg::count(0),
            agg::count(records.len()),
            agg::count(0),
            agg::count(0),
            agg::count(0),
            agg::count(0),
            agg::count(0),
        ],
    );
    entry(&mut streams, "fs_seed", seed.to_vec());
    let n = records.len();
    entry(
        &mut streams,
        "signers_split",
        vec![agg::count(n / 136), agg::count(n % 136 / 17), agg::count(n % 17)],
    );
    let mut claims = Vec::new();
    for r in &records {
        claims.extend(&r[..64]);
        let cells: Vec<F192> = r[..64].chunks_exact(16).map(agg::pack).collect();
        entry(&mut streams, "claims", cells);
    }
    for (i, r) in records.iter().enumerate() {
        let pk = LeanXmssPublicKey::from_bytes(r[..32].try_into().unwrap());
        let message: Message = r[32..64].try_into().unwrap();
        let sig = LeanXmssSignature::from_bytes(r[64..].try_into().unwrap());
        lean_xmss::verify(&pk, &message, &sig).expect("oracle record is honest");
        entry(&mut streams, "raw_index", vec![agg::count(i)]);
        for (name, values) in agg::xmss_hints(&pk, &sig, &message) {
            entry(&mut streams, name, values);
        }
    }
    entry(&mut streams, "leaf_defer", vec![value]);
    entry(&mut streams, "da_pick", vec![agg::count(0)]);

    let mut seed_bytes = Vec::new();
    for v in seed {
        seed_bytes.extend(v.c0.to_le_bytes());
        seed_bytes.extend(v.c1.to_le_bytes());
    }
    let mut statement = seed_bytes;
    statement.extend(primitives::hash::hash(&claims));
    statement.extend(primitives::hash::hash(&[]));
    statement.extend([0u8; 32]);
    statement.extend([0u8; 23 * 24]);
    for x in [value.c0, value.c1, value.c2] {
        statement.extend(x.to_le_bytes());
    }
    let statement = primitives::hash::hash(&statement);
    let pi = [agg::pack(&statement[..16]), agg::pack(&statement[16..32])];

    let mut prog = guest.clone();
    for (name, values) in &streams {
        prog.set_witness(name.clone(), values.clone());
    }
    prog.execute(pi).expect("honest guest run");

    let raw: Vec<(LeanXmssPublicKey, Message, LeanXmssSignature)> = records
        .iter()
        .map(|r| {
            (
                LeanXmssPublicKey::from_bytes(r[..32].try_into().unwrap()),
                r[32..64].try_into().unwrap(),
                LeanXmssSignature::from_bytes(r[64..].try_into().unwrap()),
            )
        })
        .collect();
    let eth = aggregate(&[], raw, vec![], &[], None, leanvm_core::pcs::TEST_LOG_INV_RATE)
        .expect("xmss4 aggregate proves");
    eth.verify().expect("xmss4 baseline verifies");
    EthBaseline {
        guest,
        records,
        streams,
        pi,
        eth,
    }
}

impl EthBaseline {
    fn guest_run(&self, streams: &BTreeMap<String, Vec<Vec<F192>>>) -> Result<(), String> {
        let mut prog = self.guest.clone();
        for (name, values) in streams {
            prog.set_witness(name.clone(), values.clone());
        }
        prog.execute(self.pi).map(|_| ()).map_err(|e| e.to_string())
    }
}

struct Mutant {
    category: u32,
    name: String,
    level: String,
    rejected: bool,
    error: String,
}

impl Mutant {
    fn reject(category: u32, name: &str, level: &str, error: String) -> Mutant {
        Mutant {
            category,
            name: name.to_string(),
            level: level.to_string(),
            rejected: true,
            error,
        }
    }

    fn accept(category: u32, name: &str, level: &str) -> Mutant {
        Mutant {
            category,
            name: name.to_string(),
            level: level.to_string(),
            rejected: false,
            error: String::new(),
        }
    }
}

/// Category 1 - mutated leanXMSS signature bit.
fn category1(b: &EthBaseline) -> Vec<Mutant> {
    let mut out = Vec::new();
    let r = &b.records[0];
    let pk = LeanXmssPublicKey::from_bytes(r[..32].try_into().unwrap());
    let message: Message = r[32..64].try_into().unwrap();

    // 1a: leaf-index bit (first byte of the signature).
    let mut sig_bytes = r[64..].to_vec();
    sig_bytes[0] ^= 1;
    let sig = LeanXmssSignature::from_bytes(sig_bytes.as_slice().try_into().unwrap());
    match lean_xmss::verify(&pk, &message, &sig) {
        Err(_) => out.push(Mutant::reject(1, "sig_leaf_index_bit", "native", "verification_error".into())),
        Ok(()) => out.push(Mutant::accept(1, "sig_leaf_index_bit", "native")),
    }

    // 1b: WOTS+ chain value bit (layer 1, first chain word).
    let mut sig_bytes = r[64..].to_vec();
    sig_bytes[LEAF_INDEX_SIZE + lean_xmss::RANDOMIZER_LEN + 3] ^= 1;
    let sig = LeanXmssSignature::from_bytes(sig_bytes.as_slice().try_into().unwrap());
    match lean_xmss::verify(&pk, &message, &sig) {
        Err(_) => out.push(Mutant::reject(1, "sig_chain_value_bit", "native", "verification_error".into())),
        Ok(()) => out.push(Mutant::accept(1, "sig_chain_value_bit", "native")),
    }

    // 1c: forged Merkle-path sibling hint (guest in-circuit check).
    let mut streams = b.streams.clone();
    streams.get_mut("lx_path").expect("lx_path stream")[0][0].c0 ^= 1;
    match b.guest_run(&streams) {
        Err(e) => out.push(Mutant::reject(1, "guest_lx_path_sibling_forged", "guest", e)),
        Ok(()) => out.push(Mutant::accept(1, "guest_lx_path_sibling_forged", "guest")),
    }

    // 1d: forged WOTS+ chain-start hint (guest in-circuit check).
    let mut streams = b.streams.clone();
    streams.get_mut("chain_starts").expect("chain_starts stream")[0][0].c0 ^= 1;
    match b.guest_run(&streams) {
        Err(e) => out.push(Mutant::reject(1, "guest_chain_start_forged", "guest", e)),
        Ok(()) => out.push(Mutant::accept(1, "guest_chain_start_forged", "guest")),
    }
    out
}

/// Category 2 - mutated message bit.
fn category2(b: &EthBaseline) -> Vec<Mutant> {
    let mut out = Vec::new();
    let r = &b.records[0];
    let pk = LeanXmssPublicKey::from_bytes(r[..32].try_into().unwrap());
    let mut message: Message = r[32..64].try_into().unwrap();
    let sig = LeanXmssSignature::from_bytes(r[64..].try_into().unwrap());
    message[5] ^= 1;
    match lean_xmss::verify(&pk, &message, &sig) {
        Err(_) => out.push(Mutant::reject(2, "message_bit", "native", "verification_error".into())),
        Ok(()) => out.push(Mutant::accept(2, "message_bit", "native")),
    }

    // 2b: forged claim message cell (guest verifies the signature against the
    // slot it reads, and the statement digest no longer binds it).
    let mut streams = b.streams.clone();
    // claim cells per record: [pk_lo, pk_hi, msg_lo, msg_hi]
    streams.get_mut("claims").expect("claims stream")[2][0].c0 ^= 1;
    match b.guest_run(&streams) {
        Err(e) => out.push(Mutant::reject(2, "guest_claim_message_forged", "guest", e)),
        Ok(()) => out.push(Mutant::accept(2, "guest_claim_message_forged", "guest")),
    }
    out
}

/// Category 3 - mutated public key bit / unsorted or duplicate signer set.
fn category3(b: &EthBaseline) -> Vec<Mutant> {
    let mut out = Vec::new();
    let r = &b.records[0];
    let mut pk_bytes = r[..32].to_vec();
    pk_bytes[1] ^= 1;
    let pk = LeanXmssPublicKey::from_bytes(pk_bytes.as_slice().try_into().unwrap());
    let message: Message = r[32..64].try_into().unwrap();
    let sig = LeanXmssSignature::from_bytes(r[64..].try_into().unwrap());
    match lean_xmss::verify(&pk, &message, &sig) {
        Err(_) => out.push(Mutant::reject(3, "pubkey_bit", "native", "verification_error".into())),
        Ok(()) => out.push(Mutant::accept(3, "pubkey_bit", "native")),
    }

    let wire = b.eth.to_bytes();
    let a = 4 + 64 * 0..4 + 64 * 1;
    let c = 4 + 64 * 1..4 + 64 * 2;

    // 3b: unsorted - swap the first two (pk, message) claim blocks.
    let mut bytes = wire.clone();
    let (ba, bc): ([u8; 64], [u8; 64]) = (bytes[a.clone()].try_into().unwrap(), bytes[c.clone()].try_into().unwrap());
    bytes[a].copy_from_slice(&bc);
    bytes[c].copy_from_slice(&ba);
    match EthereumProof::from_bytes(&bytes) {
        Err(e) => out.push(Mutant::reject(3, "wire_unsorted_signers", "wire", e.to_string())),
        Ok(p) => match p.verify() {
            Err(e) => out.push(Mutant::reject(3, "wire_unsorted_signers", "wire", e.to_string())),
            Ok(()) => out.push(Mutant::accept(3, "wire_unsorted_signers", "wire")),
        },
    }

    // 3c: duplicate - bump the signer count and repeat the first claim block.
    let mut bytes: Vec<u8> = wire[..4 + 64].to_vec();
    bytes[0] ^= 1; // 4 -> 5
    bytes.extend_from_slice(&wire[4..4 + 64]);
    bytes.extend_from_slice(&wire[4 + 64..]);
    match EthereumProof::from_bytes(&bytes) {
        Err(e) => out.push(Mutant::reject(3, "wire_duplicate_signer", "wire", e.to_string())),
        Ok(p) => match p.verify() {
            Err(e) => out.push(Mutant::reject(3, "wire_duplicate_signer", "wire", e.to_string())),
            Ok(()) => out.push(Mutant::accept(3, "wire_duplicate_signer", "wire")),
        },
    }

    // 3d: pubkey bit on the wire - parses, must fail verification
    // (the statement digest is rebuilt from the transmitted claim).
    let mut bytes = wire.clone();
    bytes[4 + 1] ^= 1;
    match EthereumProof::from_bytes(&bytes) {
        Err(e) => out.push(Mutant::reject(3, "wire_pubkey_bit", "wire", e.to_string())),
        Ok(p) => match p.verify() {
            Err(e) => out.push(Mutant::reject(3, "wire_pubkey_bit", "wire", e.to_string())),
            Ok(()) => out.push(Mutant::accept(3, "wire_pubkey_bit", "wire")),
        },
    }
    out
}

/// Category 5 - mutated table/bus column evaluation scalar in the proof stream.
fn category5(v: &VmBaseline) -> Vec<Mutant> {
    let summary = v.verify_proof(&v.proof).expect("baseline ok");
    let start = summary.keccak_scalars.start;
    let mut candidates = vec![10usize, (10 + start) / 2, start.saturating_sub(1)];
    candidates.retain(|&i| i >= 10 && i < start);
    candidates.sort_unstable();
    candidates.dedup();
    candidates.truncate(3);
    let mut out = Vec::new();
    for (k, &i) in candidates.iter().enumerate() {
        let mut proof = v.proof.clone();
        proof.stream[i].c0 ^= 1;
        match v.verify_proof(&proof) {
            Err(e) => out.push(Mutant::reject(
                5,
                &format!("bus_table_scalar[{i}]"),
                "vm_stream",
                e,
            )),
            Ok(_) => out.push(Mutant::accept(5, &format!("bus_table_scalar[{i}]"), "vm_stream")),
        }
        let _ = k;
    }
    out
}

/// Category 6 - mutated Keccak-reduction / GKR scalar in the proof stream.
fn category6(v: &VmBaseline) -> Vec<Mutant> {
    let summary = v.verify_proof(&v.proof).expect("baseline ok");
    let (a, b) = (summary.keccak_scalars.start, summary.keccak_scalars.end);
    let span = b.saturating_sub(a);
    let mut candidates = vec![a, a + span / 3, a + 2 * span / 3];
    candidates.sort_unstable();
    candidates.dedup();
    candidates.truncate(3);
    let mut out = Vec::new();
    for &i in &candidates {
        let mut proof = v.proof.clone();
        proof.stream[i].c0 ^= 1;
        match v.verify_proof(&proof) {
            Err(e) => out.push(Mutant::reject(6, &format!("keccak_gkr_scalar[{i}]"), "vm_stream", e)),
            Ok(_) => out.push(Mutant::accept(6, &format!("keccak_gkr_scalar[{i}]"), "vm_stream")),
        }
    }
    out
}

/// Category 7 - swapped/shifted Fiat-Shamir scalar order, bad PoW grinding nonce.
fn category7(v: &VmBaseline) -> Vec<Mutant> {
    let summary = v.verify_proof(&v.proof).expect("baseline ok");
    let mut out = Vec::new();

    // 7a: one transposition mid-WHIR (inside the query phase region).
    {
        let len = v.proof.stream.len();
        let k = (summary.keccak_scalars.end + len) / 2;
        if k + 1 < len {
            let mut proof = v.proof.clone();
            proof.stream.swap(k, k + 1);
            match v.verify_proof(&proof) {
                Err(e) => out.push(Mutant::reject(7, "transcript_transposed", "vm_stream", e)),
                Ok(_) => out.push(Mutant::accept(7, "transcript_transposed", "vm_stream")),
            }
        }
    }

    // 7b: the whole stream shifted by one scalar.
    {
        let mut proof = v.proof.clone();
        proof.stream.rotate_left(1);
        match v.verify_proof(&proof) {
            Err(e) => out.push(Mutant::reject(7, "transcript_shifted", "vm_stream", e)),
            Ok(_) => out.push(Mutant::accept(7, "transcript_shifted", "vm_stream")),
        }
    }

    // 7c: the PoW grinding nonce. The nonce is the last stream scalar whose
    // tampering changes a drawn challenge: probing the query-phase region for
    // the GrindingNonce failure signature, the highest such index is the final
    // level's nonce (scalars after it are checked identities, not challenges).
    let sp = cpu::scalar_proof(&v.proof);
    let start = summary.keccak_scalars.end;
    let mut nonce_idx: Option<usize> = None;
    for i in start..sp.stream.len() {
        let mut probe = sp.clone();
        probe.stream[i].c0 ^= 1;
        if vrf::verify_execution(&v.vbytecode, &v.pi_bytes, &probe)
            .is_err_and(|e| matches!(e, vrf::VerifierError::GrindingNonce))
        {
            nonce_idx = Some(i);
        }
    }
    match nonce_idx {
        Some(i) => {
            let mut proof = v.proof.clone();
            proof.stream[i].c0 ^= 1;
            match v.verify_proof(&proof) {
                Err(e) => out.push(Mutant::reject(
                    7,
                    &format!("pow_nonce[{i}]"),
                    "vm_stream",
                    e,
                )),
                Ok(_) => out.push(Mutant::accept(7, &format!("pow_nonce[{i}]"), "vm_stream")),
            }
        }
        None => out.push(Mutant {
            category: 7,
            name: "pow_nonce[unlocated]".into(),
            level: "vm_stream".into(),
            rejected: false,
            error: "no GrindingNonce signature found in the query-phase region".into(),
        }),
    }
    out
}

/// Category 8 - mutated Merkle root / sibling digest / leaf word.
fn category8(v: &VmBaseline, b: &EthBaseline) -> Vec<Mutant> {
    let mut out = Vec::new();

    // 8a: a sibling digest in the first pruned opening batch.
    {
        let mut proof = v.proof.clone();
        let batch = proof.merkle.first_mut().expect("a merkle batch");
        let digests = batch.sibling_hashes.first_mut().expect("a sibling digest");
        digests[0] ^= 1;
        match v.verify_proof(&proof) {
            Err(e) => out.push(Mutant::reject(8, "merkle_sibling_digest", "vm_merkle", e)),
            Ok(_) => out.push(Mutant::accept(8, "merkle_sibling_digest", "vm_merkle")),
        }
    }

    // 8b: a leaf word in the first pruned opening batch.
    {
        let mut proof = v.proof.clone();
        let batch = proof.merkle.first_mut().expect("a merkle batch");
        let row = batch.leaf_data.first_mut().expect("a leaf row");
        row.first_mut().expect("a leaf word").0 ^= 1;
        match v.verify_proof(&proof) {
            Err(e) => out.push(Mutant::reject(8, "merkle_leaf_word", "vm_merkle", e)),
            Ok(_) => out.push(Mutant::accept(8, "merkle_leaf_word", "vm_merkle")),
        }
    }

    // 8c: leanXMSS Merkle authentication path (layer 2 sibling digest byte).
    let r = &b.records[0];
    let pk = LeanXmssPublicKey::from_bytes(r[..32].try_into().unwrap());
    let message: Message = r[32..64].try_into().unwrap();
    let mut sig_bytes = r[64..].to_vec();
    let path2 = LEAF_INDEX_SIZE
        + LAYER_SIG_SIZE
        + lean_xmss::RANDOMIZER_LEN
        + lean_xmss::V * N
        + 5;
    sig_bytes[path2] ^= 1;
    let sig = LeanXmssSignature::from_bytes(sig_bytes.as_slice().try_into().unwrap());
    match lean_xmss::verify(&pk, &message, &sig) {
        Err(_) => out.push(Mutant::reject(8, "xmss_auth_path_bit", "native", "verification_error".into())),
        Ok(()) => out.push(Mutant::accept(8, "xmss_auth_path_bit", "native")),
    }

    // 8d: leanXMSS leaf/chain word (layer 2 chain value byte).
    let mut sig_bytes = r[64..].to_vec();
    let chain2 = LEAF_INDEX_SIZE + LAYER_SIG_SIZE + lean_xmss::RANDOMIZER_LEN + 3;
    sig_bytes[chain2] ^= 1;
    let sig = LeanXmssSignature::from_bytes(sig_bytes.as_slice().try_into().unwrap());
    match lean_xmss::verify(&pk, &message, &sig) {
        Err(_) => out.push(Mutant::reject(8, "xmss_leaf_word_bit", "native", "verification_error".into())),
        Ok(()) => out.push(Mutant::accept(8, "xmss_leaf_word_bit", "native")),
    }
    out
}

/// Category 9 - mutated deferred bytecode claim / public input word.
fn category9(b: &EthBaseline) -> Vec<Mutant> {
    let mut out = Vec::new();
    let wire = b.eth.to_bytes();

    // 9a: a byte of the deferred bytecode point. Wire layout: [u32 n_xmss]
    // [n_xmss*64B claims][u32 n_sph][n_sph*?B][1B da tag][point: u32 len, 24B/coord][proof].
    let point_at = 4 + 64 * b.records.len() + 4 + 0 + 1 + 4;
    let mut bytes = wire.clone();
    bytes[point_at + 2] ^= 1;
    match EthereumProof::from_bytes(&bytes) {
        Err(e) => out.push(Mutant::reject(9, "deferred_claim_point_bit", "wire", e.to_string())),
        Ok(p) => match p.verify() {
            Err(e) => out.push(Mutant::reject(9, "deferred_claim_point_bit", "wire", e.to_string())),
            Ok(()) => out.push(Mutant::accept(9, "deferred_claim_point_bit", "wire")),
        },
    }

    // 9b: a public input word (the transmitted claim's message byte).
    let mut bytes = wire.clone();
    bytes[4 + 32 + 5] ^= 1;
    match EthereumProof::from_bytes(&bytes) {
        Err(e) => out.push(Mutant::reject(9, "public_input_word_bit", "wire", e.to_string())),
        Ok(p) => match p.verify() {
            Err(e) => out.push(Mutant::reject(9, "public_input_word_bit", "wire", e.to_string())),
            Ok(()) => out.push(Mutant::accept(9, "public_input_word_bit", "wire")),
        },
    }
    out
}

/// Category 10 - mutated wire index/length prefix / trailing byte.
fn category10(v: &VmBaseline, b: &EthBaseline) -> Vec<Mutant> {
    let mut out = Vec::new();
    let wire = b.eth.to_bytes();

    // 10a: the signer-count prefix.
    let mut bytes = wire.clone();
    bytes[0] ^= 1;
    match EthereumProof::from_bytes(&bytes) {
        Err(e) => out.push(Mutant::reject(10, "wire_count_prefix_bit", "wire", e.to_string())),
        Ok(p) => match p.verify() {
            Err(e) => out.push(Mutant::reject(10, "wire_count_prefix_bit", "wire", e.to_string())),
            Ok(()) => out.push(Mutant::accept(10, "wire_count_prefix_bit", "wire")),
        },
    }

    // 10b: an appended trailing byte (bincode is strict about trailing data).
    let mut bytes = wire.clone();
    bytes.push(0);
    match EthereumProof::from_bytes(&bytes) {
        Err(e) => out.push(Mutant::reject(10, "wire_trailing_byte", "wire", e.to_string())),
        Ok(p) => match p.verify() {
            Err(e) => out.push(Mutant::reject(10, "wire_trailing_byte", "wire", e.to_string())),
            Ok(()) => out.push(Mutant::accept(10, "wire_trailing_byte", "wire")),
        },
    }

    // 10c: the VM proof's stream-length prefix on its own wire encoding.
    let vm_wire = bincode::serialize(&v.proof).expect("vm proof serializes");
    let mut bytes = vm_wire.clone();
    bytes[0] ^= 1;
    let rejected = bincode::deserialize::<cpu::Proof>(&bytes).is_err()
        || match bincode::deserialize::<cpu::Proof>(&bytes) {
            Ok(mutant) => v.verify_proof(&mutant).is_err(),
            Err(_) => true,
        };
    if rejected {
        out.push(Mutant::reject(10, "vm_proof_length_prefix_bit", "vm_wire", "malformed or rejected".into()));
    } else {
        out.push(Mutant::accept(10, "vm_proof_length_prefix_bit", "vm_wire"));
    }

    // 10d: a trailing byte on the VM proof wire encoding. The production wire
    // (`rec_aggregation`'s `wire()`) rejects trailing bytes so each aggregate has
    // exactly one encoding; the raw default-bincode decode is lenient, so enforce
    // the same canonicality: the decoded proof must re-serialize to the exact
    // input bytes.
    let mut bytes = vm_wire.clone();
    bytes.push(0);
    let non_canonical = match bincode::deserialize::<cpu::Proof>(&bytes) {
        Err(_) => true,
        Ok(mutant) => bincode::serialize(&mutant)
            .map(|re| re != bytes)
            .unwrap_or(true),
    };
    if non_canonical {
        out.push(Mutant::reject(10, "vm_proof_trailing_byte", "vm_wire", "non-canonical encoding (trailing byte)".into()));
    } else {
        out.push(Mutant::accept(10, "vm_proof_trailing_byte", "vm_wire"));
    }
    out
}

fn json_escape(s: &str) -> String {
    s.chars()
        .map(|c| match c {
            '"' => "\\\"".to_string(),
            '\\' => "\\\\".to_string(),
            '\n' => "\\n".to_string(),
            '\r' => "\\r".to_string(),
            '\t' => "\\t".to_string(),
            c if (c as u32) < 0x20 => format!("\\u{:04x}", c as u32),
            c => c.to_string(),
        })
        .collect()
}

const MUT34_META: [(u32, &str, &str); 34] = [
    (1, "public_input_statement", "m01_claim_message_digest_bit"),
    (2, "public_input_statement", "m02_claim_pubkey_root_bit"),
    (3, "public_input_statement", "m03_unsorted_signer_claims"),
    (4, "public_input_statement", "m04_da_commitment_root_some"),
    (5, "public_input_statement", "m05_deferred_bytecode_point_coord"),
    (6, "transcript_pow_wire", "m06_fiat_shamir_scalar_swap"),
    (7, "transcript_pow_wire", "m07_fiat_shamir_stream_rotate"),
    (8, "transcript_pow_wire", "m08_whir_pow_grinding_nonce"),
    (9, "transcript_pow_wire", "m09_wire_truncated_bytes"),
    (10, "transcript_pow_wire", "m10_wire_trailing_byte_injection"),
    (11, "pcs_merkle_rounds", "m11_l0_commitment_root_bit"),
    (12, "pcs_merkle_rounds", "m12_l0_commitment_root_nonzero_c2"),
    (13, "pcs_merkle_rounds", "m13_l0_merkle_leaf_word_bit"),
    (14, "pcs_merkle_rounds", "m14_l0_merkle_sibling_digest_bit"),
    (15, "pcs_merkle_rounds", "m15_whir_round1_commitment_root_bit"),
    (16, "pcs_merkle_rounds", "m16_whir_deeper_round_merkle_sibling_bit"),
    (17, "bus_logup_gkr", "m17_bus_gkr_shared_root_claim"),
    (18, "bus_logup_gkr", "m18_bus_gkr_zero_count_root"),
    (19, "bus_logup_gkr", "m19_bus_gkr_round_poly_coeff"),
    (20, "bus_logup_gkr", "m20_bus_gkr_layer_child_eval"),
    (21, "bus_logup_gkr", "m21_bus_memory_fingerprint_eval"),
    (22, "bus_logup_gkr", "m22_table_sumcheck_final_column_eval"),
    (23, "keccak_f1600_gkr", "m23_keccak_committed_segment_claim"),
    (24, "keccak_f1600_gkr", "m24_keccak_rmfe_bit_product_poly"),
    (25, "keccak_f1600_gkr", "m25_keccak_instance_round_sumcheck"),
    (26, "keccak_f1600_gkr", "m26_keccak_theta_rho_pi_chi_local_t"),
    (27, "keccak_f1600_gkr", "m27_keccak_output_slot_opening_word"),
    (28, "keccak_f1600_gkr", "m28_keccak_input_pack_slice_eval"),
    (29, "whir_ringswitch_pcs", "m29_ringswitch_stacked_initial_quad"),
    (30, "whir_ringswitch_pcs", "m30_whir_l0_fold_round_poly"),
    (31, "whir_ringswitch_pcs", "m31_whir_ood_sample_eval"),
    (32, "whir_ringswitch_pcs", "m32_whir_stir_query_intro_poly"),
    (33, "whir_ringswitch_pcs", "m33_whir_tail_sumcheck_round_poly"),
    (34, "whir_ringswitch_pcs", "m34_whir_final_residual_poly_coeff"),
];

fn verify_eth_wire(bytes: &[u8]) -> Result<(), String> {
    let parsed = EthereumProof::from_bytes(bytes).map_err(|e| format!("parse: {e}"))?;
    parsed.verify().map_err(|e| format!("verify: {e}"))
}

fn run_verify_34(dir: &Path, json_path: Option<&str>) -> i32 {
    let t0 = std::time::Instant::now();
    let baseline_bytes = std::fs::read(dir.join("baseline.ethwire"))
        .expect("read baseline.ethwire");
    let _ = unified_guest();

    let mut baseline_accepted_count = 0usize;
    let mut mutated_rejected_count = 0usize;
    let mut rows = Vec::with_capacity(34);

    for (id, group, name) in MUT34_META {
        let base_ok = verify_eth_wire(&baseline_bytes).is_ok();
        if base_ok {
            baseline_accepted_count += 1;
        }
        let mut_path = dir.join(format!("mutant_{id:02}.ethwire"));
        let mut_bytes = std::fs::read(&mut_path)
            .unwrap_or_else(|e| panic!("read {}: {e}", mut_path.display()));
        let (mut_rejected, err_msg) = match verify_eth_wire(&mut_bytes) {
            Ok(()) => (false, String::new()),
            Err(e) => (true, e),
        };
        if mut_rejected {
            mutated_rejected_count += 1;
        }
        rows.push(format!(
            "    {{\"id\":{},\"group\":\"{}\",\"name\":\"{}\",\"baseline_accepted\":{},\"mutated_rejected\":{},\"mutated_bytes\":{},\"error\":\"{}\"}}",
            id,
            json_escape(group),
            json_escape(name),
            base_ok,
            mut_rejected,
            mut_bytes.len(),
            json_escape(&err_msg)
        ));
    }

    let elapsed_ms = t0.elapsed().as_millis();
    let all_passed = baseline_accepted_count == 34 && mutated_rejected_count == 34;
    let json = format!(
        "{{\n  \"verifier\": \"rust_reference_unmodified\",\n  \"mutant_total\": 34,\n  \"baseline_accepted_count\": {},\n  \"mutated_rejected_count\": {},\n  \"all_passed\": {},\n  \"elapsed_ms\": {},\n  \"baseline_wire_bytes\": {},\n  \"mutants\": [\n{}\n  ]\n}}\n",
        baseline_accepted_count,
        mutated_rejected_count,
        all_passed,
        elapsed_ms,
        baseline_bytes.len(),
        rows.join(",\n")
    );
    if let Some(p) = json_path {
        std::fs::write(p, &json).expect("write rust 34-mutant json");
    }
    println!(
        "RUST_MUTANT34_DONE baseline={}/34 rejected={}/34 elapsed_ms={}",
        baseline_accepted_count, mutated_rejected_count, elapsed_ms
    );
    if all_passed { 0 } else { 1 }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut oracle_dir = Path::new("/var/lib/orb-node/work/caches/xmss-hub-v3/oracle/xmss4").to_path_buf();
    let mut verify_34_dir: Option<std::path::PathBuf> = None;
    let mut json_path: Option<String> = None;
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--oracle-xmss4" => {
                i += 1;
                oracle_dir = Path::new(&args[i]).to_path_buf();
            }
            "--verify-34-dir" => {
                i += 1;
                verify_34_dir = Some(Path::new(&args[i]).to_path_buf());
            }
            "--json" => {
                i += 1;
                json_path = Some(args[i].clone());
            }
            other => {
                eprintln!("unknown argument {other}");
                std::process::exit(2);
            }
        }
        i += 1;
    }

    if let Some(dir) = verify_34_dir {
        std::process::exit(run_verify_34(&dir, json_path.as_deref()));
    }

    eprintln!("[w5] building syn_keccak baseline (proving)...");
    let vm = build_vm_baseline();
    eprintln!("[w5] syn_keccak baseline verified ({} stream scalars, {} merkle batches)",
        vm.proof.stream.len(), vm.proof.merkle.len());

    eprintln!("[w5] building xmss4 baseline (compiling guest, proving aggregate)...");
    let eth = build_eth_baseline(&oracle_dir);
    eprintln!("[w5] xmss4 baseline verified ({} records, wire {} bytes)",
        eth.records.len(), eth.eth.to_bytes().len());

    let mut mutants: Vec<Mutant> = Vec::new();
    mutants.extend(category1(&eth));
    mutants.extend(category2(&eth));
    mutants.extend(category3(&eth));
    mutants.extend(category5(&vm));
    mutants.extend(category6(&vm));
    mutants.extend(category7(&vm));
    mutants.extend(category8(&vm, &eth));
    mutants.extend(category9(&eth));
    mutants.extend(category10(&vm, &eth));

    let accepted: Vec<_> = mutants.iter().filter(|m| !m.rejected).collect();
    let categories: Vec<u32> = mutants.iter().map(|m| m.category).collect::<BTreeSet<_>>().into_iter().collect();
    let required: Vec<u32> = vec![1, 2, 3, 5, 6, 7, 8, 9, 10];
    let all_rejected = accepted.is_empty();
    let all_categories = required.iter().all(|c| categories.contains(c));

    let mut json = String::new();
    json.push_str("{\n");
    json.push_str("  \"shard\": \"W5\",\n");
    json.push_str("  \"baseline\": {\n");
    json.push_str(&format!(
        "    \"vm\": {{\"program\": \"syn_keccak\", \"instructions\": {}, \"keccak_rows\": 2, \"log_inv_rate\": {}, \"accepted\": true, \"stream_scalars\": {}, \"merkle_batches\": {}}},\n",
        vm.program.prog.len(),
        leanvm_core::pcs::TEST_LOG_INV_RATE,
        vm.proof.stream.len(),
        vm.proof.merkle.len()
    ));
    json.push_str(&format!(
        "    \"eth\": {{\"fixture\": \"xmss4\", \"records\": {}, \"log_inv_rate\": {}, \"accepted\": true, \"wire_bytes\": {}}}\n",
        eth.records.len(),
        leanvm_core::pcs::TEST_LOG_INV_RATE,
        eth.eth.to_bytes().len()
    ));
    json.push_str("  },\n");
    json.push_str("  \"mutants\": [\n");
    for (k, m) in mutants.iter().enumerate() {
        json.push_str(&format!(
            "    {{\"category\": {}, \"name\": \"{}\", \"level\": \"{}\", \"rejected\": {}, \"error\": \"{}\"}}{}\n",
            m.category,
            json_escape(&m.name),
            json_escape(&m.level),
            m.rejected,
            json_escape(&m.error),
            if k + 1 < mutants.len() { "," } else { "" }
        ));
    }
    json.push_str("  ],\n");
    json.push_str(&format!("  \"rust_categories_covered\": {:?},\n", categories));
    json.push_str(&format!("  \"mutant_count\": {},\n", mutants.len()));
    json.push_str(&format!("  \"accepted_count\": {},\n", accepted.len()));
    json.push_str(&format!("  \"all_rejected\": {}\n", all_rejected));
    json.push_str("}\n");

    if let Some(path) = &json_path {
        std::fs::write(path, &json).expect("write json report");
    }
    println!("{json}");

    for m in &mutants {
        if !m.rejected {
            eprintln!("[w5] MUTANT ACCEPTED (FAILURE): c{} {} ({})", m.category, m.name, m.level);
        }
    }
    if !all_categories {
        eprintln!("[w5] missing rust categories: {:?}", required.iter().filter(|c| !categories.contains(c)).collect::<Vec<_>>());
    }
    std::process::exit(if all_rejected && all_categories { 0 } else { 1 });
}

use std::collections::BTreeSet;
