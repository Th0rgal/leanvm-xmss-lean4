//! The W4 end-to-end oracle CLI: proof-stream trace export, Rust/Lean VM and
//! aggregate verification, fresh-input generation, and the Rust side of the
//! Tier B alternating benchmark.

use fiat_shamir::FiatShamirState;
use leanvm_core::cpu::layout::{
    KeccakLane, MEM_HI, MEM_LO, MEM_TOP, QKECCAK, keccak_value, layout, schema,
};
use leanvm_core::cpu::{DerefMode, Op, Program, fs_seed, prove, public_input_bytes, scalar_proof, verify};
use leanvm_core::{leaf, tables};
use primitives::field::{F64, F192};
use primitives::hash::STATE_LANES;
use primitives::multilinear::interp_k;
use signatures::lean_xmss::{self, LeanXmssPublicKey, LeanXmssSignature};
use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::path::Path;
use std::time::Duration;
use bincode::Options as _;

mod aggregation {
    pub fn count(n: usize) -> primitives::field::F192 {
        cells::count(n)
    }
    pub fn pack(bytes: &[u8]) -> primitives::field::F192 {
        cells::pack_16_bytes(bytes)
    }
    pub mod error {
        #[derive(Debug)]
        pub enum AggregationError {
            MalformedRawSignature,
        }
    }
    #[path = "/var/lib/orb-node/work/caches/xmss-hub-v3/references/leanVM/crates/rec_aggregation/src/aggregation/cells.rs"]
    pub mod cells;
    #[path = "/var/lib/orb-node/work/caches/xmss-hub-v3/references/leanVM/crates/rec_aggregation/src/aggregation/hints.rs"]
    pub mod hints;
    pub fn xmss(
        pk: &signatures::lean_xmss::LeanXmssPublicKey,
        sig: &signatures::lean_xmss::LeanXmssSignature,
        message: &[u8; 32],
    ) -> Vec<(&'static str, Vec<primitives::field::F192>)> {
        hints::lean_xmss_hints(pk, sig, message).unwrap()
    }
}

fn word(out: &mut Vec<u8>, value: F192) {
    for x in [value.c0, value.c1, value.c2] {
        out.extend(x.to_le_bytes());
    }
}

fn entry(out: &mut Vec<u8>, name: &str, values: &[F192]) {
    out.extend((name.len() as u32).to_le_bytes());
    out.extend(name.as_bytes());
    out.extend((values.len() as u32).to_le_bytes());
    for &v in values {
        word(out, v);
    }
}

fn count(n: usize) -> F192 {
    aggregation::count(n)
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn read_hints(path: &str) -> BTreeMap<String, Vec<Vec<F192>>> {
    let hints = fs::read(path).unwrap();
    let mut streams = BTreeMap::new();
    let mut cursor = 0;
    while cursor < hints.len() {
        let len = u32::from_le_bytes(hints[cursor..cursor + 4].try_into().unwrap()) as usize;
        cursor += 4;
        let name = String::from_utf8(hints[cursor..cursor + len].to_vec()).unwrap();
        cursor += len;
        let n = u32::from_le_bytes(hints[cursor..cursor + 4].try_into().unwrap()) as usize;
        cursor += 4;
        let mut values = Vec::new();
        for _ in 0..n {
            let a = u64::from_le_bytes(hints[cursor..cursor + 8].try_into().unwrap());
            let b = u64::from_le_bytes(hints[cursor + 8..cursor + 16].try_into().unwrap());
            let c = u64::from_le_bytes(hints[cursor + 16..cursor + 24].try_into().unwrap());
            cursor += 24;
            values.push(F192::new(a, b, c));
        }
        streams.entry(name).or_insert_with(Vec::new).push(values);
    }
    streams
}

fn set_k(offset: u32, value: u64) -> Op {
    Op::Set { o: offset, k: F192::new(value, 0, 0) }
}

fn pad_pow2(mut ops: Vec<Op>) -> Vec<Op> {
    let target = (ops.len() + 1).next_power_of_two().max(2);
    while ops.len() + 1 < target {
        ops.push(set_k(0, 0));
    }
    ops.push(Op::Xor { a: 0, b: 0, c: 0 });
    ops
}

fn synthetic(name: &str) -> (Vec<Op>, u32, [F192; 2]) {
    let pi = [F192::ZERO, F192::ZERO];
    let (ops, frame) = match name {
        "syn_tiny" => (
            vec![
                set_k(2, 5),
                set_k(3, 9),
                Op::Xor { a: 2, b: 3, c: 4 },
                set_k(5, 7),
                Op::Mul { a: 4, b: 5, c: 6 },
                set_k(8, 1),
                set_k(9, 0),
                set_k(10, 0),
            ],
            16,
        ),
        "syn_jump" => (
            vec![
                set_k(2, 1),
                set_k(3, 32),
                set_k(4, 1),
                Op::Jump { oc: 2, od: 3, of: 4 },
                set_k(5, 9),
                set_k(6, 0),
                set_k(7, 1),
                Op::Jump { oc: 6, od: 7, of: 4 },
            ],
            16,
        ),
        "syn_deref" => (
            vec![
                set_k(2, 64),
                set_k(3, 11),
                Op::Deref { o1: 2, o2: 0, o3: 3, mode: DerefMode::Cell },
                Op::Deref { o1: 2, o2: 1, o3: 0, mode: DerefMode::Pc },
                Op::Deref { o1: 2, o2: 2, o3: 0, mode: DerefMode::Fp },
                set_k(12, 0),
                set_k(13, 0),
                set_k(14, 0),
            ],
            16,
        ),
        _ => (
            vec![
                set_k(2, 0x1111),
                set_k(3, 0x2222),
                set_k(4, 0),
                set_k(5, 0),
                set_k(6, 0),
                set_k(7, 0),
                set_k(8, 0),
                set_k(9, 0),
                set_k(10, 0),
                set_k(11, 0),
                set_k(12, 0),
                set_k(13, 0),
                set_k(14, 0),
                Op::Keccak {
                    m: [2, 3, 4, 5],
                    tail: 6,
                    b8: 10,
                    cap: 11,
                    out: 16,
                    in_odd: false,
                    out_odd: true,
                },
                Op::Keccak {
                    m: [16, 17, 18, 19],
                    tail: 20,
                    b8: 24,
                    cap: 25,
                    out: 30,
                    in_odd: true,
                    out_odd: false,
                },
            ],
            64,
        ),
    };
    (pad_pow2(ops), frame, pi)
}

fn fixture(dir: &str) -> (Program, [F192; 2]) {
    let mut program = rec_aggregation::aggregation::unified_guest().clone();
    for (name, entries) in read_hints(&format!("{dir}/hints.bin")) {
        program.set_witness(name, entries);
    }
    let statement = fs::read(format!("{dir}/statement.bin")).unwrap();
    let pi = [
        F192::new(
            u64::from_le_bytes(statement[0..8].try_into().unwrap()),
            u64::from_le_bytes(statement[8..16].try_into().unwrap()),
            0,
        ),
        F192::new(
            u64::from_le_bytes(statement[16..24].try_into().unwrap()),
            u64::from_le_bytes(statement[24..32].try_into().unwrap()),
            0,
        ),
    ];
    (program, pi)
}

const RECORD: usize = 32 + 32 + 2404;

fn fixture_records(dir: &str) -> Vec<(LeanXmssPublicKey, lean_xmss::Message, LeanXmssSignature)> {
    let raw = fs::read(format!("{dir}/xmss-inputs.bin")).unwrap();
    assert_eq!(raw.len() % RECORD, 0, "raw inputs are whole records");
    raw.chunks_exact(RECORD)
        .map(|r| {
            (
                LeanXmssPublicKey::from_bytes(r[..32].try_into().unwrap()),
                r[32..64].try_into().unwrap(),
                LeanXmssSignature::from_bytes(r[64..].try_into().unwrap()),
            )
        })
        .collect()
}

struct ReplayReader<'a> {
    sponge: FiatShamirState,
    stream: &'a [F192],
    cursor: usize,
}

impl<'a> ReplayReader<'a> {
    fn next_scalar(&mut self) -> F192 {
        let v = self.stream[self.cursor];
        self.cursor += 1;
        self.sponge.observe(v);
        v
    }

    fn next_scalars(&mut self, n: usize) -> Vec<F192> {
        (0..n).map(|_| self.next_scalar()).collect()
    }

    fn sample(&mut self) -> F192 {
        self.sponge.sample()
    }

    fn samples(&mut self, n: usize) -> Vec<F192> {
        (0..n).map(|_| self.sample()).collect()
    }
}

// The WHIR ladder constants, mirroring `verifier::whir` (private there).
const INITIAL_FOLDING_FACTOR: usize = 6;
const SUBSEQUENT_FOLDING_FACTOR: usize = 4;
const RS_DOMAIN_INITIAL_REDUCTION_FACTOR: usize = 3;
const RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR: usize = 1;
const RESIDUAL_MAX_LOG: usize = 5;
const MIN_STACKED_LOG: usize = 15;

#[rustfmt::skip]
const WHIR_QUERIES: [[&[usize]; 14]; 4] = [
    [&[222,55], &[223,56,30], &[223,56,31], &[223,56,32], &[223,56,32], &[223,56,32,22], &[223,56,32,22], &[224,56,32,23], &[224,56,32,23], &[224,56,32,23,17], &[224,56,32,23,17], &[224,56,32,23,18], &[225,56,32,23,18], &[225,56,32,23,18,14]],
    [&[111,45], &[112,45,27], &[112,45,28], &[112,45,28], &[112,45,28], &[112,45,28,20], &[112,45,28,20], &[112,45,28,21], &[112,45,28,21], &[112,45,28,21,16], &[112,45,28,21,16], &[112,45,28,21,16], &[112,45,28,21,16], &[112,45,28,21,16,13]],
    [&[75,37], &[75,37,24], &[75,37,25], &[75,38,25], &[75,38,25], &[75,38,25,18], &[75,38,25,19], &[75,38,25,19], &[75,38,25,19], &[75,38,25,19,15], &[75,38,25,19,15], &[75,38,25,19,15], &[75,38,25,19,15], &[75,38,25,19,15,13]],
    [&[56,32], &[56,32,22], &[56,32,22], &[56,32,23], &[56,32,23], &[56,32,23,17], &[56,32,23,17], &[56,32,23,18], &[56,32,23,18], &[56,32,23,18,14], &[56,32,23,18,14], &[56,32,23,18,14], &[56,32,23,18,15], &[56,32,23,18,15,12]],
];

/// The WHIR ladder at `log_n` and `log_inv_rate`: folds, per-level rates,
/// queries, the final message log, and the whole phase's scalar count.
fn whir_ladder(log_n: usize, log_inv_rate: usize) -> (usize, Vec<usize>, Vec<usize>, Vec<usize>, usize) {
    let mut folds = vec![INITIAL_FOLDING_FACTOR];
    let mut log_inv_rates = vec![log_inv_rate];
    let mut remaining = log_n - INITIAL_FOLDING_FACTOR;
    while remaining > RESIDUAL_MAX_LOG {
        let reduction = if folds.len() == 1 {
            RS_DOMAIN_INITIAL_REDUCTION_FACTOR
        } else {
            RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR
        };
        log_inv_rates.push(log_inv_rates[log_inv_rates.len() - 1] + folds[folds.len() - 1] - reduction);
        let fold = SUBSEQUENT_FOLDING_FACTOR.min(remaining);
        remaining -= fold;
        folds.push(fold);
    }
    let queries = WHIR_QUERIES[log_inv_rate - 1][log_n - MIN_STACKED_LOG];
    assert_eq!(queries.len(), folds.len(), "query ladder matches the fold ladder");
    let levels = folds.len();
    let mut scalars = 2; // the opening sumcheck's first round poly
    let mut total_folds = 0;
    for (level, &fold_count) in folds.iter().enumerate() {
        total_folds += fold_count;
        let message_log = log_n - total_folds;
        scalars += fold_count * 2; // one round poly per fold challenge
        scalars += 1; // the grinding nonce
        scalars += 2; // the level's intro round poly
        if level == levels - 1 {
            scalars += 1 << message_log; // the residual
            scalars += (message_log - 1) * 2; // the tail round polys
        } else {
            scalars += 5; // next root halves, the OOD value, its intro round poly
        }
    }
    (scalars, folds, log_inv_rates, queries.to_vec(), log_n - total_folds)
}

struct Phase {
    name: &'static str,
    scalars: usize,
}

struct Trace {
    case: String,
    log_inv_rate: usize,
    log_n: usize,
    placed: u64,
    stream_len: usize,
    merkle_batches: usize,
    stream_keccak256: String,
    phases: Vec<Phase>,
    bus_scalars: usize,
    whir_scalars: usize,
    whir_rounds: Vec<usize>,
    whir_folds: Vec<usize>,
    whir_rates: Vec<usize>,
    whir_queries: Vec<usize>,
    whir_final_message_log: usize,
    batch_stats: Vec<(usize, usize, usize)>,
    merkle_bytes: usize,
    proof_size: usize,
    ethereum_proof_wire_bytes: Option<usize>,
}

fn wire_opts() -> impl bincode::Options {
    bincode::DefaultOptions::new().with_fixint_encoding()
}

fn stream_bytes(stream: &[F192]) -> Vec<u8> {
    let mut out = Vec::with_capacity(stream.len() * 24);
    for v in stream {
        word(&mut out, *v);
    }
    out
}

fn hash_e(words: &[F192]) -> String {
    let mut preimage = Vec::with_capacity(words.len() * 24);
    for w in words {
        for limb in [w.c0, w.c1, w.c2] {
            preimage.extend_from_slice(&limb.to_le_bytes());
        }
    }
    hex(&primitives::hash::hash(&preimage))
}

fn build_trace(case: &str, program: &Program, pi: [F192; 2]) -> (Trace, String) {
    let (proof, stats) = prove(program, pi, 1).expect("prove");
    let summary = verify(program, &pi, &proof).expect("verify");
    let stream_hash = hex(&primitives::hash::hash(&stream_bytes(&proof.stream)));

    let seed = fs_seed(program);
    let mut iv = [F64::ZERO; 4];
    for (index, word_val) in iv.iter_mut().enumerate() {
        *word_val = F64(if index % 2 == 0 { seed[index / 2].c0 } else { seed[index / 2].c1 });
    }
    let public_words = public_input_bytes(&pi);
    let mut public_input = [F64::ZERO; 4];
    for (index, chunk) in public_words.chunks_exact(8).enumerate() {
        public_input[index] = F64(u64::from_le_bytes(chunk.try_into().unwrap()));
    }
    let mut reader = ReplayReader {
        sponge: FiatShamirState::new(iv, public_input),
        stream: &proof.stream,
        cursor: 0,
    };
    let mut phases = Vec::new();

    let announce = reader.next_scalars(2 + tables::N_TABLES);
    phases.push(Phase { name: "announce", scalars: 2 + tables::N_TABLES });
    let _root = reader.next_scalars(2);
    phases.push(Phase { name: "l0_root", scalars: 2 });
    let l = layout(&program.prog, stats.log_mem, stats.rows, pi);
    let log_bytecode = program.prog.len().trailing_zeros() as usize;

    let _alphas = reader.samples(4);
    let _beta = reader.sample();

    let mut bus_gkr = 0;
    let mut point: Vec<F192> = Vec::new();
    let _shared = reader.next_scalar();
    let _count_scalar = reader.next_scalar();
    bus_gkr += 2;
    let push_lay = leaf::layout(&l.push);
    let mut layer = push_lay.mu;
    while layer > 0 {
        let step = if layer % 2 == 1 { 1 } else { 2 };
        let _combiner = reader.sample();
        let degree = (1usize << step) + 1;
        let mut x = Vec::with_capacity(point.len());
        for _ in 0..point.len() {
            let _coeffs = reader.next_scalars(degree - 1);
            bus_gkr += degree - 1;
            x.push(reader.sample());
        }
        let _c0 = reader.next_scalars(1 << step);
        let _c1 = reader.next_scalars(1 << step);
        let _c2 = reader.next_scalars(1 << step);
        bus_gkr += 3 * (1 << step);
        let y = reader.samples(step);
        point = [y, x].concat();
        layer -= step;
    }
    phases.push(Phase { name: "bus_gkr", scalars: bus_gkr });

    let memory_low = point[..stats.log_mem].to_vec();
    let bytecode_low = point[..log_bytecode].to_vec();
    let mem_vals = reader.next_scalars(3);
    let mem_final = reader.next_scalar();
    let bc_final = reader.next_scalar();
    phases.push(Phase { name: "bus_memory", scalars: 5 });

    let mut claims: Vec<(usize, Vec<F192>, F192)> = vec![
        (MEM_LO, memory_low.clone(), mem_vals[0]),
        (MEM_HI, memory_low.clone(), mem_vals[1]),
        (MEM_TOP, memory_low.clone(), mem_vals[2]),
        (3, memory_low, mem_final),
        (4, bytecode_low, bc_final),
    ];

    let _xi = reader.sample();
    let n_rounds = l.taus.into_iter().max().unwrap_or(0);
    let mut constraints = 0;
    let mut challenges = Vec::with_capacity(n_rounds);
    for _ in 0..n_rounds {
        let _coeffs = reader.next_scalars(3);
        constraints += 3;
        challenges.push(reader.sample());
    }
    phases.push(Phase { name: "constraints_scalars", scalars: constraints });
    let sumcheck_point: Vec<F192> = challenges.into_iter().rev().collect();

    let sch = schema();
    let mut table_evals = 0;
    let mut table_eval_list = Vec::with_capacity(tables::N_TABLES);
    for (t, table) in tables::tables().iter().enumerate() {
        let chi = sumcheck_point[..l.taus[t]].to_vec();
        let evals = reader.next_scalars(table.n_committed_columns());
        table_evals += table.n_committed_columns();
        for (c, &val) in evals.iter().enumerate() {
            let col = sch.base[t] + c;
            if let Some(KeccakLane::Output(_)) = keccak_value(col) {
                continue;
            }
            claims.push((col, chi.clone(), val));
        }
        table_eval_list.push((chi, evals));
    }
    phases.push(Phase { name: "table_evals", scalars: table_evals });

    let r_pi = reader.sample();
    phases.push(Phase { name: "r_pi", scalars: 0 });
    assert_eq!(
        reader.cursor, summary.keccak_scalars.start,
        "the r_pi boundary must open the Keccak phase"
    );

    let keccak_n = summary.keccak_scalars.len();
    reader.next_scalars(keccak_n);
    phases.push(Phase { name: "keccak_scalars", scalars: keccak_n });
    phases.push(Phase { name: "ring_switch_scalars", scalars: 0 });
    assert_eq!(reader.cursor, summary.keccak_scalars.end, "the ring switch reads no scalars");

    // The sponge state is irrelevant past this point: the WHIR phase is walked
    // by count only, its ladder a function of the announced shape alone.
    let log_n = l.shape.mu;
    let (whir_n, folds, rates, queries, final_message_log) = whir_ladder(log_n, summary.log_inv_rate);
    phases.push(Phase { name: "whir_scalars", scalars: whir_n });
    let whir_start = reader.cursor;
    reader.cursor += whir_n;
    assert_eq!(
        reader.cursor, proof.stream.len(),
        "the WHIR count must close the stream exactly"
    );
    assert_eq!(whir_start, summary.keccak_scalars.end);

    let vproof = scalar_proof(&proof);
    assert_eq!(
        match &vproof.merkle_openings { verifier::MerkleOpenings::Pruned(b) => b.len(), _ => usize::MAX },
        folds.len(),
        "one Merkle batch per WHIR level"
    );
    let batches = match &vproof.merkle_openings {
        verifier::MerkleOpenings::Pruned(b) => b.clone(),
        _ => Vec::new(),
    };
    let batch_stats: Vec<(usize, usize, usize)> = batches
        .iter()
        .map(|batch| {
            let leaf_words: usize = batch.leaf_data.iter().map(|row| row.len()).sum();
            let hashes = batch.sibling_hashes.len();
            (batch.leaf_data.len(), leaf_words, hashes)
        })
        .collect();

    let whir_rounds: Vec<usize> = {
        let mut total_folds = 0;
        folds
            .iter()
            .enumerate()
            .map(|(level, &fold_count)| {
                total_folds += fold_count;
                let tail = if level == folds.len() - 1 { log_n - total_folds } else { 0 };
                fold_count + 1 + tail
            })
            .collect()
    };
    let proof_size = wire_opts()
        .serialize(&proof)
        .expect("a CPU proof serializes")
        .len();
    let merkle_bytes: usize = batch_stats
        .iter()
        .map(|&(_, leaf_words, hashes)| leaf_words * 8 + hashes * 32)
        .sum();

    let _ = r_pi;
    let trace = Trace {
        case: case.to_string(),
        log_inv_rate: summary.log_inv_rate,
        log_n,
        placed: l.shape.committed_len() as u64,
        stream_len: proof.stream.len(),
        merkle_batches: batch_stats.len(),
        stream_keccak256: stream_hash,
        phases,
        bus_scalars: bus_gkr + 5,
        whir_scalars: whir_n,
        whir_rounds,
        whir_folds: folds,
        whir_rates: rates,
        whir_queries: queries,
        whir_final_message_log: final_message_log,
        batch_stats,
        merkle_bytes,
        proof_size,
        ethereum_proof_wire_bytes: None,
    };
    let checksum = {
        let mut acc = String::new();
        for p in &trace.phases {
            acc.push_str(&format!("{}={},", p.name, p.scalars));
        }
        acc
    };
    (trace, checksum)
}

fn trace_json(trace: &Trace) -> String {
    let mut out = String::new();
    out.push_str("{\n");
    out.push_str(&format!("  \"case\": \"{}\",\n", trace.case));
    out.push_str(&format!("  \"log_inv_rate\": {},\n", trace.log_inv_rate));
    out.push_str(&format!("  \"log_n\": {},\n", trace.log_n));
    out.push_str(&format!("  \"placed\": {},\n", trace.placed));
    out.push_str(&format!("  \"stream_len\": {},\n", trace.stream_len));
    out.push_str(&format!("  \"merkle_batches\": {},\n", trace.merkle_batches));
    out.push_str(&format!("  \"bus_scalars\": {},\n", trace.bus_scalars));
    out.push_str(&format!("  \"stream_keccak256\": \"{}\",\n", trace.stream_keccak256));
    out.push_str("  \"phases\": [\n");
    for (i, p) in trace.phases.iter().enumerate() {
        out.push_str(&format!(
            "    {{\"name\": \"{}\", \"scalars\": {}}}{}\n",
            p.name,
            p.scalars,
            if i + 1 < trace.phases.len() { "," } else { "" }
        ));
    }
    out.push_str("  ],\n");
    out.push_str("  \"whir\": {\n");
    out.push_str(&format!("    \"scalars\": {},\n", trace.whir_scalars));
    out.push_str(&format!(
        "    \"rounds\": [{}],\n",
        trace.whir_rounds.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", ")
    ));
    out.push_str(&format!(
        "    \"folds\": [{}],\n",
        trace.whir_folds.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", ")
    ));
    out.push_str(&format!(
        "    \"log_inv_rates\": [{}],\n",
        trace.whir_rates.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", ")
    ));
    out.push_str(&format!(
        "    \"queries\": [{}],\n",
        trace.whir_queries.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", ")
    ));
    out.push_str(&format!("    \"final_message_log\": {}\n", trace.whir_final_message_log));
    out.push_str("  },\n");
    out.push_str("  \"merkle_batches_detail\": [\n");
    for (i, (rows, leaf_words, hashes)) in trace.batch_stats.iter().enumerate() {
        out.push_str(&format!(
            "    {{\"rows\": {}, \"leaf_words\": {}, \"sibling_hashes\": {}, \"bytes\": {}}}{}\n",
            rows,
            leaf_words,
            hashes,
            leaf_words * 8 + hashes * 32,
            if i + 1 < trace.batch_stats.len() { "," } else { "" }
        ));
    }
    out.push_str("  ],\n");
    out.push_str(&format!("  \"merkle_bytes\": {},\n", trace.merkle_bytes));
    out.push_str(&format!("  \"proof_size\": {},\n", trace.proof_size));
    match trace.ethereum_proof_wire_bytes {
        Some(bytes) => out.push_str(&format!("  \"ethereum_proof_wire_bytes\": {},\n", bytes)),
        None => out.push_str("  \"ethereum_proof_wire_bytes\": null,\n"),
    }
    let total: usize = trace.phases.iter().map(|p| p.scalars).sum();
    out.push_str(&format!("  \"phase_total\": {},\n", total));
    out.push_str("  \"stream_consumed_exactly\": true,\n");
    out.push_str("  \"batches_consumed_exactly\": true\n");
    out.push_str("}\n");
    out
}

fn load_case(spec: &str) -> (String, Program, [F192; 2]) {
    if let Some(name) = spec.strip_prefix("syn:") {
        let (ops, frame, pi) = synthetic(name);
        let program = Program::assemble(ops, Default::default(), frame);
        (name.to_string(), program, pi)
    } else {
        let (program, pi) = fixture(spec);
        let case = Path::new(spec).file_name().unwrap().to_string_lossy().to_string();
        (case, program, pi)
    }
}

fn trace_for(spec: &str) -> Trace {
    let (case, program, pi) = load_case(spec);
    let (mut trace, _) = build_trace(&case, &program, pi);
    if !spec.starts_with("syn:") {
        leanvm_core::init_prover();
        let records = fixture_records(spec);
        let (proof, _) = rec_aggregation::aggregate_with_stats(&[], records, vec![], &[], None, trace.log_inv_rate)
            .expect("aggregate for the Ethereum wire size");
        trace.ethereum_proof_wire_bytes = Some(proof.to_bytes_without_pubkeys().len());
    }
    trace
}

fn cmd_export_trace(spec: &str, out: &str) {
    let trace = trace_for(spec);
    let case = trace.case.clone();
    let json = trace_json(&trace);
    if out == "-" {
        print!("{json}");
    } else {
        fs::write(out, json).unwrap();
        println!("TRACE_EXPORTED|case={case}|path={out}|stream_len={}|phases={}|merkle_bytes={}|proof_size={}", trace.stream_len, trace.phases.len(), trace.merkle_bytes, trace.proof_size);
    }
}

fn cmd_verify_trace(spec: &str, trace_path: &str) {
    let trace = trace_for(spec);
    let case = trace.case.clone();
    let json = trace_json(&trace);
    let recorded = fs::read_to_string(trace_path).unwrap();
    if json != recorded {
        eprintln!("TRACE_MISMATCH|case={case}");
        for (a, b) in json.lines().zip(recorded.lines()) {
            if a != b {
                eprintln!("  regenerated: {a}");
                eprintln!("  recorded:    {b}");
            }
        }
        std::process::exit(1);
    }
    println!(
        "TRACE_VERIFIED|case={case}|stream_len={}|log_n={}|phases={}|batches={}",
        trace.stream_len, trace.log_n, trace.phases.len(), trace.merkle_batches
    );
}

fn json_field(text: &str, key: &str) -> String {
    let pattern = format!("\"{key}\":");
    let start = text.find(&pattern).expect("key present") + pattern.len();
    let rest = &text[start..];
    let end = rest.find([',', '}']).unwrap_or(rest.len());
    rest[..end].trim().trim_matches('"').to_string()
}

fn cmd_check_vm(dir: &str) {
    let (program, pi) = fixture(dir);
    let execution = program.execute(pi).expect("execute");
    assert!(execution.unconstrained_reads.is_empty(), "unconstrained reads");
    let report = fs::read_to_string(format!("{dir}/execution.json")).unwrap();
    let mut memory = Vec::new();
    for i in 0..execution.mem_used {
        word(&mut memory, execution.mem.word(i));
    }
    let memory_hash = hex(&primitives::hash::hash(&memory));
    let expected_cycles: usize = json_field(&report, "cycles").parse().unwrap();
    let expected_cells: usize = json_field(&report, "memory_cells_used").parse().unwrap();
    let expected_hash = json_field(&report, "memory_keccak256");
    assert_eq!(execution.cycles, expected_cycles, "cycle mismatch");
    assert_eq!(execution.mem_used, expected_cells, "memory cell mismatch");
    assert_eq!(memory_hash, expected_hash, "memory hash mismatch");
    println!(
        "E2E_ORACLE_VM|PASS|dir={dir}|cycles={}|memory_cells_used={}|memory_keccak256={}|rows={:?}",
        execution.cycles, execution.mem_used, memory_hash, execution.rows()
    );
}

fn cmd_export_proof(spec: &str, out: &str) {
    leanvm_core::init_prover();
    let (case, program, pi) = load_case(spec);
    let (proof, _) = prove(&program, pi, 1).expect("prove");
    let bytes = wire_opts().serialize(&proof).expect("a CPU proof serializes");
    fs::write(out, &bytes).unwrap();
    println!(
        "PROOF_EXPORTED|case={case}|path={out}|proof_bytes={}",
        bytes.len()
    );
}

fn cmd_verify_vm(spec: &str, proof_path: &str) {
    let (case, program, pi) = load_case(spec);
    let bytes = fs::read(proof_path).expect("the proof file exists");
    let proof: leanvm_core::cpu::Proof = wire_opts()
        .deserialize(&bytes)
        .unwrap_or_else(|e| {
            eprintln!("VERIFY_VM|FAIL|case={case}|path={proof_path}|error={e:?}");
            std::process::exit(1);
        });
    println!("VERIFY_VM|case={case}|path={proof_path}|proof_bytes={}", bytes.len());
    for pass in 1..=3 {
        let t = std::time::Instant::now();
        match verify(&program, &pi, &proof) {
            Ok(summary) => {
                let ms = t.elapsed().as_millis();
                println!(
                    "VERIFY_VM|PASS|pass={pass}|ms={ms}|keccak_scalars_len={}",
                    summary.keccak_scalars.len()
                );
            }
            Err(e) => {
                eprintln!("VERIFY_VM|FAIL|pass={pass}|error={e:?}");
                std::process::exit(1);
            }
        }
    }
}

fn mirror_statement(records: &[&[u8]]) -> [u8; 32] {
    let guest = rec_aggregation::aggregation::unified_guest();
    let seed = fs_seed(guest);
    let table = leanvm_core::cpu::layout::bytecode_table(&guest.prog);
    let value = F192::new(table[0].0, 0, 0);
    let mut sorted: Vec<&[u8]> = records.to_vec();
    sorted.sort_by_key(|r| &r[..64]);
    sorted.dedup_by_key(|r| &r[..64]);
    let mut claims = Vec::new();
    for r in &sorted {
        claims.extend(&r[..64]);
    }
    let mut statement = Vec::new();
    for v in seed {
        statement.extend(v.c0.to_le_bytes());
        statement.extend(v.c1.to_le_bytes());
    }
    statement.extend(primitives::hash::hash(&claims));
    statement.extend(primitives::hash::hash(&[]));
    statement.extend([0u8; 32]);
    statement.extend([0u8; 23 * 24]);
    word(&mut statement, value);
    primitives::hash::hash(&statement)
}

fn cmd_check_eth(dir: &str, log_inv_rate: usize) {
    let records = fixture_records(dir);
    let raw: Vec<(LeanXmssPublicKey, lean_xmss::Message, LeanXmssSignature)> = records;
    let (proof, stats) =
        rec_aggregation::aggregate_with_stats(&[], raw, vec![], &[], None, log_inv_rate).expect("aggregate");
    proof.verify().expect("aggregate verifies");
    let claims = rec_aggregation::SignatureClaims {
        xmss: proof.xmss_signers().to_vec(),
        lean_sphincs: proof.lean_sphincs_signers().to_vec(),
    };
    let wire = proof.to_bytes_without_pubkeys();
    let restored = rec_aggregation::EthereumProof::from_bytes_without_pubkeys(&wire, claims).expect("wire round trip");
    restored.verify().expect("restored aggregate verifies");
    let expected_statement = fs::read(format!("{dir}/statement.bin")).unwrap();
    let statement = mirror_statement(
        &fs::read(format!("{dir}/xmss-inputs.bin"))
            .unwrap()
            .chunks_exact(RECORD)
            .collect::<Vec<_>>(),
    );
    assert_eq!(hex(&statement), hex(&expected_statement), "mirror statement matches the fixture");
    println!(
        "E2E_ORACLE_ETH|PASS|dir={dir}|records={}|signers={}|log_inv_rate={}|proof_bytes={}|cycles={}|mem_used={}|committed={}|statement={}",
        records_len(dir),
        proof.xmss_signers().len(),
        log_inv_rate,
        wire.len(),
        stats.cycles,
        stats.mem_used,
        stats.committed,
        hex(&statement)
    );
}

fn cmd_export_eth_proof(dir: &str, out: &str, log_inv_rate: usize) {
    leanvm_core::init_prover();
    rec_aggregation::warm_up();
    let records = fixture_records(dir);
    let (proof, stats) =
        rec_aggregation::aggregate_with_stats(&[], records, vec![], &[], None, log_inv_rate).expect("aggregate");
    proof.verify().expect("aggregate verifies");
    let claims = rec_aggregation::SignatureClaims {
        xmss: proof.xmss_signers().to_vec(),
        lean_sphincs: proof.lean_sphincs_signers().to_vec(),
    };
    let wire = proof.to_bytes_without_pubkeys();
    let restored = rec_aggregation::EthereumProof::from_bytes_without_pubkeys(&wire, claims).expect("wire round trip");
    restored.verify().expect("restored aggregate verifies");
    let expected_statement = fs::read(format!("{dir}/statement.bin"))
        .or_else(|_| fs::read(format!("{dir}/expected-statement.bin")))
        .expect("a statement fixture");
    let statement = mirror_statement(
        &fs::read(format!("{dir}/xmss-inputs.bin"))
            .unwrap()
            .chunks_exact(RECORD)
            .collect::<Vec<_>>(),
    );
    assert_eq!(hex(&statement), hex(&expected_statement), "mirror statement matches the fixture");
    fs::write(out, &wire).unwrap();
    println!(
        "ETH_PROOF_EXPORTED|dir={dir}|path={out}|wire_bytes={}|proof_size={}|cycles={}|mem_used={}|committed={}|statement={}",
        wire.len(),
        proof.proof_size(),
        stats.cycles,
        stats.mem_used,
        stats.committed,
        hex(&statement)
    );
}

fn cmd_verify_eth(inputs_path: &str, proof_path: &str) {
    let records = fs::read(inputs_path).expect("the inputs file exists");
    let mut claims: Vec<(LeanXmssPublicKey, lean_xmss::Message)> = records
        .chunks_exact(RECORD)
        .map(|record| {
            (
                LeanXmssPublicKey::from_bytes(record[..32].try_into().unwrap()),
                record[32..64].try_into().unwrap(),
            )
        })
        .collect();
    claims.sort_by(|a, b| (a.0.to_bytes(), a.1).cmp(&(b.0.to_bytes(), b.1)));
    claims.dedup();
    let wire = fs::read(proof_path).expect("the proof file exists");
    let proof = rec_aggregation::EthereumProof::from_bytes_without_pubkeys(
        &wire,
        rec_aggregation::SignatureClaims { xmss: claims, lean_sphincs: vec![] },
    )
    .unwrap_or_else(|e| {
        eprintln!("VERIFY_ETH|FAIL|inputs={inputs_path}|path={proof_path}|error={e:?}");
        std::process::exit(1);
    });
    println!(
        "VERIFY_ETH|inputs={inputs_path}|path={proof_path}|wire_bytes={}|proof_size={}|signers={}",
        wire.len(),
        proof.proof_size(),
        proof.xmss_signers().len()
    );
    for pass in 1..=3 {
        let t = std::time::Instant::now();
        match proof.verify() {
            Ok(()) => {
                let ms = t.elapsed().as_millis();
                println!("VERIFY_ETH|PASS|pass={pass}|ms={ms}");
            }
            Err(e) => {
                eprintln!("VERIFY_ETH|FAIL|pass={pass}|error={e:?}");
                std::process::exit(1);
            }
        }
    }
}

fn records_len(dir: &str) -> usize {
    fs::metadata(format!("{dir}/xmss-inputs.bin")).unwrap().len() as usize / RECORD
}

fn cmd_gen_fresh(seed_value: u64, n: usize, out_dir: &str, guest_dir: &str) {
    use signatures::lean_xmss::mock;
    let out = Path::new(out_dir);
    fs::create_dir_all(out).unwrap();
    const KEY_START: u32 = 3_000_000_000;
    const KEY_END: u32 = 3_000_000_015;
    let message = rec_aggregation::signers_cache::message();
    let mut raw = Vec::with_capacity(n * RECORD);
    let mut records: Vec<Vec<u8>> = Vec::with_capacity(n);
    for i in 0..n {
        let mut seed_material = Vec::new();
        seed_material.extend(seed_value.to_le_bytes());
        seed_material.extend((i as u64).to_le_bytes());
        let seed: signatures::lean_xmss::Seed = primitives::hash::hash(&seed_material);
        let (sk, pk) = mock::key_gen_from_seed(seed, KEY_START, KEY_END);
        let leaf = KEY_START + (i as u32 % (KEY_END - KEY_START + 1));
        let sig = mock::sign(&sk, &message, leaf).expect("mock key signs in its range");
        lean_xmss::verify(&pk, &message, &sig).expect("a fresh mock signature verifies");
        let mut record = Vec::with_capacity(RECORD);
        record.extend(pk.to_bytes());
        record.extend(message);
        record.extend(sig.to_bytes());
        records.push(record.clone());
        raw.extend(&record);
    }
    fs::write(out.join("xmss-inputs.bin"), &raw).unwrap();

    let guest = rec_aggregation::aggregation::unified_guest();
    let seed = fs_seed(guest);
    let table = leanvm_core::cpu::layout::bytecode_table(&guest.prog);
    let value = F192::new(table[0].0, 0, 0);
    let mut seed_bytes = Vec::new();
    for v in seed {
        seed_bytes.extend(v.c0.to_le_bytes());
        seed_bytes.extend(v.c1.to_le_bytes());
    }
    fs::write(out.join("seed.bin"), &seed_bytes).unwrap();
    fs::write(out.join("bytecode-value.bin"), table[0].0.to_le_bytes()).unwrap();
    let mut bytecode = Vec::new();
    for op in &guest.prog {
        let mut n = vec![];
        let tag = match *op {
            Op::Xor { a, b, c } => {
                n.extend([a as u64, b as u64, c as u64]);
                0
            }
            Op::Mul { a, b, c } => {
                n.extend([a as u64, b as u64, c as u64]);
                1
            }
            Op::Set { o, k } => {
                n.extend([o as u64, k.c0, k.c1, k.c2]);
                2
            }
            Op::Deref { o1, o2, o3, mode } => {
                n.extend([
                    o1 as u64,
                    o2 as u64,
                    o3 as u64,
                    match mode {
                        DerefMode::Cell => 0,
                        DerefMode::Pc => 1,
                        DerefMode::Fp => 2,
                    },
                ]);
                3
            }
            Op::Jump { oc, od, of } => {
                n.extend([oc as u64, od as u64, of as u64]);
                4
            }
            Op::Keccak { m, tail, b8, cap, out, in_odd, out_odd } => {
                n.extend(m.map(u64::from));
                n.extend([tail as u64, b8 as u64, cap as u64, out as u64, in_odd as u64, out_odd as u64]);
                5
            }
        };
        bytecode.push(tag);
        for x in n {
            bytecode.extend(x.to_le_bytes());
        }
    }
    fs::write(out.join("bytecode.bin"), &bytecode).unwrap();

    let mut sorted: Vec<&[u8]> = records.iter().map(|r| r.as_slice()).collect();
    sorted.sort_by_key(|r| &r[..64]);
    sorted.dedup_by_key(|r| &r[..64]);
    let mut hints = Vec::new();
    entry(
        &mut hints,
        "meta",
        &[
            count(sorted.len()),
            count(0),
            count(sorted.len()),
            count(0),
            count(0),
            count(0),
            count(0),
            count(0),
        ],
    );
    entry(&mut hints, "fs_seed", &seed);
    if !sorted.is_empty() {
        let n = sorted.len();
        entry(&mut hints, "signers_split", &[count(n / 136), count(n % 136 / 17), count(n % 17)]);
    }
    let mut claims = Vec::new();
    for r in &sorted {
        claims.extend(&r[..64]);
        let cells: Vec<_> = r[..64].chunks_exact(16).map(aggregation::pack).collect();
        entry(&mut hints, "claims", &cells);
    }
    for (i, r) in sorted.iter().enumerate() {
        let pk = LeanXmssPublicKey::from_bytes(r[..32].try_into().unwrap());
        let message_i: &[u8; 32] = r[32..64].try_into().unwrap();
        let sig = LeanXmssSignature::from_bytes(r[64..].try_into().unwrap());
        lean_xmss::verify(&pk, message_i, &sig).unwrap();
        entry(&mut hints, "raw_index", &[count(i)]);
        for (name, values) in aggregation::xmss(&pk, &sig, message_i) {
            entry(&mut hints, name, &values);
        }
    }
    entry(&mut hints, "leaf_defer", &[value]);
    entry(&mut hints, "da_pick", &[count(0)]);
    fs::write(out.join("expected-hints.bin"), &hints).unwrap();

    let mut statement = seed_bytes;
    statement.extend(primitives::hash::hash(&claims));
    statement.extend(primitives::hash::hash(&[]));
    statement.extend([0u8; 32]);
    statement.extend([0u8; 23 * 24]);
    word(&mut statement, value);
    let statement = primitives::hash::hash(&statement);
    fs::write(out.join("expected-statement.bin"), statement).unwrap();

    let mut program = guest.clone();
    let streams = read_hints_bytes(&hints);
    for (name, values) in streams {
        program.set_witness(name, values);
    }
    let pi = [
        aggregation::pack(&statement[..16]),
        aggregation::pack(&statement[16..]),
    ];
    let execution = program.execute(pi).unwrap();
    assert!(execution.unconstrained_reads.is_empty());
    let mut memory = Vec::new();
    for i in 0..execution.mem_used {
        word(&mut memory, execution.mem.word(i));
    }
    let rows = execution.rows();
    let report = format!(
        "{{\"cycles\":{},\"memory_cells_used\":{},\"memory_keccak256\":\"{}\",\"rows\":{:?},\"unconstrained_reads\":[]}}",
        execution.cycles,
        execution.mem_used,
        hex(&primitives::hash::hash(&memory)),
        rows
    );
    fs::write(out.join("expected-execution.json"), &report).unwrap();
    fs::copy(
        Path::new(guest_dir).join("schedule.bin"),
        out.join("schedule.bin"),
    )
    .unwrap();
    println!(
        "FRESH_INPUTS|dir={out_dir}|records={n}|sorted_unique={}|cycles={}|mem_used={}|statement={}",
        sorted.len(),
        execution.cycles,
        execution.mem_used,
        hex(&statement)
    );
}

fn read_hints_bytes(hints: &[u8]) -> BTreeMap<String, Vec<Vec<F192>>> {
    let mut streams = BTreeMap::new();
    let mut cursor = 0;
    while cursor < hints.len() {
        let len = u32::from_le_bytes(hints[cursor..cursor + 4].try_into().unwrap()) as usize;
        cursor += 4;
        let name = String::from_utf8(hints[cursor..cursor + len].to_vec()).unwrap();
        cursor += len;
        let n = u32::from_le_bytes(hints[cursor..cursor + 4].try_into().unwrap()) as usize;
        cursor += 4;
        let mut values = Vec::new();
        for _ in 0..n {
            let a = u64::from_le_bytes(hints[cursor..cursor + 8].try_into().unwrap());
            let b = u64::from_le_bytes(hints[cursor + 8..cursor + 16].try_into().unwrap());
            let c = u64::from_le_bytes(hints[cursor + 16..cursor + 24].try_into().unwrap());
            cursor += 24;
            values.push(F192::new(a, b, c));
        }
        streams.entry(name).or_insert_with(Vec::new).push(values);
    }
    streams
}

fn cmd_benchmark(dir: &str, repeat: usize, cooldown_ms: u64, log_inv_rate: usize) {
    leanvm_core::init_prover();
    rec_aggregation::warm_up();
    let records = fixture_records(dir);
    let n = records.len();
    println!(
        "BENCH|impl=rust-e2e|prover=aggregate|records={n}|log_inv_rate={log_inv_rate}|repeat={repeat}|cooldown_ms={cooldown_ms}"
    );
    let t0 = std::time::Instant::now();
    let (proof, stats) = rec_aggregation::aggregate_with_stats(&[], records.clone(), vec![], &[], None, log_inv_rate)
        .expect("warmup aggregate");
    println!("WARMUP|nanos={}", t0.elapsed().as_nanos());
    let mut last_proof = proof;
    let mut times: Vec<u128> = Vec::with_capacity(repeat);
    let mut last_stats = stats;
    for i in 1..=repeat {
        if cooldown_ms > 0 {
            std::thread::sleep(Duration::from_millis(cooldown_ms));
        }
        let t = std::time::Instant::now();
        let (proof, stats) =
            rec_aggregation::aggregate_with_stats(&[], records.clone(), vec![], &[], None, log_inv_rate)
                .expect("measured aggregate");
        let nanos = t.elapsed().as_nanos();
        last_proof = proof;
        last_stats = stats;
        times.push(nanos);
        println!("PASS|i={i}|nanos={nanos}");
    }
    let mean = times.iter().sum::<u128>() / (times.len().max(1) as u128);
    let statement = mirror_statement(
        &fs::read(format!("{dir}/xmss-inputs.bin"))
            .unwrap()
            .chunks_exact(RECORD)
            .collect::<Vec<_>>(),
    );
    println!(
        "LAST|statement={}|proof_bytes={}|proof_size={}|cycles={}|mem_used={}|committed={}",
        hex(&statement),
        last_proof.to_bytes_without_pubkeys().len(),
        last_proof.proof_size(),
        last_stats.cycles,
        last_stats.mem_used,
        last_stats.committed
    );
    println!("STATS|passes={}|mean_nanos={mean}", times.len());
    let verify_status = match last_proof.verify() {
        Ok(()) => "ok",
        Err(_) => "failed",
    };
    println!("VERIFY|status={verify_status}");
    if verify_status != "ok" {
        std::process::exit(1);
    }
}

fn flag(args: &[String], name: &str, default: &str) -> String {
    let mut value = default.to_string();
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == name {
            if let Some(v) = it.next() {
                value = v.clone();
            }
        }
    }
    value
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let command = args.get(1).map(String::as_str).unwrap_or("usage");
    match command {
        "export-trace" => cmd_export_trace(&args[2], args.get(3).map(String::as_str).unwrap_or("-")),
        "verify-trace" => cmd_verify_trace(&args[2], &args[3]),
        "export-proof" => cmd_export_proof(&args[2], &args[3]),
        "verify-vm" => cmd_verify_vm(&args[2], &args[3]),
        "check-vm" => cmd_check_vm(&args[2]),
        "check-eth" => cmd_check_eth(
            &args[2],
            flag(&args[2..], "--log-inv-rate", "1").parse().unwrap(),
        ),
        "export-eth-proof" => cmd_export_eth_proof(
            &args[2],
            &args[3],
            flag(&args[2..], "--log-inv-rate", "1").parse().unwrap(),
        ),
        "verify-eth" => cmd_verify_eth(&args[2], &args[3]),
        "gen-fresh-inputs" => {
            let n = args[2].parse::<usize>().expect("a record count");
            let seed_value = args[3].parse::<u64>().expect("a numeric seed");
            let guest_dir = args
                .get(5)
                .cloned()
                .unwrap_or_else(|| format!("{}/oracle/xmss4", env::var("HUB").unwrap_or_default()));
            cmd_gen_fresh(seed_value, n, &args[4], &guest_dir);
        }
        "benchmark" => cmd_benchmark(
            &args[2],
            flag(&args[2..], "--repeat", "3").parse().unwrap(),
            flag(&args[2..], "--cooldown-ms", "2000").parse().unwrap(),
            flag(&args[2..], "--log-inv-rate", "1").parse().unwrap(),
        ),
        _ => {
            eprintln!(
                "usage: e2e-oracle <export-trace|verify-trace|export-proof|verify-vm|check-vm|check-eth|export-eth-proof|verify-eth|gen-fresh-inputs|benchmark> ..."
            );
            std::process::exit(2);
        }
    }
}
