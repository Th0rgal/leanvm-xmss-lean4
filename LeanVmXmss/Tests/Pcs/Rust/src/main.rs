use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::io::Write as _;
use bincode::Options as _;
use fiat_shamir::FiatShamirState;
use fiat_shamir::merkle::PrunedMerklePaths;
use fiat_shamir::transcript::Proof;
use leanvm_core::cpu::layout::{KeccakLane, MEM_HI, MEM_LO, MEM_TOP, QKECCAK, keccak_value, layout, schema};
use leanvm_core::cpu::{DerefMode, Op, Program, fs_seed, prove, public_input_bytes, verify};
use leanvm_core::leaf;
use leanvm_core::tables;
use primitives::field::{F64, F192};
use primitives::hash::STATE_LANES;
use primitives::multilinear::interp_k;
use rec_aggregation::aggregation::{EthereumProof, SignatureClaims};
use signatures::lean_sphincs::LeanSphincsPublicKey;
use signatures::lean_xmss::LeanXmssPublicKey;
use verifier::da;
use verifier::{E, K};

const SHIFTS: [usize; 6] = [32, 16, 8, 4, 2, 1];
const INITIAL: usize = 6;
const SUBSEQUENT: usize = 4;
const RS_INITIAL: usize = 3;
const RS_SUBSEQUENT: usize = 1;
const RESIDUAL: usize = 5;
const MIN_LOG: usize = 15;
const MAX_LOG: usize = 28;

const QUERIES: [[&[usize]; 14]; 4] = [
    [&[222, 55], &[223, 56, 30], &[223, 56, 31], &[223, 56, 32], &[223, 56, 32],
     &[223, 56, 32, 22], &[223, 56, 32, 22], &[224, 56, 32, 23], &[224, 56, 32, 23],
     &[224, 56, 32, 23, 17], &[224, 56, 32, 23, 17], &[224, 56, 32, 23, 18],
     &[225, 56, 32, 23, 18], &[225, 56, 32, 23, 18, 14]],
    [&[111, 45], &[112, 45, 27], &[112, 45, 28], &[112, 45, 28], &[112, 45, 28],
     &[112, 45, 28, 20], &[112, 45, 28, 20], &[112, 45, 28, 21], &[112, 45, 28, 21],
     &[112, 45, 28, 21, 16], &[112, 45, 28, 21, 16], &[112, 45, 28, 21, 16],
     &[112, 45, 28, 21, 16], &[112, 45, 28, 21, 16, 13]],
    [&[75, 37], &[75, 37, 24], &[75, 37, 25], &[75, 38, 25], &[75, 38, 25],
     &[75, 38, 25, 18], &[75, 38, 25, 19], &[75, 38, 25, 19], &[75, 38, 25, 19],
     &[75, 38, 25, 19, 15], &[75, 38, 25, 19, 15], &[75, 38, 25, 19, 15],
     &[75, 38, 25, 19, 15], &[75, 38, 25, 19, 15, 13]],
    [&[56, 32], &[56, 32, 22], &[56, 32, 22], &[56, 32, 23], &[56, 32, 23],
     &[56, 32, 23, 17], &[56, 32, 23, 17], &[56, 32, 23, 18], &[56, 32, 23, 18],
     &[56, 32, 23, 18, 14], &[56, 32, 23, 18, 14], &[56, 32, 23, 18, 14],
     &[56, 32, 23, 18, 15], &[56, 32, 23, 18, 15, 12]],
];

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn limbs(value: E) -> String {
    format!("{:x},{:x},{:x}", value.c0, value.c1, value.c2)
}

fn elem(seed: u64, tag: u64) -> E {
    E::new(
        seed.wrapping_mul(0x9e37_79b9_7f4a_7c15).wrapping_add(tag),
        seed.wrapping_mul(0xbf58_476d_1ce4_e5b9).wrapping_add(tag << 1),
        seed.wrapping_mul(0x94d0_49bb_1331_11eb).wrapping_add(tag << 2),
    )
}

fn ring_map(mut value: E, challenges: &[E]) -> E {
    for (&challenge, shift) in challenges.iter().zip(SHIFTS) {
        value += challenge * value.pow(1 << shift);
    }
    value
}

fn coefficient(challenges: &[E], k: usize) -> E {
    challenges
        .iter()
        .zip(SHIFTS)
        .filter(|&(_, shift)| k & shift != 0)
        .fold(E::new(1, 0, 0), |acc, (factor, shift)| acc * factor.pow(1 << (k % shift)))
}

fn ring_weight(point: &[E], r_prime: &[E], coefficients: &[E]) -> E {
    let mut total = E::new(0, 0, 0);
    let mut frobenius = point.to_vec();
    for &scale in coefficients {
        let mut product = scale;
        for (value, &challenge) in frobenius.iter_mut().zip(r_prime) {
            product *= E::new(1, 0, 0) + *value + challenge;
            *value = value.square();
        }
        total += product;
    }
    total
}

fn derive(log_n: usize, rate: usize) -> Option<(Vec<usize>, Vec<usize>, &'static [usize])> {
    if !(MIN_LOG..=MAX_LOG).contains(&log_n) || !(1..=4).contains(&rate) {
        return None;
    }
    let mut folds = vec![INITIAL];
    let mut rates = vec![rate];
    let mut remaining = log_n - INITIAL;
    while remaining > RESIDUAL {
        let reduction = if folds.len() == 1 { RS_INITIAL } else { RS_SUBSEQUENT };
        rates.push(rates[rates.len() - 1] + folds[folds.len() - 1] - reduction);
        let fold = SUBSEQUENT.min(remaining);
        remaining -= fold;
        folds.push(fold);
    }
    let queries = QUERIES[rate - 1][log_n - MIN_LOG];
    (queries.len() == folds.len()).then_some((rates, folds, queries))
}

fn sample_window(sample: E, depth: usize, chunk: usize) -> u64 {
    let bits = [sample.c0, sample.c1, sample.c2, 0];
    let limb = chunk * depth / 64;
    let shift = chunk * depth % 64;
    let window = ((bits[limb] as u128) | ((bits[limb + 1] as u128) << 64)) >> shift;
    (window as u64) & ((1u64 << depth) - 1)
}

fn eq_eval(left: &[E], right: &[E]) -> E {
    let mut result = E::new(1, 0, 0);
    for (&x, &y) in left.iter().zip(right) {
        result *= E::new(1, 0, 0) + x + y;
    }
    result
}

fn multilinear(table: &[K], point: &[E]) -> E {
    let mut cur: Vec<E> = table.iter().copied().map(E::from).collect();
    for &challenge in point {
        for index in 0..cur.len() / 2 {
            cur[index] = cur[2 * index] + challenge * (cur[2 * index] + cur[2 * index + 1]);
        }
        cur.truncate(cur.len() / 2);
    }
    cur[0]
}

fn poly_eval(coeffs: &[E], point: E) -> E {
    coeffs.iter().rev().fold(E::new(0, 0, 0), |acc, coeff| acc * point + *coeff)
}

fn nums(values: &[usize]) -> String {
    values.iter().map(ToString::to_string).collect::<Vec<_>>().join(",")
}

fn da_line(name: &str, root: Option<[u8; 32]>) {
    println!("DA|{name}|{}", hex(&da::digest(root)));
}

fn key_bytes(seed: u8) -> [u8; 32] {
    std::array::from_fn(|index| seed.wrapping_add(index as u8).wrapping_mul(17))
}

fn message_bytes(seed: u8) -> [u8; 32] {
    std::array::from_fn(|index| seed.wrapping_add(3).wrapping_mul(index as u8 + 1))
}

fn wire_case(name: &str, count: usize, da_root: Option<[u8; 32]>) {
    let claims = SignatureClaims {
        xmss: (0..count)
            .map(|index| {
                (
                    LeanXmssPublicKey::from_bytes(&key_bytes(0x11 + index as u8)),
                    message_bytes(0x41 + index as u8),
                )
            })
            .collect(),
        lean_sphincs: (0..count.saturating_sub(1))
            .map(|index| {
                (
                    LeanSphincsPublicKey::from_bytes(&key_bytes(0x81 + index as u8)),
                    message_bytes(0xc1 + index as u8),
                )
            })
            .collect(),
    };
    let point = vec![F192::ZERO; 4 + rec_aggregation::aggregation::unified_guest().prog.len().trailing_zeros() as usize];
    let proof = Proof {
        stream: vec![F192::new(7, 8, 9), F192::new(10, 11, 12)],
        merkle: vec![PrunedMerklePaths::default()],
    };
    let encoded = bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .serialize(&((&claims.xmss, &claims.lean_sphincs), &da_root, &point, &proof))
        .expect("wire encoding");
    let parsed = EthereumProof::from_bytes(&encoded).expect("accepted wire");
    let again = parsed.to_bytes();
    let bare = parsed.to_bytes_without_pubkeys();
    let restored = EthereumProof::from_bytes_without_pubkeys(&bare, claims.clone()).expect("bare wire");
    assert_eq!(again, encoded);
    assert_eq!(restored.to_bytes(), encoded);
    let mut tampered = encoded.clone();
    if let Some(byte) = tampered.last_mut() {
        *byte ^= 0xff;
    }
    let rejected = EthereumProof::from_bytes(&tampered).map(|parsed| parsed.to_bytes() == encoded);
    assert_ne!(rejected, Ok(true), "tampered wire must not round-trip");
    assert_eq!(parsed.proof_size(), restored.proof_size());
    let da_bytes = da::digest(da_root);
    println!(
        "WIRE|{name}|{}|{}|{}|{}",
        hex(&encoded),
        hex(&bare),
        parsed.proof_size(),
        hex(&da_bytes)
    );
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

fn load_case(name: &str, dir: Option<&str>) -> (Program, [F192; 2]) {
    let pi = [F192::ZERO, F192::ZERO];
    match name {
        "syn_tiny" => (
            Program::assemble(
                pad_pow2(vec![
                    set_k(2, 5),
                    set_k(3, 9),
                    Op::Xor { a: 2, b: 3, c: 4 },
                    set_k(5, 7),
                    Op::Mul { a: 4, b: 5, c: 6 },
                    set_k(8, 1),
                    set_k(9, 0),
                    set_k(10, 0),
                ]),
                Default::default(),
                16,
            ),
            pi,
        ),
        "syn_jump" => (
            Program::assemble(
                pad_pow2(vec![
                    set_k(2, 1),
                    set_k(3, 32),
                    set_k(4, 1),
                    Op::Jump { oc: 2, od: 3, of: 4 },
                    set_k(5, 9),
                    set_k(6, 0),
                    set_k(7, 1),
                    Op::Jump { oc: 6, od: 7, of: 4 },
                ]),
                Default::default(),
                16,
            ),
            pi,
        ),
        "syn_deref" => (
            Program::assemble(
                pad_pow2(vec![
                    set_k(2, 64),
                    set_k(3, 11),
                    Op::Deref { o1: 2, o2: 0, o3: 3, mode: DerefMode::Cell },
                    Op::Deref { o1: 2, o2: 1, o3: 0, mode: DerefMode::Pc },
                    Op::Deref { o1: 2, o2: 2, o3: 0, mode: DerefMode::Fp },
                    set_k(12, 0),
                    set_k(13, 0),
                    set_k(14, 0),
                ]),
                Default::default(),
                16,
            ),
            pi,
        ),
        "syn_keccak" => (
            Program::assemble(
                pad_pow2(vec![
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
                    Op::Keccak { m: [2, 3, 4, 5], tail: 6, b8: 10, cap: 11, out: 16, in_odd: false, out_odd: true },
                    Op::Keccak { m: [16, 17, 18, 19], tail: 20, b8: 24, cap: 25, out: 30, in_odd: true, out_odd: false },
                ]),
                Default::default(),
                64,
            ),
            pi,
        ),
        _ => {
            let default_dir = format!("/var/lib/orb-node/work/caches/xmss-hub-v3/oracle/{name}");
            let dir = dir.unwrap_or(&default_dir);
            let mut program = rec_aggregation::aggregation::unified_guest().clone();
            let bytes = fs::read(format!("{dir}/hints.bin")).unwrap();
            let mut cursor = 0usize;
            let mut streams: BTreeMap<String, Vec<Vec<F192>>> = BTreeMap::new();
            while cursor < bytes.len() {
                let len = u32::from_le_bytes(bytes[cursor..cursor + 4].try_into().unwrap()) as usize;
                cursor += 4;
                let hname = String::from_utf8(bytes[cursor..cursor + len].to_vec()).unwrap();
                cursor += len;
                let n = u32::from_le_bytes(bytes[cursor..cursor + 4].try_into().unwrap()) as usize;
                cursor += 4;
                let mut values = Vec::with_capacity(n);
                for _ in 0..n {
                    let a = u64::from_le_bytes(bytes[cursor..cursor + 8].try_into().unwrap());
                    let b = u64::from_le_bytes(bytes[cursor + 8..cursor + 16].try_into().unwrap());
                    let c = u64::from_le_bytes(bytes[cursor + 16..cursor + 24].try_into().unwrap());
                    cursor += 24;
                    values.push(F192::new(a, b, c));
                }
                streams.entry(hname).or_default().push(values);
            }
            for (hname, entries) in streams {
                program.set_witness(hname, entries);
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
    }
}

struct ReplayReader<'a> {
    sponge: FiatShamirState,
    stream: &'a [F192],
    cursor: usize,
    ops: Vec<u8>,
}

impl<'a> ReplayReader<'a> {
    fn next_scalar(&mut self) -> F192 {
        let v = self.stream[self.cursor];
        self.cursor += 1;
        self.sponge.observe(v);
        self.ops.push(0);
        v
    }
    fn next_scalars(&mut self, n: usize) -> Vec<F192> {
        (0..n).map(|_| self.next_scalar()).collect()
    }
    fn sample(&mut self) -> F192 {
        self.ops.push(1);
        self.sponge.sample()
    }
    fn samples(&mut self, n: usize) -> Vec<F192> {
        (0..n).map(|_| self.sample()).collect()
    }
}

fn write_f192(out: &mut fs::File, v: F192) {
    for limb in [v.c0, v.c1, v.c2] {
        out.write_all(&limb.to_le_bytes()).unwrap();
    }
}

fn splice_dump(case: &str, path: &str, program: &Program, pi: [F192; 2]) {
    let (proof, stats) = prove(program, pi, 1).expect("prove");
    let summary = verify(program, &pi, &proof).expect("verify");
    let seed = fs_seed(program);
    let mut iv = [0u8; 32];
    iv[..8].copy_from_slice(&seed[0].c0.to_le_bytes());
    iv[8..16].copy_from_slice(&seed[0].c1.to_le_bytes());
    iv[16..24].copy_from_slice(&seed[1].c0.to_le_bytes());
    iv[24..32].copy_from_slice(&seed[1].c1.to_le_bytes());
    let pi_bytes = public_input_bytes(&pi);
    let mut sponge_iv = [F64::ZERO; 4];
    for (index, word) in sponge_iv.iter_mut().enumerate() {
        *word = F64(if index % 2 == 0 { seed[index / 2].c0 } else { seed[index / 2].c1 });
    }
    let mut sponge_pi = [F64::ZERO; 4];
    for (index, chunk) in pi_bytes.chunks_exact(8).enumerate() {
        sponge_pi[index] = F64(u64::from_le_bytes(chunk.try_into().unwrap()));
    }
    let mut reader = ReplayReader {
        sponge: FiatShamirState::new(sponge_iv, sponge_pi),
        stream: &proof.stream,
        cursor: 0,
        ops: Vec::new(),
    };
    let _announced = reader.next_scalars(2 + tables::N_TABLES);
    let _root = reader.next_scalars(2);
    let l = layout(&program.prog, stats.log_mem, stats.rows, pi);
    let log_bytecode = program.prog.len().trailing_zeros() as usize;
    let _alphas = reader.samples(4);
    let _beta = reader.sample();
    let mut point: Vec<F192> = Vec::new();
    let _shared = reader.next_scalar();
    let _count = reader.next_scalar();
    let push_lay = leaf::layout(&l.push);
    let mut layer = push_lay.mu;
    while layer > 0 {
        let step = if layer % 2 == 1 { 1 } else { 2 };
        let _combiner = reader.sample();
        let degree = (1usize << step) + 1;
        let mut x = Vec::with_capacity(point.len());
        for _ in 0..point.len() {
            let _coeffs = reader.next_scalars(degree - 1);
            x.push(reader.sample());
        }
        let _c0 = reader.next_scalars(1 << step);
        let _c1 = reader.next_scalars(1 << step);
        let _c2 = reader.next_scalars(1 << step);
        let y = reader.samples(step);
        point = [y, x].concat();
        layer -= step;
    }
    let memory_low = point[..stats.log_mem].to_vec();
    let bytecode_low = point[..log_bytecode].to_vec();
    let mem_vals = reader.next_scalars(3);
    let mem_final = reader.next_scalar();
    let bc_final = reader.next_scalar();
    let mut claims: Vec<(usize, Vec<F192>, F192)> = vec![
        (MEM_LO, memory_low.clone(), mem_vals[0]),
        (MEM_HI, memory_low.clone(), mem_vals[1]),
        (MEM_TOP, memory_low.clone(), mem_vals[2]),
        (3, memory_low, mem_final),
        (4, bytecode_low, bc_final),
    ];
    let _xi = reader.sample();
    let n_rounds = l.taus.into_iter().max().unwrap_or(0);
    let mut challenges = Vec::with_capacity(n_rounds);
    for _ in 0..n_rounds {
        let _coeffs = reader.next_scalars(3);
        challenges.push(reader.sample());
    }
    let sumcheck_point: Vec<F192> = challenges.into_iter().rev().collect();
    let sch = schema();
    let mut keccak_instance = Vec::new();
    for (t, table) in tables::tables().iter().enumerate() {
        let chi = sumcheck_point[..l.taus[t]].to_vec();
        let evals = reader.next_scalars(table.n_committed_columns());
        for (c, &val) in evals.iter().enumerate() {
            let col = sch.base[t] + c;
            if let Some(KeccakLane::Output(_)) = keccak_value(col) {
                continue;
            }
            claims.push((col, chi.clone(), val));
        }
        if t == 5 {
            keccak_instance = chi;
        }
    }
    let r_pi = reader.sample();
    assert_eq!(reader.cursor, summary.keccak_scalars.start, "keccak start mismatch");
    let [pi0, pi1] = pi;
    let pi_limbs = [(pi0.c0, pi1.c0), (pi0.c1, pi1.c1), (pi0.c2, pi1.c2)];
    let mut pi_point = vec![F192::ZERO; l.placements[MEM_LO].n_vars];
    pi_point[0] = r_pi;
    for (idx, col) in [MEM_LO, MEM_HI, MEM_TOP].into_iter().enumerate() {
        let (lo, hi) = pi_limbs[idx];
        claims.push((col, pi_point.clone(), interp_k(F64(lo), F64(hi), r_pi)));
    }
    let mut slot_claims: Vec<(usize, Vec<F192>, F192)> = claims
        .into_iter()
        .map(|(col, pt, val)| {
            let offset = match keccak_value(col) {
                Some(KeccakLane::Slot(slot)) => l.placements[QKECCAK].offset + (slot << pt.len()),
                _ => l.placements[col].offset,
            };
            (offset, pt, val)
        })
        .collect();
    let log_steps = l.taus[5];
    let pack_bits = log_steps - 4;
    let slot_bits = 6usize;
    let segment = reader.samples(1);
    let _lanes = reader.samples(5);
    let _committed = reader.next_scalar();
    let mut k_point = [&keccak_instance[4..], &segment[..]].concat();
    for _ in 0..12 {
        let _prod = reader.next_scalars(47);
        let _s = reader.sample();
        k_point = (0..k_point.len())
            .map(|_| {
                let _ = reader.next_scalars(2);
                reader.sample()
            })
            .collect();
        for _ in 0..11 {
            let _ = reader.next_scalars(3);
            let _ = reader.sample();
        }
        let _t = reader.next_scalars(3);
        let _beta = reader.sample();
    }
    let out_slot: Vec<F192> = (0..slot_bits)
        .map(|_| {
            let _ = reader.next_scalars(2);
            reader.sample()
        })
        .collect();
    let out_word = reader.next_scalar();
    let qkeccak_offset = l.placements[QKECCAK].offset;
    slot_claims.push((qkeccak_offset, [&keccak_instance[..], &out_slot[..]].concat(), out_word));
    let low: Vec<F192> = (0..4)
        .map(|_| {
            let _ = reader.next_scalars(2);
            reader.sample()
        })
        .collect();
    let in_slot: Vec<F192> = (0..slot_bits)
        .map(|_| {
            let _ = reader.next_scalars(2);
            reader.sample()
        })
        .collect();
    let ring_slices = reader.next_scalars(64);
    assert_eq!(reader.cursor, summary.keccak_scalars.end, "keccak end mismatch");
    let ring_point = [&low[..], &k_point[..pack_bits], &in_slot[..]].concat();
    let mut out = fs::File::create(path).unwrap();
    out.write_all(&iv).unwrap();
    out.write_all(&pi_bytes).unwrap();
    out.write_all(&(reader.ops.len() as u64).to_le_bytes()).unwrap();
    out.write_all(&reader.ops).unwrap();
    out.write_all(&(reader.cursor as u64).to_le_bytes()).unwrap();
    for &v in &proof.stream[..reader.cursor] {
        write_f192(&mut out, v);
    }
    out.write_all(&(slot_claims.len() as u64).to_le_bytes()).unwrap();
    for (off, pt, val) in &slot_claims {
        out.write_all(&(*off as u64).to_le_bytes()).unwrap();
        out.write_all(&(pt.len() as u64).to_le_bytes()).unwrap();
        for &p in pt {
            write_f192(&mut out, p);
        }
        write_f192(&mut out, *val);
    }
    out.write_all(&(qkeccak_offset as u64).to_le_bytes()).unwrap();
    out.write_all(&(ring_point.len() as u64).to_le_bytes()).unwrap();
    for &p in &ring_point {
        write_f192(&mut out, p);
    }
    for &s in &ring_slices {
        write_f192(&mut out, s);
    }
    let _ = STATE_LANES;
    println!("SPLICE_DUMP|{case}|stream={}|slots={}|ring_vars={}", reader.cursor, slot_claims.len(), ring_point.len());
}

fn splice_verify(case: &str, path: &str, program: &Program, pi: [F192; 2]) {
    let (rust_proof, _) = prove(program, pi, 1).expect("rust prove");
    let raw = fs::read(path).expect("read lean proof");
    let lean_proof: Proof = bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .deserialize(&raw)
        .expect("bincode deserialize lean Proof");
    if lean_proof.stream.len() != rust_proof.stream.len() {
        eprintln!("STREAM_LEN_MISMATCH|lean={}|rust={}", lean_proof.stream.len(), rust_proof.stream.len());
    }
    let min_s = lean_proof.stream.len().min(rust_proof.stream.len());
    for i in 0..min_s {
        if lean_proof.stream[i] != rust_proof.stream[i] {
            panic!("STREAM_MISMATCH|{case}|idx={i}|lean={:?}|rust={:?}", lean_proof.stream[i], rust_proof.stream[i]);
        }
    }
    assert_eq!(lean_proof.stream.len(), rust_proof.stream.len(), "stream len mismatch");
    assert_eq!(lean_proof.merkle.len(), rust_proof.merkle.len(), "merkle phase count mismatch");
    for (p, (lm, rm)) in lean_proof.merkle.iter().zip(rust_proof.merkle.iter()).enumerate() {
        if lm != rm {
            panic!("MERKLE_MISMATCH|{case}|phase={p}|lean_rows={}|rust_rows={}|lean_sibs={}|rust_sibs={}",
                lm.leaf_data.len(), rm.leaf_data.len(), lm.sibling_hashes.len(), rm.sibling_hashes.len());
        }
    }
    let summary = verify(program, &pi, &lean_proof).expect("unchanged cpu::verify rejected lean proof");
    let _ = summary;
    let claims = SignatureClaims {
        xmss: vec![(
            LeanXmssPublicKey::from_bytes(&key_bytes(0x11)),
            message_bytes(0x41),
        )],
        lean_sphincs: vec![],
    };
    let point = vec![F192::ZERO; 4 + rec_aggregation::aggregation::unified_guest().prog.len().trailing_zeros() as usize];
    let da_root: Option<[u8; 32]> = None;
    let wire_bytes = bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .serialize(&((&claims.xmss, &claims.lean_sphincs), &da_root, &point, &lean_proof))
        .expect("serialize EthereumProof");
    let parsed = EthereumProof::from_bytes(&wire_bytes).expect("EthereumProof::from_bytes");
    assert_eq!(parsed.to_bytes(), wire_bytes);
    let mut tampered = wire_bytes.clone();
    if let Some(byte) = tampered.last_mut() {
        *byte ^= 0xff;
    }
    let rejected = EthereumProof::from_bytes(&tampered).map(|parsed| parsed.to_bytes() == wire_bytes);
    assert_ne!(rejected, Ok(true), "tampered wire must not round-trip");
    println!("SPLICE_OK|{case}|stream={}|merkle={}|wire_bytes={}", lean_proof.stream.len(), lean_proof.merkle.len(), wire_bytes.len());
}

fn main() {
    let mode = env::args().nth(1).unwrap_or_else(|| "synthetic".into());
    if mode == "splice-dump" || mode == "splice-verify" {
        let case = env::args().nth(2).expect("case name");
        let path = env::args().nth(3).expect("path");
        let dir = env::args().nth(4);
        let (program, pi) = load_case(&case, dir.as_deref());
        if mode == "splice-dump" {
            splice_dump(&case, &path, &program, pi);
        } else {
            splice_verify(&case, &path, &program, pi);
        }
        return;
    }
    let challenges: Vec<E> = (0..6).map(|index| elem(0x111, index)).collect();
    let point: Vec<E> = (0..4).map(|index| elem(0x222, index)).collect();
    let prime: Vec<E> = (0..4).map(|index| elem(0x333, index)).collect();
    let slices: Vec<E> = (0..64).map(|index| elem(0x444, index)).collect();
    let coefficients: Vec<E> = (0..64).map(|index| coefficient(&challenges, index as usize)).collect();
    let images: Vec<E> = slices.iter().map(|slice| ring_map(*slice, &challenges)).collect();
    println!(
        "RING|mapped={}|weight={}|target={}",
        limbs(ring_map(slices[3], &challenges)),
        limbs(ring_weight(&point, &prime, &coefficients)),
        limbs(poly_eval(&images, E::new(2, 0, 0)))
    );
    let mut configs = String::new();
    for log_n in [15usize, 16, 20, 28] {
        for rate in 1..=4 {
            if let Some((rates, folds, queries)) = derive(log_n, rate) {
                configs.push_str(&format!("{log_n}:{rate}:{}:{}:{}|", nums(&rates), nums(&folds), nums(queries)));
            }
        }
    }
    println!("WHIR|{configs}");
    let sample = elem(0x555, 7);
    let windows = (0..4).map(|chunk| sample_window(sample, 9, chunk).to_string()).collect::<Vec<_>>();
    println!("WINDOW|{}", windows.join(","));
    let table: Vec<K> = (0..16).map(|index| K(0x1000 + index)).collect();
    println!("MLE|{}", limbs(multilinear(&table, &(0..4).map(|index| elem(0x666, index)).collect::<Vec<_>>())));
    println!("EQ|{}", limbs(eq_eval(&point, &prime)));
    println!(
        "POLY|{}",
        limbs(poly_eval(&[elem(1, 0), elem(2, 0), elem(3, 0), elem(4, 0)], elem(9, 1)))
    );
    if mode == "synthetic" || mode == "all" {
        da_line("syn_tiny", None);
        da_line("syn_jump", Some([7; 32]));
        da_line("syn_deref", None);
        da_line("syn_keccak", Some([9; 32]));
    }
    if mode == "oracle" || mode == "all" {
        for name in ["xmss4", "xmss16"] {
            let bytes = fs::read(format!("/var/lib/orb-node/work/caches/xmss-hub-v3/oracle/{name}/seed.bin"))
                .unwrap_or_else(|_| panic!("missing seed for {name}"));
            let mut root = [0u8; 32];
            root.copy_from_slice(&bytes[..32]);
            da_line(name, Some(root));
        }
    }
    if mode == "wire" || mode == "all" {
        wire_case("syn_tiny", 1, None);
        wire_case("syn_jump", 2, Some([7; 32]));
        wire_case("syn_deref", 0, None);
        wire_case("syn_keccak", 3, Some([9; 32]));
        for name in ["xmss4", "xmss16"] {
            let bytes = fs::read(format!("/var/lib/orb-node/work/caches/xmss-hub-v3/oracle/{name}/seed.bin"))
                .unwrap_or_else(|_| panic!("missing seed for {name}"));
            let mut root = [0u8; 32];
            root.copy_from_slice(&bytes[..32]);
            wire_case(name, 2, Some(root));
        }
    }
    println!("PARITY_DONE|{mode}");
}
