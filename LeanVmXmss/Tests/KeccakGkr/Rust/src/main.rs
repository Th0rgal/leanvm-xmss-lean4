use fiat_shamir::FiatShamirState;
use leanvm_core::cpu::layout::{KeccakLane, MEM_HI, MEM_LO, MEM_TOP, QKECCAK, keccak_value, layout, schema};
use leanvm_core::cpu::{DerefMode, Op, Program, fs_seed, prove, public_input_bytes, verify};
use leanvm_core::leaf;
use leanvm_core::tables;
use primitives::field::{F64, F192};
use primitives::hash::{PI as KECCAK_PI, RC as KECCAK_RC, RHO as KECCAK_RHO, ROUNDS, STATE_LANES};
use primitives::multilinear::{eq_table, interp_k, poly_eval};
use std::collections::BTreeMap;
use std::env;
use std::fs;

const LOG_INV_RATE: usize = 1;
const BUS_BITS: usize = 4;
const KECCAK_TABLE: usize = 5;
const KECCAK_V_OUT: usize = 38;

const PACK_BITS: usize = 4;
const PACK: usize = 1 << PACK_BITS;
const EMBED_BITS: usize = 24;
const PRODUCT_BITS: usize = 2 * EMBED_BITS - 1;
const BITS: usize = 64 * STATE_LANES;
const LOCAL_BITS: usize = 11;
const LANE_BITS: usize = 5;
const K_BITS: usize = 64;

const RMFE_EMBED: [u32; PACK] = [
    0x40c50b, 0x7f79f2, 0x4b4e0a, 0x72740c, 0x5357da, 0x1d1c9e, 0x04be6e, 0x785246,
    0x097cdc, 0x109e7e, 0x1f1454, 0x213cfc, 0x4cfcc8, 0x775770, 0x187386, 0x818a16,
];
const RMFE_PROJECT: [u64; PACK] = [
    0x1,
    0x7fffffffffff,
    0x274e9d3a74e9,
    0x1d3a74e9d3a7,
    0x65cb972e5cb9,
    0x5cb972e5cb97,
    0x6690aec7cd21,
    0x5d8f9a42bb1f,
    0x73485763e690,
    0x3750967c6ea1,
    0x12cf8dd4259f,
    0x1ba84b3e3750,
    0x0ad0c9f715a1,
    0x064fb8ad0c9f,
    0x456864fb8ad0,
    0x400000000000,
];

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn limbs(value: F192) -> String {
    format!("{:x},{:x},{:x}", value.c0, value.c1, value.c2)
}

fn hash_e(words: &[F192]) -> String {
    let mut preimage = Vec::with_capacity(words.len() * 24);
    for w in words {
        for limb in [w.c0, w.c1, w.c2] {
            preimage.extend_from_slice(&limb.to_le_bytes());
        }
    }
    hex(&primitives::hash::Hasher::new().update(&preimage).finalize())
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
        "syn_keccak" => (
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
        _ => panic!("unknown synthetic {name}"),
    };
    (pad_pow2(ops), frame, pi)
}

fn read_hints(path: &str) -> BTreeMap<String, Vec<Vec<F192>>> {
    let bytes = fs::read(path).unwrap();
    let mut cursor = 0usize;
    let mut streams = BTreeMap::new();
    while cursor < bytes.len() {
        let len = u32::from_le_bytes(bytes[cursor..cursor + 4].try_into().unwrap()) as usize;
        cursor += 4;
        let name = String::from_utf8(bytes[cursor..cursor + len].to_vec()).unwrap();
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
        streams.entry(name).or_insert_with(Vec::new).push(values);
    }
    streams
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

    fn sumcheck_round_poly(&mut self, count: usize, claim: F192, eq_factor: Option<F192>) -> Vec<F192> {
        let Some(eq_factor) = eq_factor else {
            let constant = self.next_scalar();
            let tail = self.next_scalars(count - 2);
            let sum_tail = tail.iter().fold(F192::ZERO, |a, &x| a + x);
            return [vec![constant, claim + sum_tail], tail].concat();
        };
        let tail = self.next_scalars(count - 1);
        let sum_tail = tail.iter().fold(F192::ZERO, |a, &x| a + x);
        [vec![claim + eq_factor * sum_tail], tail].concat()
    }

    fn sumcheck(&mut self, mut claim: F192, count: usize, n_rounds: usize) -> (Vec<F192>, F192) {
        let mut point = Vec::with_capacity(n_rounds);
        for _ in 0..n_rounds {
            let msg = self.sumcheck_round_poly(count, claim, None);
            let ch = self.sample();
            point.push(ch);
            claim = poly_eval(&msg, ch);
        }
        (point, claim)
    }
}

fn dot(a: &[F192], b: &[F192]) -> F192 {
    a.iter().zip(b).fold(F192::ZERO, |acc, (&x, &y)| acc + x * y)
}

fn sum_slice(xs: &[F192]) -> F192 {
    xs.iter().fold(F192::ZERO, |acc, &x| acc + x)
}

fn along(j: usize, k: usize) -> usize {
    let (lane, z) = (j / 64, j % 64);
    64 * ((lane % 5 + k) % 5 + 5 * (lane / 5)) + z
}

fn linear_transpose(w: &[F192]) -> Vec<F192> {
    let mut g = vec![F192::ZERO; BITS];
    for lane in 0..STATE_LANES {
        for z in 0..64 {
            g[64 * lane + z] = w[64 * KECCAK_PI[lane] + (z + KECCAK_RHO[lane] as usize) % 64];
        }
    }
    let mut columns = vec![F192::ZERO; 5 * 64];
    for (j, &weight) in g.iter().enumerate() {
        columns[64 * (j / 64 % 5) + j % 64] += weight;
    }
    (0..BITS)
        .map(|j| {
            let (x, z) = (j / 64 % 5, j % 64);
            g[j] + columns[64 * ((x + 1) % 5) + z] + columns[64 * ((x + 4) % 5) + (z + 1) % 64]
        })
        .collect()
}

fn instance_weights(s: F192) -> Vec<F192> {
    let mut powers = [F192::ONE; EMBED_BITS];
    for b in 1..EMBED_BITS {
        powers[b] = powers[b - 1] * s;
    }
    RMFE_EMBED
        .iter()
        .map(|&e| {
            (0..EMBED_BITS)
                .filter(|b| e >> b & 1 == 1)
                .fold(F192::ZERO, |acc, b| acc + powers[b])
        })
        .collect()
}

struct KeccakClaim {
    value: F192,
    mu: Vec<F192>,
    point: Vec<F192>,
    weights: Vec<F192>,
}

fn slot_weights(
    pack_bits: usize,
    slot_bits: usize,
    claim: &KeccakClaim,
    first: usize,
    count: usize,
) -> Vec<[F192; 64]> {
    let segments = eq_table(&claim.point[pack_bits..]);
    let mut rows = vec![[F192::ZERO; 64]; 1 << slot_bits];
    for segment in 0..count {
        for j in 0..BITS {
            rows[STATE_LANES * (first + segment) + j / 64][j % 64] = segments[segment] * claim.weights[j];
        }
    }
    rows
}

fn replay_open(
    reader: &mut ReplayReader<'_>,
    pack_bits: usize,
    slot_bits: usize,
    claim: &KeccakClaim,
    first: usize,
    count: usize,
    value: F192,
) -> (Vec<F192>, [F192; 64], F192) {
    let (slot, value) = reader.sumcheck(value, 3, slot_bits);
    let mut rows = slot_weights(pack_bits, slot_bits, claim, first, count);
    for &challenge in &slot {
        rows = rows
            .chunks(2)
            .map(|pair| std::array::from_fn(|z| pair[0][z] + challenge * (pair[0][z] + pair[1][z])))
            .collect();
    }
    (slot, rows[0], value)
}

fn replay_layer(
    reader: &mut ReplayReader<'_>,
    pack_bits: usize,
    segments: usize,
    depth: usize,
    step: usize,
    claim: &KeccakClaim,
) -> KeccakClaim {
    let product = reader.next_scalars(PRODUCT_BITS);
    let projected = (0..PRODUCT_BITS).fold(F192::ZERO, |acc, c| {
        let functional = (0..PACK)
            .filter(|&i| RMFE_PROJECT[i] >> c & 1 == 1)
            .fold(F192::ZERO, |s, i| s + claim.mu[i]);
        acc + functional * product[c]
    });
    let seg_eq = eq_table(&claim.point[pack_bits..]);
    let mut iota = F192::ZERO;
    for (segment, &weight) in seg_eq.iter().enumerate().take(segments) {
        let constant = KECCAK_RC[depth * (segment + 1) - step - 1];
        let wsum = (0..64)
            .filter(|z| constant >> z & 1 == 1)
            .fold(F192::ZERO, |a, z| a + claim.weights[z]);
        iota += weight * wsum;
    }
    assert_eq!(projected + iota * sum_slice(&claim.mu), claim.value, "KeccakProduct step {step}");

    let s = reader.sample();
    let mu = instance_weights(s);
    let kappa = sum_slice(&mu);
    let mut value = poly_eval(&product, s);

    let mut scale = F192::ONE;
    let mut point = Vec::with_capacity(claim.point.len());
    for &r in &claim.point {
        let message = reader.sumcheck_round_poly(3, value, Some(r));
        let challenge = reader.sample();
        value = (F192::ONE + r + challenge) * poly_eval(&message, challenge);
        scale *= F192::ONE + r + challenge;
        point.push(challenge);
    }

    let (local, value) = reader.sumcheck(value, 4, LOCAL_BITS);
    let t = reader.next_scalars(3);
    let eq = eq_table(&local);
    assert_eq!(
        scale * dot(&eq[..BITS], &claim.weights) * (kappa * t[0] + (kappa + t[1]) * t[2]),
        value,
        "KeccakLayer step {step}"
    );

    let beta = reader.sample();
    let weights: Vec<F192> = (0..BITS)
        .map(|j| eq[j] + beta * (eq[along(j, 4)] + beta * eq[along(j, 3)]))
        .collect();
    KeccakClaim {
        value: t[0] + beta * (t[1] + beta * t[2]),
        mu,
        point,
        weights: linear_transpose(&weights),
    }
}

fn mle_eval_eq(values: &[F192], point: &[F192]) -> F192 {
    dot(values, &eq_table(point))
}

fn emit(name: &str, program: &Program, pi: [F192; 2]) {
    let t0 = std::time::Instant::now();
    eprintln!("[{name}] starting prove...");
    let (proof, stats) = prove(program, pi, LOG_INV_RATE).expect("prove");
    eprintln!("[{name}] prove done in {:.2?}", t0.elapsed());
    let t1 = std::time::Instant::now();
    let summary = verify(program, &pi, &proof).expect("verify");
    eprintln!("[{name}] verify done in {:.2?}", t1.elapsed());

    let seed = fs_seed(program);
    let mut iv = [F64::ZERO; 4];
    for (index, word) in iv.iter_mut().enumerate() {
        *word = F64(if index % 2 == 0 { seed[index / 2].c0 } else { seed[index / 2].c1 });
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

    let _announced = reader.next_scalars(2 + tables::N_TABLES);
    let _root = reader.next_scalars(2);
    let l = layout(&program.prog, stats.log_mem, stats.rows, pi);
    let log_bytecode = program.prog.len().trailing_zeros() as usize;

    let _alphas = reader.samples(BUS_BITS);
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
    let mut table_evals: Vec<(Vec<F192>, Vec<F192>)> = Vec::with_capacity(tables::N_TABLES);
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
        table_evals.push((chi, evals));
    }

    let r_pi = reader.sample();
    assert_eq!(
        reader.cursor, summary.keccak_scalars.start,
        "Keccak start stream boundary mismatch"
    );

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

    // Replay Keccak GKR reduction up to summary.keccak_scalars.end.
    let (instance, keccak_evals) = &table_evals[KECCAK_TABLE];
    let output_lanes = &keccak_evals[KECCAK_V_OUT..KECCAK_V_OUT + STATE_LANES];
    let log_steps = l.taus[KECCAK_TABLE];
    let depth = leanvm_core::keccak::DEPTH;
    let segments = ROUNDS / depth;
    let seg_bits = segments.next_power_of_two().ilog2() as usize;
    let pack_bits = log_steps - PACK_BITS;
    let slot_bits = (STATE_LANES * segments).next_power_of_two().ilog2() as usize;

    let segment = reader.samples(seg_bits);
    let first_point = [&instance[PACK_BITS..], &segment[..]].concat();
    let lanes_eq = eq_table(&reader.samples(LANE_BITS));
    let first_weights: Vec<F192> = (0..BITS)
        .map(|j| lanes_eq[j / 64] * F192::new(1 << (j % 64), 0, 0))
        .collect();
    let last_val = eq_table(&segment)[segments - 1] * dot(&lanes_eq[..STATE_LANES], output_lanes);
    let committed_val = if segments > 1 { reader.next_scalar() } else { F192::ZERO };
    let first_claim = KeccakClaim {
        value: committed_val + last_val,
        mu: eq_table(&instance[..PACK_BITS]),
        point: first_point,
        weights: first_weights,
    };

    let mut claim = replay_layer(&mut reader, pack_bits, segments, depth, 0, &first_claim);
    for step in 1..depth {
        claim = replay_layer(&mut reader, pack_bits, segments, depth, step, &claim);
    }

    let qkeccak_offset = l.placements[QKECCAK].offset;
    let mut output_opening: Option<(Vec<F192>, F192)> = None;
    if segments > 1 {
        let (slot_pt, weights, rem_val) = replay_open(
            &mut reader,
            pack_bits,
            slot_bits,
            &first_claim,
            1,
            segments - 1,
            committed_val,
        );
        let word = reader.next_scalar();
        assert_eq!(weights[0] * word, rem_val, "KeccakOutputOpening");
        let full_pt = [&instance[..], &slot_pt[..]].concat();
        output_opening = Some((full_pt.clone(), word));
        slot_claims.push((qkeccak_offset, full_pt, word));
    }

    let (low, rem_val) = reader.sumcheck(claim.value, 3, PACK_BITS);
    let (slot_pt, weights, rem_val) = replay_open(
        &mut reader,
        pack_bits,
        slot_bits,
        &claim,
        0,
        segments,
        rem_val,
    );
    let slices = reader.next_scalars(K_BITS);
    assert_eq!(
        mle_eval_eq(&claim.mu, &low) * dot(&weights, &slices),
        rem_val,
        "KeccakInputOpening"
    );
    let input_point = [&low[..], &claim.point[..pack_bits], &slot_pt[..]].concat();

    assert_eq!(
        reader.cursor, summary.keccak_scalars.end,
        "Keccak end stream boundary mismatch"
    );
    let probe = reader.sponge.clone().sample();
    let keccak_slice = &proof.stream[summary.keccak_scalars.clone()];

    println!("CASE|{name}");
    println!(
        "STREAM|{}|{}",
        reader.cursor,
        hash_e(&proof.stream[..reader.cursor])
    );
    println!(
        "KECCAK_SCALARS|{}|{}|{}",
        summary.keccak_scalars.start,
        keccak_slice.len(),
        hash_e(keccak_slice)
    );
    if std::env::var_os("KECCAK_GKR_DUMP_SCALARS").is_some() {
        for (i, w) in keccak_slice.iter().enumerate() {
            println!("SCALAR|{i}|{}", limbs(*w));
        }
    }
    println!("PROBE|{}", limbs(probe));
    match &output_opening {
        Some((pt, val)) => println!(
            "OUT_OPEN|1|{}|{}|{}|{}",
            qkeccak_offset,
            pt.len(),
            hash_e(pt),
            limbs(*val)
        ),
        None => println!("OUT_OPEN|0|0|0||0,0,0"),
    }
    println!(
        "RING_OPEN|{}|{}|{}|{}|{}",
        qkeccak_offset,
        input_point.len(),
        hash_e(&input_point),
        slices.len(),
        hash_e(&slices)
    );
    let mut slot_words = Vec::new();
    for (off, pt, val) in &slot_claims {
        slot_words.push(F192::new(*off as u64, pt.len() as u64, 0));
        slot_words.extend_from_slice(pt);
        slot_words.push(*val);
    }
    println!("SLOTS|{}|{}", slot_claims.len(), hash_e(&slot_words));
}

fn xmss(dir: &str) -> (Program, [F192; 2]) {
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

fn main() {
    let args: Vec<String> = env::args().collect();
    let which = args.get(1).map(String::as_str).unwrap_or("synthetic");
    if which == "synthetic" || which == "all" {
        for name in ["syn_tiny", "syn_jump", "syn_deref", "syn_keccak"] {
            let (ops, frame, pi) = synthetic(name);
            let program = Program::assemble(ops, Default::default(), frame);
            emit(name, &program, pi);
        }
    }
    if which == "xmss" {
        let label = args.get(2).expect("xmss case name (e.g. xmss4 or xmss16)");
        let dir = args.get(3).expect("xmss oracle directory");
        let (program, pi) = xmss(dir);
        emit(label, &program, pi);
    }
    if which == "all" {
        let dir4 = args.get(2).expect("xmss4 oracle directory");
        let dir16 = args.get(3).expect("xmss16 oracle directory");
        let (prog4, pi4) = xmss(dir4);
        emit("xmss4", &prog4, pi4);
        let (prog16, pi16) = xmss(dir16);
        emit("xmss16", &prog16, pi16);
    }
}
