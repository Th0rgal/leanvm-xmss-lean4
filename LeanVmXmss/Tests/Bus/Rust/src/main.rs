use fiat_shamir::FiatShamirState;
use leanvm_core::cpu::layout::{KeccakLane, MEM_HI, MEM_LO, MEM_TOP, QKECCAK, keccak_value, layout, schema};
use leanvm_core::cpu::{DerefMode, Op, Program, fs_seed, prove, public_input_bytes, verify};
use leanvm_core::leaf;
use leanvm_core::tables;
use primitives::field::{F64, F192};
use primitives::hash::STATE_LANES;
use primitives::multilinear::interp_k;
use std::collections::BTreeMap;
use std::env;
use std::fs;

const LOG_INV_RATE: usize = 1;
const BUS_BITS: usize = 4;
const KECCAK_TABLE: usize = 5;
const KECCAK_V_OUT: usize = 38;

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
        "Slice 3A stream boundary mismatch"
    );
    let probe = reader.sponge.clone().sample();

    let [pi0, pi1] = pi;
    let pi_limbs = [(pi0.c0, pi1.c0), (pi0.c1, pi1.c1), (pi0.c2, pi1.c2)];
    let mut pi_point = vec![F192::ZERO; l.placements[MEM_LO].n_vars];
    pi_point[0] = r_pi;
    for (idx, col) in [MEM_LO, MEM_HI, MEM_TOP].into_iter().enumerate() {
        let (lo, hi) = pi_limbs[idx];
        claims.push((col, pi_point.clone(), interp_k(F64(lo), F64(hi), r_pi)));
    }

    let slot_claims: Vec<(usize, Vec<F192>, F192)> = claims
        .into_iter()
        .map(|(col, pt, val)| {
            let offset = match keccak_value(col) {
                Some(KeccakLane::Slot(slot)) => l.placements[QKECCAK].offset + (slot << pt.len()),
                _ => l.placements[col].offset,
            };
            (offset, pt, val)
        })
        .collect();

    let (keccak_pt, keccak_evals) = &table_evals[KECCAK_TABLE];
    let keccak_lanes = &keccak_evals[KECCAK_V_OUT..KECCAK_V_OUT + STATE_LANES];

    println!("CASE|{name}");
    println!(
        "STREAM|{}|{}",
        reader.cursor,
        hash_e(&proof.stream[..reader.cursor])
    );
    println!("PROBE|{}", limbs(probe));
    println!(
        "KECCAK_OUT|{}|{}|{}",
        keccak_pt.len(),
        hash_e(keccak_pt),
        hash_e(keccak_lanes)
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
    if which == "xmss" || which == "all" {
        let dir = args.get(2).expect("xmss oracle directory");
        let (program, pi) = xmss(dir);
        emit("xmss1400", &program, pi);
    }
}
