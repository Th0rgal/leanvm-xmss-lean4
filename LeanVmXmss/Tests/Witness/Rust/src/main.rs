use fiat_shamir::FiatShamirState;
use fiat_shamir::merkle::hash_to_scalars;
use leanvm_core::cpu::{DerefMode, Op, Program, fs_seed, prove, public_input_bytes, verify};
use primitives::field::{F64, F192};
use std::collections::BTreeMap;
use std::env;
use std::fs;

const LOG_INV_RATE: usize = 1;

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

fn emit(name: &str, program: &Program, pi: [F192; 2]) {
    let t0 = std::time::Instant::now();
    eprintln!("[{name}] starting execute...");
    let execution = program.execute(pi).expect("execution");
    eprintln!("[{name}] execute done in {:.2?}", t0.elapsed());
    assert!(execution.unconstrained_reads.is_empty(), "{name} unconstrained reads");
    let rows = execution.rows();
    let t1 = std::time::Instant::now();
    eprintln!("[{name}] starting prove...");
    let (proof, stats) = prove(program, pi, LOG_INV_RATE).expect("prove");
    eprintln!("[{name}] prove done in {:.2?}", t1.elapsed());
    let t2 = std::time::Instant::now();
    verify(program, &pi, &proof).expect("verify");
    eprintln!("[{name}] verify done in {:.2?}", t2.elapsed());
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
    let mut announced = Vec::new();
    announced.push(F192::new(stats.log_mem as u64, 0, 0));
    for &count in &rows {
        announced.push(F192::new(count as u64, 0, 0));
    }
    announced.push(F192::new(LOG_INV_RATE as u64, 0, 0));
    let mut sponge = FiatShamirState::new(iv, public_input);
    for value in &announced {
        sponge.observe(*value);
    }
    let challenge = sponge.clone().sample();
    let root_scalars = [proof.stream[announced.len()], proof.stream[announced.len() + 1]];
    sponge.observe(root_scalars[0]);
    sponge.observe(root_scalars[1]);
    let official = sponge.sample();
    println!("CASE|{name}");
    println!(
        "EXEC|{}|{}|{}|{}|{}",
        execution.cycles,
        execution.mem_used,
        stats.log_mem,
        rows.map(|n| n.to_string()).join(","),
        execution.unconstrained_reads.len()
    );
    println!("ANNOUNCE|{}", hash_e(&announced));
    println!("ROOT|{}|{}", limbs(root_scalars[0]), limbs(root_scalars[1]));
    println!("CHAL|{}|{}", limbs(challenge), limbs(official));
    let expected = hash_to_scalars(&primitives::hash::hash(&[]));
    let _ = expected;
}

fn xmss(dir: &str) -> (Program, [F192; 2]) {
    let t0 = std::time::Instant::now();
    eprintln!("[xmss] compiling unified_guest...");
    let mut program = rec_aggregation::aggregation::unified_guest().clone();
    eprintln!("[xmss] unified_guest done in {:.2?}", t0.elapsed());
    let t1 = std::time::Instant::now();
    for (name, entries) in read_hints(&format!("{dir}/hints.bin")) {
        program.set_witness(name, entries);
    }
    eprintln!("[xmss] hints loaded in {:.2?}", t1.elapsed());
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
