use leanvm_core::cpu::layout::{
    KeccakLane, QKECCAK_SPARE, bytecode_table, col_kappa_sources, keccak_value, layout, schema,
};
use leanvm_core::cpu::{DerefMode, Op, Program, fs_seed};
use leanvm_core::leaf::{Block, Coord};
use leanvm_core::tables;
use primitives::field::{F64, F192};
use std::collections::HashMap;
use std::fs;
use verifier::Bytecode;

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn hash_words(words: &[F64]) -> String {
    let mut preimage = Vec::with_capacity(words.len() * 8);
    for w in words {
        preimage.extend_from_slice(&w.0.to_le_bytes());
    }
    let digest = primitives::hash::Hasher::new().update(&preimage).finalize();
    hex(&digest)
}

fn format_coord(c: &Coord, prog_ptrs: &[usize]) -> String {
    match c {
        Coord::Const(v) => format!("K({})", v.0),
        Coord::Col(i) => format!("C({i})"),
        Coord::GCol(i, k) => format!("G({i},{k})"),
        Coord::Prod(i, j, k) => format!("P({i},{j},{k})"),
        Coord::Index => "I".to_string(),
        Coord::Public(arc) => {
            let ptr = std::sync::Arc::as_ptr(arc) as usize;
            let idx = prog_ptrs
                .iter()
                .position(|&p| p == ptr)
                .expect("unknown public column arc");
            format!("B({idx})")
        }
        Coord::Sum(cs) => {
            let inner: Vec<String> = cs.iter().map(|x| format_coord(x, prog_ptrs)).collect();
            format!("S[{}]", inner.join("+"))
        }
    }
}

fn format_blocks(blocks: &[Block], prog_ptrs: &[usize]) -> Vec<String> {
    blocks
        .iter()
        .map(|b| {
            let coords: Vec<String> = b.coords.iter().map(|c| format_coord(c, prog_ptrs)).collect();
            let pad: Vec<String> = b.padding.iter().map(|p| p.0.to_string()).collect();
            format!(
                "{}|{}|[{}]|[{}]",
                b.kappa,
                b.rows,
                coords.join(","),
                pad.join(",")
            )
        })
        .collect()
}

fn bus_side_layout(blocks: &[Block]) -> (usize, Vec<usize>) {
    let n = blocks.len();
    let mut order: Vec<usize> = (0..n).collect();
    order.sort_by(|&a, &b| blocks[b].kappa.cmp(&blocks[a].kappa).then(a.cmp(&b)));
    let mut offsets = vec![0usize; n];
    let mut off = 0usize;
    for i in order {
        offsets[i] = off;
        off += 1usize << blocks[i].kappa;
    }
    let placed = off.max(1);
    let mu = (64 - (placed as u64 - 1).leading_zeros()) as usize;
    (mu, offsets)
}

fn decode_bytecode(bytes: &[u8]) -> Vec<Op> {
    let mut out = Vec::new();
    let mut offset = 0usize;
    while offset < bytes.len() {
        let tag = bytes[offset];
        let n = match tag {
            5 => 10usize,
            2 | 3 => 4usize,
            0 | 1 | 4 => 3usize,
            _ => panic!("unknown tag {tag}"),
        };
        let mut words = Vec::with_capacity(n);
        for i in 0..n {
            let pos = offset + 1 + 8 * i;
            let w = u64::from_le_bytes(bytes[pos..pos + 8].try_into().unwrap());
            words.push(w);
        }
        offset += 1 + 8 * n;
        let op = match tag {
            0 => Op::Xor {
                a: words[0] as u32,
                b: words[1] as u32,
                c: words[2] as u32,
            },
            1 => Op::Mul {
                a: words[0] as u32,
                b: words[1] as u32,
                c: words[2] as u32,
            },
            2 => Op::Set {
                o: words[0] as u32,
                k: F192::new(words[1], words[2], words[3]),
            },
            3 => Op::Deref {
                o1: words[0] as u32,
                o2: words[1] as u32,
                o3: words[2] as u32,
                mode: match words[3] {
                    0 => DerefMode::Cell,
                    1 => DerefMode::Pc,
                    2 => DerefMode::Fp,
                    _ => panic!("bad deref mode"),
                },
            },
            4 => Op::Jump {
                oc: words[0] as u32,
                od: words[1] as u32,
                of: words[2] as u32,
            },
            5 => Op::Keccak {
                m: [
                    words[0] as u32,
                    words[1] as u32,
                    words[2] as u32,
                    words[3] as u32,
                ],
                tail: words[4] as u32,
                b8: words[5] as u32,
                cap: words[6] as u32,
                out: words[7] as u32,
                in_odd: words[8] == 1,
                out_odd: words[9] == 1,
            },
            _ => unreachable!(),
        };
        out.push(op);
    }
    out
}

fn emit_case(name: &str, prog: &[Op], log_mem: usize, rows: [usize; 6]) {
    let sch = schema();
    let program = Program::assemble(prog.to_vec(), HashMap::new(), 16);
    let seed = fs_seed(&program);
    let mut seed_bytes = Vec::with_capacity(32);
    for half in seed {
        seed_bytes.extend_from_slice(&half.c0.to_le_bytes());
        seed_bytes.extend_from_slice(&half.c1.to_le_bytes());
    }
    let table = bytecode_table(prog);
    let raw_table: Vec<u64> = table.iter().map(|w| w.0).collect();
    let vbc = Bytecode::new(&raw_table);
    let vbc_dummy = F192::ZERO;
    let _ = vbc_dummy;
    assert_eq!(vbc.len(), table.len());

    let lay = layout(prog, log_mem, rows, [F192::ZERO, F192::ZERO]);
    let prog_ptrs: Vec<usize> = lay.push[2].coords[3..]
        .iter()
        .map(|c| match c {
            Coord::Public(arc) => std::sync::Arc::as_ptr(arc) as usize,
            _ => panic!("expected public coord"),
        })
        .collect();

    let qk_offset = lay.placements[5].offset;
    let step_log = lay.taus[5];
    let placements_str: Vec<String> = (0..sch.n)
        .map(|col| match keccak_value(col) {
            Some(KeccakLane::Slot(slot)) => {
                format!("{}:{}", step_log, qk_offset + (slot << step_log))
            }
            Some(KeccakLane::Output(_)) => "none".to_string(),
            None => {
                let p = lay.placements[col];
                format!("{}:{}", p.n_vars, p.offset)
            }
        })
        .collect();

    let (push_mu, push_off) = bus_side_layout(&lay.push);
    let (pull_mu, pull_off) = bus_side_layout(&lay.pull);
    let (count_mu, count_off) = bus_side_layout(&lay.count);

    println!("CASE|{name}");
    println!(
        "SCHEMA|{}|{}|{}",
        sch.n,
        QKECCAK_SPARE,
        sch.base.map(|x| x.to_string()).join(",")
    );
    let log_bc = prog.len().trailing_zeros() as usize;
    let sources_str: Vec<String> = col_kappa_sources(log_bc)
        .into_iter()
        .map(|s| match s {
            Some((src, adj)) => format!("{src}:{adj}"),
            None => "none".to_string(),
        })
        .collect();
    println!("SOURCES|{}", sources_str.join(","));
    let kv_str: Vec<String> = (0..sch.n)
        .map(|c| match keccak_value(c) {
            Some(KeccakLane::Slot(s)) => format!("S({s})"),
            Some(KeccakLane::Output(o)) => format!("O({o})"),
            None => "N".to_string(),
        })
        .collect();
    println!("KECCAK_VAL|{}", kv_str.join(","));
    println!("IV|{}", hex(&seed_bytes));
    println!("BC_LEN|{}", table.len());
    println!("BC_WORD0|{}", table[0].0);
    println!("BC_HASH|{}", hash_words(&table));
    println!(
        "TAUS|{}",
        lay.taus.map(|x| x.to_string()).join(",")
    );
    let placed: usize = lay
        .placements
        .iter()
        .filter(|p| p.n_vars != usize::MAX)
        .map(|p| 1usize << p.n_vars)
        .sum();
    println!(
        "SHAPE|{}|{}|{}|{}",
        lay.shape.mu,
        lay.shape.n_lanes,
        lay.shape.committed_len(),
        placed
    );
    println!("PLACEMENTS|{}", placements_str.join(","));
    let push_off_s: Vec<String> = push_off.iter().map(|x| x.to_string()).collect();
    let pull_off_s: Vec<String> = pull_off.iter().map(|x| x.to_string()).collect();
    let count_off_s: Vec<String> = count_off.iter().map(|x| x.to_string()).collect();
    println!("BUS_PUSH_LAY|{push_mu}|{}", push_off_s.join(","));
    println!("BUS_PULL_LAY|{pull_mu}|{}", pull_off_s.join(","));
    println!("BUS_COUNT_LAY|{count_mu}|{}", count_off_s.join(","));
    for (idx, line) in format_blocks(&lay.push, &prog_ptrs).into_iter().enumerate() {
        println!("PUSH|{idx}|{line}");
    }
    for (idx, line) in format_blocks(&lay.pull, &prog_ptrs).into_iter().enumerate() {
        println!("PULL|{idx}|{line}");
    }
    for (idx, line) in format_blocks(&lay.count, &prog_ptrs).into_iter().enumerate() {
        println!("COUNT|{idx}|{line}");
    }
    let _ = tables::N_TABLES;
}

fn synthetic_prog() -> Vec<Op> {
    vec![
        Op::Xor { a: 2, b: 3, c: 4 },
        Op::Mul { a: 5, b: 6, c: 7 },
        Op::Set {
            o: 8,
            k: F192::new(0x1234_5678_9abc_def0, 0xfedc_ba98_7654_3210, 0x1122_3344_5566_7788),
        },
        Op::Deref {
            o1: 2,
            o2: 3,
            o3: 9,
            mode: DerefMode::Cell,
        },
        Op::Deref {
            o1: 2,
            o2: 1,
            o3: 10,
            mode: DerefMode::Pc,
        },
        Op::Deref {
            o1: 4,
            o2: 2,
            o3: 11,
            mode: DerefMode::Fp,
        },
        Op::Jump {
            oc: 2,
            od: 7,
            of: 0,
        },
        Op::Keccak {
            m: [1, 3, 5, 7],
            tail: 9,
            b8: 11,
            cap: 13,
            out: 15,
            in_odd: true,
            out_odd: false,
        },
    ]
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let syn = synthetic_prog();
    emit_case("syn_tiny", &syn, 16, [0, 1, 2, 3, 4, 5]);
    emit_case("syn_keccak_heavy", &syn, 20, [1000, 2048, 0, 513, 17, 600]);
    if args.len() >= 2 {
        let bc_bytes = fs::read(&args[1]).expect("failed to read bytecode.bin");
        let xmss_prog = decode_bytecode(&bc_bytes);
        assert_eq!(xmss_prog.len(), 1 << 19);
        emit_case(
            "xmss1400",
            &xmss_prog,
            24,
            [262098, 237184, 169439, 159273, 57477, 261066],
        );
    }
}
