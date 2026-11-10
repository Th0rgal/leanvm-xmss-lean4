use leanvm_core::cpu::{DerefMode, Fault, Op, Program};
use primitives::field::F192;
use std::collections::HashMap;

fn k(n: u64) -> F192 { F192::new(n, 0, 0) }
fn set(o: u32, n: u64) -> Op { Op::Set { o, k: k(n) } }

fn main() {
    let cases = vec![
        ("xor", vec![set(2, 5), set(3, 9), Op::Xor { a: 2, b: 3, c: 4 }]),
        ("mul", vec![set(2, 5), set(3, 9), Op::Mul { a: 2, b: 3, c: 4 }]),
        ("backsolve", vec![set(2, 5), set(4, 45), Op::Mul { a: 2, b: 3, c: 4 }]),
        ("zero-backsolve", vec![set(2, 0), set(4, 1), Op::Mul { a: 2, b: 3, c: 4 }]),
        ("conflict", vec![set(2, 5), set(2, 9)]),
        ("deref-link", vec![set(2, 8), Op::Deref { o1: 2, o2: 1, o3: 5, mode: DerefMode::Cell }, set(4, 11)]),
        ("wild-pointer", vec![set(2, 0), Op::Deref { o1: 2, o2: 0, o3: 5, mode: DerefMode::Cell }]),
        ("deref-pc", vec![set(2, 8), Op::Deref { o1: 2, o2: 1, o3: 5, mode: DerefMode::Pc }]),
        ("deref-fp", vec![set(2, 8), Op::Deref { o1: 2, o2: 1, o3: 5, mode: DerefMode::Fp }]),
        ("unwritten-read", vec![Op::Xor { a: 2, b: 3, c: 4 }]),
    ];
    for (name, mut ops) in cases {
        while ops.len() < 8 { ops.push(set(15, 0)); }
        let program = Program::assemble(ops, HashMap::new(), 16);
        match program.execute([k(0), k(0)]) {
            Ok(e) => {
                let words: Vec<_> = (0..16).map(|i| { let x = e.mem.word(i); format!("{}:{}:{}", x.c0, x.c1, x.c2) }).collect();
                println!("{name}|ok|{}|{:?}|{:?}|{}", e.cycles, e.rows(), e.unconstrained_reads, words.join(","));
            }
            Err(e) => {
                let fault = match e.fault {
                    Fault::Conflict { .. } => "conflict",
                    Fault::BackSolveThroughZero => "backSolveThroughZero",
                    Fault::WildPointer { .. } => "wildPointer",
                    _ => panic!("unexpected fault: {:?}", e),
                };
                println!("{name}|error|{fault}");
            }
        }
    }
}
