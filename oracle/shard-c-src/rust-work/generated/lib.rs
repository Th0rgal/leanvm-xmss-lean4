


























use std::collections::HashMap;
use std::fmt::Write;

use leanvm_core::cpu::hints::{BitsDest, RHint};
use leanvm_core::cpu::{DerefMode, Op, Program};
use primitives::{
    field::{F64, F192, g_pow},
    pretty_integer,
};

mod ast;
mod ir;
mod lower;
mod parser;
pub use ast::*;
pub(crate) use ir::*;
use lower::lower_func;
pub(crate) use parser::subst_stmts;
pub use parser::{parse, parse_const, parse_with_replacements};



pub fn compile(ast: &Ast) -> Program {
    
    let mut queue: Vec<Func> = Vec::new();
    let main = ast
        .funcs
        .iter()
        .find(|f| f.name == "main")
        .expect("program needs a `main`");
    assert!(!main.has_const_params(), "main cannot take Const parameters");
    assert!(!main.inline, "main cannot be `@inline`");
    queue.push(main.clone());
    for f in &ast.funcs {
        if f.name != "main" {
            queue.push(f.clone());
        }
    }
    
    let defs: HashMap<&str, &Func> = ast.funcs.iter().map(|f| (f.name.as_str(), f)).collect();
    
    let const_arrays: HashMap<&str, &[F192]> = ast
        .const_arrays
        .iter()
        .map(|(name, values)| (name.as_str(), values.as_slice()))
        .collect();
    let dbg_lower = std::env::var("DBG_LOWER").is_ok();

    let mut loop_bounds = HashMap::new();
    let mut loop_ctr = 0usize;
    let mut lowered: Vec<Lowered> = Vec::new();
    let mut tables = JumpTables::default();
    let mut i = 0;
    while i < queue.len() {
        let f = &queue[i];
        i += 1;
        
        
        
        if f.has_const_params() || f.inline {
            continue;
        }
        let f = f.clone();
        lowered.push(lower_func(
            &f,
            &mut queue,
            &mut loop_ctr,
            &defs,
            &const_arrays,
            &mut loop_bounds,
            &mut tables,
        ));
    }
    
    
    let tables_base = lowered[0].frame_size;
    if !tables.slots.is_empty() {
        lowered[0].frame_size += tables.slots.len() as u32;
        let code = (tables.slots.iter().zip(tables_base..))
            .map(|(k, o)| LInstr {
                op: LOp::Set { o, k: k.clone() },
                line: 0,
                hints: Vec::new(),
            })
            .collect();
        let frame_size = lowered[0].frame_size;
        lowered.insert(
            0,
            Lowered {
                name: "__jump_tables".into(),
                code,
                frame_size,
            },
        );
    }
    if dbg_lower {
        for low in &lowered {
            eprintln!("== fn {} (frame {}) ==", low.name, pretty_integer(low.frame_size));
            for (i, ins) in low.code.iter().enumerate() {
                let index = pretty_integer(i);
                eprintln!("  {index:>5}: {:?}", ins.op);
            }
        }
    }
    
    let mut entry = HashMap::new();
    let mut frame_size = HashMap::new();
    let mut pc = 0u32;
    for l in &lowered {
        entry.insert(l.name.clone(), pc);
        frame_size.insert(l.name.clone(), l.frame_size);
        pc += l.code.len() as u32;
    }
    
    
    
    let total: usize = lowered.iter().map(|l| l.code.len()).sum();
    
    
    
    let bytecode_size = (total + 1).next_power_of_two();
    let sentinel = (bytecode_size - 1) as u32;

    
    let mut prog: Vec<Op> = Vec::new();
    
    let mut src_lines: Vec<u32> = Vec::new();
    let mut hints: HashMap<u32, Vec<RHint>> = HashMap::new();
    for l in &mut lowered {
        let pc0 = entry[&l.name];
        for ins in &mut l.code {
            let here = prog.len() as u32;
            if !ins.hints.is_empty() {
                let rhs = ins
                    .hints
                    .drain(..)
                    .map(|h| match h {
                        Hint::NextFrameAddress => RHint::FrameAddress { offset: l.frame_size },
                        Hint::AllocLoopFrames {
                            ptr,
                            callee,
                            count,
                            tail,
                        } => {
                            let size = frame_size[&callee];
                            match count {
                                LoopCount::Constant(n) => RHint::Alloc {
                                    ptr,
                                    size: size
                                        .checked_mul(u32::try_from(n - 1).expect("loop range too large"))
                                        .and_then(|frames| frames.checked_add(tail))
                                        .expect("loop frames overflow"),
                                },
                                LoopCount::Bound { cell, start } => RHint::AllocFrames {
                                    ptr,
                                    size,
                                    end: cell,
                                    start_inverse: g_pow_u128(u128::from(start)).inv(),
                                    tail,
                                },
                            }
                        }
                        Hint::AllocFrame { ptr, callee } => RHint::Alloc {
                            ptr,
                            size: frame_size[&callee],
                        },
                        Hint::AllocFrameMax { ptr, callees } => RHint::Alloc {
                            ptr,
                            size: callees.iter().map(|c| frame_size[c]).max().unwrap(),
                        },
                        Hint::AllocBuffer { ptr, size } => RHint::Alloc { ptr, size },
                        Hint::AllocBufferDyn { ptr, size } => RHint::AllocDyn { ptr, size },
                        Hint::Resolved(r) => r,
                    })
                    .collect();
                hints.insert(here, rhs);
            }
            src_lines.push(ins.line);
            prog.push(resolve(&ins.op, &entry, sentinel, pc0, l.frame_size, tables_base));
        }
    }

    
    prog.resize(bytecode_size, Op::Set { o: 0, k: F192::ZERO });
    let mut program = { export_schedule(&hints, frame_size["main"]); Program::assemble(prog, hints, frame_size["main"]) };
    program.src_lines = src_lines;
    program.fn_ranges = lowered
        .iter()
        .map(|l| (l.name.clone(), entry[&l.name], l.code.len() as u32))
        .collect();
    program
}




pub fn disassemble(prog: &[Op]) -> String {
    
    let mut gmap: HashMap<F64, usize> = HashMap::new();
    let mut acc = F64::ONE;
    for j in 0..(prog.len() + 512) {
        gmap.entry(acc).or_insert(j);
        acc *= primitives::field::G;
    }
    
    
    let kfmt = |k: F192| match (k.c1 == 0 && k.c2 == 0).then(|| gmap.get(&F64(k.c0))).flatten() {
        Some(j) => format!("g^{j}"),
        None if k.c1 == 0 && k.c2 == 0 => format!("0x{:016x}", k.c0),
        None => format!("0x{:016x}{:016x}{:016x}", k.c2, k.c1, k.c0),
    };

    let mut out = String::new();
    for (pc, op) in prog.iter().enumerate() {
        let line = match op {
            Op::Set { o, k } => format!("SET    fp[{o}] = {}", kfmt(*k)),
            Op::Xor { a, b, c } => format!("XOR    fp[{c}] = fp[{a}] ^ fp[{b}]"),
            Op::Mul { a, b, c } => format!("MUL    fp[{c}] = fp[{a}] * fp[{b}]"),
            Op::Deref { o1, o2, o3, mode } => {
                let src = match mode {
                    DerefMode::Cell => format!("fp[{o3}]"),
                    DerefMode::Pc => "g²·pc".to_string(),
                    DerefMode::Fp => "fp".to_string(),
                };
                format!("DEREF  *(fp[{o1}]·g^{o2}) = {src}  [{mode:?}]")
            }
            Op::Jump { oc, od, of } => {
                format!("JUMP   if fp[{oc}]≠0: pc=fp[{od}], fp=fp[{of}]")
            }
            Op::Keccak {
                m,
                tail,
                b8,
                cap,
                out,
                in_odd,
                out_odd,
            } => {
                let layout = |odd: bool| if odd { "odd" } else { "even" };
                format!(
                    "KECCAK fp[{out}..+13] {} = keccak_f(fp[{}],fp[{}],fp[{}],fp[{}], tail=fp[{tail}..+4], b8=fp[{b8}], cap=fp[{cap}..+4]) {}",
                    layout(*out_odd),
                    m[0],
                    m[1],
                    m[2],
                    m[3],
                    layout(*in_odd)
                )
            }
        };
        writeln!(out, "{:>6}  {line}", pretty_integer(pc)).unwrap();
    }
    out
}


pub(crate) fn lit_field(n: u128) -> F192 {
    F192::new(n as u64, (n >> 64) as u64, 0)
}




fn g_pow_u128(mut e: u128) -> F64 {
    let mut result = F64::ONE;
    let mut base = primitives::field::G;
    while e > 0 {
        if e & 1 == 1 {
            result *= base;
        }
        base = base * base;
        e >>= 1;
    }
    result
}

fn resolve(op: &LOp, entry: &HashMap<String, u32>, sentinel: u32, pc0: u32, frame_size: u32, tables: u32) -> Op {
    let resolve_kval = |kv: &KVal| -> F192 {
        match kv {
            KVal::FrameSize => g_pow(frame_size as usize).into(),
            KVal::Const(c) => *c,
            
            
            KVal::Entry(name) => g_pow(entry[name] as usize).into(),
            KVal::EndSentinel => g_pow(sentinel as usize).into(),
            KVal::Local(i) => g_pow((pc0 + i) as usize).into(),
            KVal::At(name, i) => g_pow((entry[name] + i) as usize).into(),
        }
    };
    match op {
        LOp::MulNextFrame { a, b, c } => Op::Mul {
            a: *a,
            b: *b,
            c: frame_size.checked_add(*c).expect("frame offset overflow"),
        },
        LOp::Set { o, k: kv } => Op::Set {
            o: *o,
            k: resolve_kval(kv),
        },
        LOp::Xor { a, b, c } => Op::Xor { a: *a, b: *b, c: *c },
        LOp::Mul { a, b, c } => Op::Mul { a: *a, b: *b, c: *c },
        LOp::Deref { o1, o2, o3, mode } => Op::Deref {
            o1: *o1,
            o2: *o2,
            o3: *o3,
            mode: *mode,
        },
        LOp::Slot { x, first, dst } => Op::Deref {
            o1: *x,
            o2: tables + first,
            o3: *dst,
            mode: DerefMode::Cell,
        },
        LOp::Jump { oc, od, of } => Op::Jump {
            oc: *oc,
            od: *od,
            of: *of,
        },
        LOp::Keccak {
            m,
            tail,
            b8,
            cap,
            c,
            in_odd,
            out_odd,
        } => Op::Keccak {
            m: *m,
            tail: *tail,
            b8: *b8,
            cap: *cap,
            out: *c,
            in_odd: *in_odd,
            out_odd: *out_odd,
        },
    }
}

fn export_schedule(hints: &HashMap<u32, Vec<RHint>>, main_frame: u32) {
    fn word(out: &mut Vec<u8>, x: u64) { out.extend(x.to_le_bytes()); }
    fn dest(out: &mut Vec<u8>, x: BitsDest) {
        match x {
            BitsDest::Stack(n) => { word(out, 0); word(out, n as u64); }
            BitsDest::Heap(n) => { word(out, 1); word(out, n as u64); }
        }
    }
    fn name(out: &mut Vec<u8>, x: &str) {
        word(out, x.len() as u64);
        out.extend(x.as_bytes());
    }
    let mut out = Vec::new();
    word(&mut out, main_frame as u64);
    word(&mut out, hints.len() as u64);
    let mut pcs: Vec<_> = hints.keys().copied().collect();
    pcs.sort();
    for pc in pcs {
        word(&mut out, pc as u64);
        word(&mut out, hints[&pc].len() as u64);
        for hint in &hints[&pc] {
            let mut n: Vec<u64> = vec![];
            let tag = match hint {
                RHint::FrameAddress { offset } => { n.push(*offset as u64); 0 }
                RHint::AllocFrames { ptr, size, end, start_inverse, tail } => {
                    n.extend([*ptr as u64,*size as u64,*end as u64,start_inverse.0,*tail as u64]); 1
                }
                RHint::Alloc { ptr,size } => { n.extend([*ptr as u64,*size as u64]); 2 }
                RHint::AllocDyn { ptr,size } => { n.extend([*ptr as u64,*size as u64]); 3 }
                RHint::WitnessStack { name: text,base,len } => {
                    word(&mut out,4); name(&mut out,text); n.extend([*base as u64,*len as u64]); u64::MAX
                }
                RHint::WitnessHeap { name: text,ptr,lo,len } => {
                    word(&mut out,5); name(&mut out,text); n.extend([*ptr as u64,*lo as u64,*len as u64]); u64::MAX
                }
                RHint::Log2Ceil { bits,dst,nbits,floor } => {
                    word(&mut out,6); dest(&mut out,*bits); n.extend([*dst as u64,*nbits as u64,*floor as u64]); u64::MAX
                }
                RHint::BitDecompose { value,bits,nbits,start } => {
                    word(&mut out,7); word(&mut out,*value as u64); dest(&mut out,*bits); n.extend([*nbits as u64,*start as u64]); u64::MAX
                }
                RHint::BitDecomposeExp { value,bits,nbits } => {
                    word(&mut out,8); word(&mut out,*value as u64); dest(&mut out,*bits); n.push(*nbits as u64); u64::MAX
                }
                RHint::DigitDecomposeExp { value,dst,nbits,ndigits,digit_bits,start,start_cell } => {
                    word(&mut out,9); word(&mut out,*value as u64); dest(&mut out,*dst);
                    n.extend([*nbits as u64,*ndigits as u64,*digit_bits as u64,*start as u64,start_cell.map_or(u64::MAX,|x| x as u64)]); u64::MAX
                }
                RHint::WindowsExp { value,dest: dst,at,start,width,count } => {
                    word(&mut out,10); word(&mut out,*value as u64); dest(&mut out,*dst);
                    n.extend([*at as u64,*start as u64,*width as u64,*count as u64]); u64::MAX
                }
                RHint::FieldLimbs { value,base,len } => { n.extend([*value as u64,*base as u64,*len as u64]); 11 }
                RHint::Inverse { value,dst } => { n.extend([*value as u64,*dst as u64]); 12 }
                RHint::Print { label,cell } => {
                    word(&mut out,13); name(&mut out,label); n.push(*cell as u64); u64::MAX
                }
            };
            if tag != u64::MAX { word(&mut out,tag); }
            for x in n { word(&mut out,x); }
        }
    }
    std::fs::write(std::env::args().nth(2).unwrap(),out).unwrap();
}

fn main() {
    let args: Vec<_> = std::env::args().collect();
    let replacements = std::fs::read_to_string(&args[1]).unwrap();
    let replacements: std::collections::BTreeMap<String,String> = replacements.lines().map(|line| {
        let (key,value) = line.split_once(" = ").unwrap();
        (key.to_string(),value.to_string())
    }).collect();
    let source = include_str!("/var/lib/sandboxed-node/.scratch/b2c1c0b9-4d89-47e7-ab06-c94b999a4cce/opencode/xmss-hub-unified/references/leanVM/crates/rec_aggregation/guests/lean_ethereum.py");
    let ast = parse_with_replacements(source,&replacements).unwrap();
    let program = compile(&ast);
    assert_eq!(program.prog.len(),1<<19);
    println!("instructions={} code={}",program.prog.len(),program.code_len());
}
