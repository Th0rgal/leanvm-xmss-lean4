use leanvm_core::cpu::{DerefMode, Op, fs_seed};
use primitives::field::F192;
use signatures::lean_xmss::{self, LeanXmssPublicKey, LeanXmssSignature};
use std::{fs, path::Path};

mod aggregation {
    pub fn count(n: usize) -> primitives::field::F192 { cells::count(n) }
    pub fn pack(bytes: &[u8]) -> primitives::field::F192 { cells::pack_16_bytes(bytes) }
    pub mod error {
        #[derive(Debug)]
        pub enum AggregationError {
            MalformedRawSignature,
        }
    }
    #[path = "/var/lib/orb-node/work/caches/xmss-hub-unified/references/leanVM/crates/rec_aggregation/src/aggregation/cells.rs"]
    pub mod cells;
    #[path = "/var/lib/orb-node/work/caches/xmss-hub-unified/references/leanVM/crates/rec_aggregation/src/aggregation/hints.rs"]
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

fn main() {
    let args: Vec<_> = std::env::args().collect();
    let input = fs::read(&args[1]).unwrap();
    let output = Path::new(&args[2]);
    fs::create_dir_all(output).unwrap();
    assert_eq!(input.len() % 2468, 0);
    let mut records: Vec<_> = input.chunks_exact(2468).collect();
    records.sort_by_key(|r| &r[..64]);
    records.dedup_by_key(|r| &r[..64]);
    let guest = rec_aggregation::aggregation::unified_guest();
    assert_eq!(guest.prog.len(), 1 << 19);
    let seed = fs_seed(guest);
    let table = leanvm_core::cpu::layout::bytecode_table(&guest.prog);
    let mut bytecode = Vec::new();
    for op in &guest.prog {
        let mut n = vec![];
        let tag = match *op {
            Op::Xor { a, b, c } => { n.extend([a as u64, b as u64, c as u64]); 0 }
            Op::Mul { a, b, c } => { n.extend([a as u64, b as u64, c as u64]); 1 }
            Op::Set { o, k } => { n.extend([o as u64, k.c0, k.c1, k.c2]); 2 }
            Op::Deref { o1, o2, o3, mode } => {
                n.extend([o1 as u64, o2 as u64, o3 as u64, match mode { DerefMode::Cell => 0, DerefMode::Pc => 1, DerefMode::Fp => 2 }]); 3
            }
            Op::Jump { oc, od, of } => { n.extend([oc as u64, od as u64, of as u64]); 4 }
            Op::Keccak { m, tail, b8, cap, out, in_odd, out_odd } => {
                n.extend(m.map(u64::from));
                n.extend([tail as u64, b8 as u64, cap as u64, out as u64, in_odd as u64, out_odd as u64]); 5
            }
        };
        bytecode.push(tag);
        for x in n { bytecode.extend(x.to_le_bytes()); }
    }
    fs::write(output.join("bytecode.bin"), &bytecode).unwrap();
    let mut seed_bytes = Vec::new();
    for v in seed { seed_bytes.extend(v.c0.to_le_bytes()); seed_bytes.extend(v.c1.to_le_bytes()); }
    fs::write(output.join("seed.bin"), &seed_bytes).unwrap();
    let value = F192::new(table[0].0, 0, 0);
    fs::write(output.join("bytecode-value.bin"), table[0].0.to_le_bytes()).unwrap();
    let mut hints = Vec::new();
    entry(&mut hints, "meta", &[count(records.len()), count(0), count(records.len()), count(0), count(0), count(0), count(0), count(0)]);
    entry(&mut hints, "fs_seed", &seed);
    if !records.is_empty() {
        let n = records.len();
        entry(&mut hints, "signers_split", &[count(n/136), count(n%136/17), count(n%17)]);
    }
    let mut claims = Vec::new();
    for r in &records {
        claims.extend(&r[..64]);
        let cells: Vec<_> = r[..64].chunks_exact(16).map(aggregation::pack).collect();
        entry(&mut hints, "claims", &cells);
    }
    for (i, r) in records.iter().enumerate() {
        let pk = LeanXmssPublicKey::from_bytes(r[..32].try_into().unwrap());
        let message = r[32..64].try_into().unwrap();
        let sig = LeanXmssSignature::from_bytes(r[64..].try_into().unwrap());
        lean_xmss::verify(&pk, &message, &sig).unwrap();
        entry(&mut hints, "raw_index", &[count(i)]);
        for (name, values) in aggregation::xmss(&pk, &sig, &message) {
            entry(&mut hints, name, &values);
        }
    }
    entry(&mut hints, "leaf_defer", &[value]);
    entry(&mut hints, "da_pick", &[count(0)]);
    fs::write(output.join("hints.bin"), &hints).unwrap();
    let mut statement = seed_bytes;
    statement.extend(primitives::hash::hash(&claims));
    statement.extend(primitives::hash::hash(&[]));
    statement.extend([0u8; 32]);
    statement.extend([0u8; 23*24]);
    word(&mut statement, value);
    let statement = primitives::hash::hash(&statement);
    fs::write(output.join("statement.bin"), statement).unwrap();
    let mut program = guest.clone();
    let mut streams: std::collections::BTreeMap<String, Vec<Vec<F192>>> = std::collections::BTreeMap::new();
    let mut cursor = 0;
    while cursor < hints.len() {
        let len = u32::from_le_bytes(hints[cursor..cursor+4].try_into().unwrap()) as usize;
        cursor += 4;
        let name = String::from_utf8(hints[cursor..cursor+len].to_vec()).unwrap();
        cursor += len;
        let n = u32::from_le_bytes(hints[cursor..cursor+4].try_into().unwrap()) as usize;
        cursor += 4;
        let mut values = Vec::new();
        for _ in 0..n {
            let a = u64::from_le_bytes(hints[cursor..cursor+8].try_into().unwrap());
            let b = u64::from_le_bytes(hints[cursor+8..cursor+16].try_into().unwrap());
            let c = u64::from_le_bytes(hints[cursor+16..cursor+24].try_into().unwrap());
            cursor += 24;
            values.push(F192::new(a,b,c));
        }
        streams.entry(name).or_default().push(values);
    }
    for (name, values) in streams { program.set_witness(name, values); }
    let pi = [aggregation::pack(&statement[..16]), aggregation::pack(&statement[16..])];
    let execution = program.execute(pi).unwrap();
    assert!(execution.unconstrained_reads.is_empty());
    if records.len() == 1400 { assert_eq!(execution.cycles, 1_146_537); }
    let mut memory = Vec::new();
    for i in 0..execution.mem_used { word(&mut memory, execution.mem.word(i)); }
    let rows = execution.rows();
    let report = format!("{{\"cycles\":{},\"memory_cells_used\":{},\"memory_keccak256\":\"{}\",\"rows\":{:?},\"unconstrained_reads\":[]}}", execution.cycles, execution.mem_used, hex(&primitives::hash::hash(&memory)), rows);
    fs::write(output.join("execution.json"), &report).unwrap();
    println!("{report}");
    let mut mutated = records[0][64..].to_vec();
    mutated[0] ^= 1;
    let pk = LeanXmssPublicKey::from_bytes(records[0][..32].try_into().unwrap());
    let message = records[0][32..64].try_into().unwrap();
    let sig = LeanXmssSignature::from_bytes(mutated.as_slice().try_into().unwrap());
    assert!(lean_xmss::verify(&pk, &message, &sig).is_err());
    println!("{{\"records\":{},\"padded_instructions\":{},\"code_instructions\":{},\"bytecode_keccak256\":\"{}\",\"hints_keccak256\":\"{}\",\"statement_digest\":\"{}\",\"signature_mutant_rejected\":true}}", records.len(), guest.prog.len(), guest.code_len(), hex(&primitives::hash::hash(&bytecode)), hex(&primitives::hash::hash(&hints)), hex(&statement));
}
