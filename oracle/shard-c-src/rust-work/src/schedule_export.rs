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
