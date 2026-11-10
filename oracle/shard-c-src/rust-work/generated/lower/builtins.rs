












use super::*;

impl FnLower<'_> {
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    fn lower_keccak(&mut self, args: &[Expr]) {
        let kwargs = self.keccak_kwargs(args, "keccak", &["a", "b", "out"], &["tail", "len", "cap"]);
        let mut cells = self.keccak_operand(&args[0], 2);
        cells.extend(self.keccak_operand(&args[1], 2));
        if let Some(tail) = kwargs.get("tail") {
            cells.extend(self.keccak_operand(tail, 4));
        }
        if let Some(cap) = kwargs.get("cap") {
            if kwargs.contains_key("len") {
                self.fail("keccak cap= is an overwrite duplex step: it takes no len=")
            }
            let cap = self.prev_state(cap, 5).unwrap_or_else(|| {
                self.fail(format!(
                    "keccak cap= must be a previous {STATE_CELLS}-cell output or its last five cells"
                ))
            });
            cells.resize(8, SpongeCell::Zero);
            let out = self.keccak_out(&args[2]);
            let (m, tail) = self.keccak_rate(&cells, None);
            self.emit(LOp::Keccak {
                m,
                tail,
                b8: cap,
                cap: cap + 1,
                c: out.state,
                in_odd: false,
                out_odd: false,
            });
            self.keccak_finish(out);
            return;
        }
        let len = self.keccak_len(&kwargs, cells.len() as u32);
        let out = self.keccak_out(&args[2]);
        self.emit_keccak_message(cells, Some(len), None, out.state);
        self.keccak_finish(out);
    }

    
    
    
    
    
    
    
    
    
    
    fn lower_keccak_cells(&mut self, args: &[Expr]) {
        let kwargs = self.keccak_kwargs(args, "keccak_cells", &["cells", "out"], &["state", "len", "final"]);
        let comprehension;
        let list = match &args[0] {
            Expr::ListComp(body, var, lo, hi) => {
                let bound = |e: &Expr| {
                    self.try_const_int(e).unwrap_or_else(|| {
                        self.fail(format!(
                            "a list comprehension's bounds must be compile-time integers, got `{e:?}`"
                        ))
                    })
                };
                comprehension = Expr::ListLit(
                    (bound(lo)..bound(hi))
                        .map(|i| crate::parser::subst_var(body, var, &Expr::Lit(i)))
                        .collect(),
                );
                &comprehension
            }
            e => e,
        };
        let cells = self.sponge_cells(list);
        if cells.is_empty() {
            self.fail("keccak_cells hashes at least one cell")
        }
        let is_final = match kwargs.get("final") {
            Some(e) => {
                self.try_const_int(e)
                    .unwrap_or_else(|| self.fail(format!("keccak `final` must be a compile-time integer, got `{e:?}`")))
                    != 0
            }
            None => true,
        };
        let final_len = if is_final {
            Some(self.keccak_len(&kwargs, cells.len() as u32))
        } else {
            if kwargs.contains_key("len") {
                self.fail("keccak_cells final=0 absorbs whole cells: it takes no len=")
            }
            None
        };
        let state = kwargs.get("state").map(|state| {
            self.prev_state(state, STATE_CELLS).unwrap_or_else(|| {
                self.fail(format!(
                    "keccak_cells state= must be the {STATE_CELLS}-cell run a previous keccak wrote"
                ))
            })
        });
        let out = self.keccak_out(&args[1]);
        self.emit_keccak_message(cells, final_len, state, out.state);
        self.keccak_finish(out);
    }

    
    fn keccak_len(&self, kwargs: &HashMap<&str, &Expr>, n: u32) -> u32 {
        let Some(e) = kwargs.get("len") else { return 16 * n };
        let len = self
            .try_const_int(e)
            .unwrap_or_else(|| self.fail(format!("keccak `len` must be a compile-time integer, got `{e:?}`")));
        if len > u128::from(16 * n) {
            self.fail(format!(
                "keccak len= {len} is past the {} bytes of its {n} cells",
                16 * n
            ))
        };
        len as u32
    }

    
    fn keccak_kwargs<'e>(
        &self,
        args: &'e [Expr],
        f: &str,
        positional: &[&str],
        allowed: &[&str],
    ) -> HashMap<&'e str, &'e Expr> {
        let first_kw = args
            .iter()
            .position(|a| matches!(a, Expr::Call(name, _) if name.starts_with("__kw_")))
            .unwrap_or(args.len());
        if first_kw != positional.len() {
            self.fail(format!(
                "{f} takes {} positional arguments: ({})",
                positional.len(),
                positional.join(", ")
            ))
        };
        let kws = &args[first_kw..];
        if !(kws
            .iter()
            .all(|a| matches!(a, Expr::Call(name, v) if name.starts_with("__kw_") && v.len() == 1)))
        {
            self.fail("keyword arguments must follow the positional keccak arguments")
        };
        let mut kwargs: HashMap<&str, &Expr> = HashMap::new();
        for kw in kws {
            let Expr::Call(name, value) = kw else { unreachable!() };
            let key = name.strip_prefix("__kw_").unwrap();
            if kwargs.insert(key, &value[0]).is_some() {
                self.fail(format!("duplicate keccak keyword `{key}`"))
            };
        }
        if !(kwargs.keys().all(|k| allowed.contains(k))) {
            
            
            let mut bad: Vec<&&str> = kwargs.keys().filter(|k| !allowed.contains(k)).collect();
            bad.sort_unstable();
            self.fail(format!("unknown keccak keyword {bad:?}; the keywords are {allowed:?}"))
        };
        kwargs
    }

    
    
    fn keccak_out(&mut self, e: &Expr) -> KeccakOut {
        match self.cell_run(e) {
            CellRun::Stack { base, len } if len >= STATE_CELLS => KeccakOut {
                state: base,
                copy: None,
            },
            run @ (CellRun::Heap { len: STATE_CELLS, .. }
            | CellRun::Stack { len: 2, .. }
            | CellRun::Heap { len: 2, .. }) => KeccakOut {
                state: self.alloc_stack(STATE_CELLS),
                copy: Some(run),
            },
            _ => self.fail(format!(
                "a keccak destination is a {STATE_CELLS}-cell run (the state) or a 2-cell run (the digest)"
            )),
        }
    }

    
    fn keccak_finish(&mut self, out: KeccakOut) {
        match out.copy {
            None => {}
            Some(CellRun::Stack { base, len }) => {
                for k in 0..len {
                    self.copy(out.state + k, base + k);
                }
            }
            Some(CellRun::Heap { ptr, lo, len }) => self.deref_run(ptr, lo, len, out.state),
        }
    }

    
    
    
    fn emit_keccak_message(
        &mut self,
        mut cells: Vec<SpongeCell>,
        final_len: Option<u32>,
        state: Option<Off>,
        out: Off,
    ) {
        let blocks = match final_len {
            Some(len) => len as usize / RATE + 1,
            None => (16 * cells.len()).div_ceil(RATE),
        };
        
        let read = 17 * (blocks - 1) / 2 + BLOCK_CELLS as usize;
        if cells.len() < read {
            cells.resize(read, SpongeCell::Zero);
        }
        if let Some(len) = final_len {
            
            
            let past = (len as usize).div_ceil(16);
            if let Some(k) = (past..cells.len()).find(|&k| !matches!(cells[k], SpongeCell::Zero)) {
                self.fail(format!(
                    "keccak len= {len} ends before message cell {k}, which is not a literal 0"
                ))
            }
            self.xor_byte(&mut cells, len as usize, primitives::hash::PAD_FIRST);
            self.xor_byte(&mut cells, blocks * RATE - 1, primitives::hash::PAD_LAST);
        }
        
        
        let mut state = state;
        for k in 0..blocks {
            let last = k + 1 == blocks;
            let c = if last { out } else { self.alloc_stack(STATE_CELLS) };
            let block = &cells[17 * k / 2..][..BLOCK_CELLS as usize];
            let (m, tail) = self.keccak_rate(block, state);
            let b8 = match state {
                None => self.sponge_cell(block[8]),
                Some(st) => self.sponge_xor(st + 8, block[8], None),
            };
            let cap = state.map_or_else(|| self.keccak_pad_run() + 1, |st| st + 9);
            self.emit(LOp::Keccak {
                m,
                tail,
                b8,
                cap,
                c,
                in_odd: k % 2 == 1,
                out_odd: !last && k % 2 == 0,
            });
            state = Some(c);
        }
    }

    
    fn xor_byte(&mut self, cells: &mut [SpongeCell], at: usize, v: u8) {
        let (cell, byte) = (at / 16, at % 16);
        let w = u64::from(v) << (8 * (byte % 8));
        let v = if byte < 8 {
            F192::new(w, 0, 0)
        } else {
            F192::new(0, w, 0)
        };
        cells[cell] = match cells[cell] {
            SpongeCell::Zero => SpongeCell::Const(v),
            SpongeCell::Const(c) => SpongeCell::Const(c + v),
            SpongeCell::Cell(o) => {
                let (k, dst) = (self.const_cell(v), self.fresh());
                self.emit(LOp::Xor { a: o, b: k, c: dst });
                SpongeCell::Cell(dst)
            }
        };
    }

    
    
    fn keccak_rate(&mut self, block: &[SpongeCell], st: Option<Off>) -> ([Off; 4], Off) {
        let Some(st) = st else {
            return (
                [0, 1, 2, 3].map(|i| self.sponge_cell(block[i])),
                self.sponge_run(&block[4..8]),
            );
        };
        let m = [0, 1, 2, 3].map(|i| self.sponge_xor(st + i, block[i as usize], None));
        if block[4..8].iter().all(|c| matches!(c, SpongeCell::Zero)) {
            return (m, st + 4);
        }
        let tail = self.alloc_stack(4);
        for j in 0..4 {
            self.sponge_xor(st + 4 + j, block[4 + j as usize], Some(tail + j));
        }
        (m, tail)
    }

    
    
    fn sponge_xor(&mut self, state: Off, c: SpongeCell, dst: Option<Off>) -> Off {
        let other = match c {
            SpongeCell::Zero => {
                return match dst {
                    Some(d) => {
                        self.copy(state, d);
                        d
                    }
                    None => state,
                };
            }
            c => self.sponge_cell(c),
        };
        let d = dst.unwrap_or_else(|| self.fresh());
        self.emit(LOp::Xor {
            a: state,
            b: other,
            c: d,
        });
        d
    }

    
    
    fn sponge_run(&mut self, cells: &[SpongeCell]) -> Off {
        let at = |k: usize| match cells[k] {
            SpongeCell::Cell(o) => o.checked_sub(k as u32),
            _ => None,
        };
        if let Some(base) = at(0)
            && (1..cells.len()).all(|k| at(k) == Some(base))
        {
            return base;
        }
        let zero = |c: &SpongeCell| matches!(c, SpongeCell::Zero);
        if cells.iter().all(zero) {
            return self.keccak_pad_run() + 1;
        }
        if matches!(cells[0], SpongeCell::Const(v) if v == keccak_pad_value()) && cells[1..].iter().all(zero) {
            return self.keccak_pad_run();
        }
        let t = self.alloc_stack(cells.len() as u32);
        for (j, &c) in cells.iter().enumerate() {
            let dst = t + j as u32;
            match c {
                SpongeCell::Zero => self.set_const(dst, F192::ZERO),
                SpongeCell::Const(v) => self.set_const(dst, v),
                SpongeCell::Cell(o) => self.copy(o, dst),
            }
        }
        t
    }

    
    
    
    
    
    
    pub(super) fn lower_builtin(&mut self, f: &str, args: &[Expr]) -> bool {
        match f {
            "hint_decompose_bits" | "hint_decompose_bits_exponent" => {
                let plain = f == "hint_decompose_bits";
                if args.len() != 3 && !(plain && args.len() == 4) {
                    self.fail(format!(
                        "{f} takes `(bits, value, nbits{})`, got {} arguments",
                        if plain { "[, start]" } else { "" },
                        args.len()
                    ))
                };
                let nbits = self.const_index(&args[2]);
                
                if !plain && nbits > 64 {
                    self.fail(format!("{f} writes at most 64 bits, got {nbits}"))
                }
                let bits = self.bits_dest(&args[0], nbits, f);
                let value = self.expr(&args[1]);
                self.pending.push(Hint::Resolved(if plain {
                    let start = args.get(3).map_or(0, |start| self.const_index(start));
                    let end = u64::from(start) + u64::from(nbits);
                    if end > 192 {
                        self.fail(format!("{f} reads bits {start}..{end} of a 192-bit word"))
                    };
                    RHint::BitDecompose {
                        value,
                        bits,
                        nbits,
                        start,
                    }
                } else {
                    RHint::BitDecomposeExp { value, bits, nbits }
                }));
            }
            "hint_windows_exponent" => {
                if !(5..=6).contains(&args.len()) {
                    self.fail(format!(
                        "{f} takes `(dest, value, start, width, count[, at])`, got {} arguments",
                        args.len()
                    ))
                };
                let start = self.const_index(&args[2]);
                let width = self.const_index(&args[3]);
                let count = self.const_index(&args[4]);
                if !(1..=16).contains(&width) || u64::from(start) + u64::from(width * count) > 192 {
                    self.fail(format!("{f}: windows of 1..=16 bits inside a 192-bit word"))
                };
                let at = args.get(5).map_or(0, |at| self.const_index(at));
                let dest = self.bits_dest(&args[0], at + count, f);
                let value = self.expr(&args[1]);
                self.pending.push(Hint::Resolved(RHint::WindowsExp {
                    value,
                    dest,
                    at,
                    start,
                    width,
                    count,
                }));
            }
            "hint_decompose_digits_exponent" => {
                
                
                
                if args.len() != 6 {
                    self.fail(format!(
                        "{f} takes `(dest, value, nbits, ndigits, digit_bits, start)`, got {} arguments",
                        args.len()
                    ))
                };
                let nbits = self.const_index(&args[2]);
                let ndigits = self.const_index(&args[3]);
                let digit_bits = self.const_index(&args[4]);
                if nbits > 64 || !(1..=16).contains(&digit_bits) {
                    self.fail(format!("{f}: nbits <= 64 and 1 <= digit_bits <= 16"))
                }
                let dst = self.bits_dest(&args[0], ndigits, f);
                let value = self.expr(&args[1]);
                let (start, start_cell) = match self.try_const_index(&args[5]) {
                    Some(k) => (k, None),
                    None => (0, Some(self.expr(&args[5]))),
                };
                self.pending.push(Hint::Resolved(RHint::DigitDecomposeExp {
                    value,
                    dst,
                    nbits,
                    ndigits,
                    digit_bits,
                    start,
                    start_cell,
                }));
            }
            "keccak" => self.lower_keccak(args),
            "keccak_cells" => self.lower_keccak_cells(args),
            "assert_in_k" => {
                if args.len() != 2 {
                    self.fail("assert_in_k(a, b) takes two scalar cells")
                };
                let a = self.expr(&args[0]);
                let b = self.expr(&args[1]);
                let zero = self.zero();
                self.emit(LOp::Jump { oc: zero, od: a, of: b });
            }
            "assert_gpow" => {
                
                
                if args.len() != 1 {
                    self.fail("assert_gpow(x) takes one scalar cell")
                };
                let x = self.expr(&args[0]);
                let t = self.fresh();
                self.deref(x, 0, t, DerefMode::Cell);
            }
            "hint_f192_limbs" => {
                if args.len() != 2 {
                    self.fail(format!(
                        "hint_f192_limbs takes two arguments, `(dest, value)`, got {}",
                        args.len()
                    ))
                };
                let (base, len) = self.stack_of(&args[0]).unwrap_or_else(|| {
                    self.fail(format!(
                        "hint_f192_limbs writes 1..=3 frame cells, so its destination must be a \
                             StackBuf, got `{:?}`",
                        args[0]
                    ))
                });
                if !((1..=3).contains(&len)) {
                    self.fail("hint_f192_limbs destination must have 1..=3 cells")
                };
                let value = self.expr(&args[1]);
                
                
                
                self.pending
                    .push(Hint::Resolved(RHint::FieldLimbs { value, base, len }));
            }
            _ => return false,
        }
        true
    }

    
    
    
    fn sponge_cells(&mut self, e: &Expr) -> Vec<SpongeCell> {
        if let Expr::ListLit(words) = e {
            return words
                .iter()
                .map(|w| match self.try_const_int(w) {
                    Some(0) => SpongeCell::Zero,
                    _ => SpongeCell::Cell(self.expr(w)),
                })
                .collect();
        }
        let (base, len) = match self.cell_run(e) {
            CellRun::Stack { base, len } => (base, len),
            CellRun::Heap { ptr, lo, len } => (self.heap_to_stack(ptr, lo, len), len),
        };
        (0..len).map(|k| SpongeCell::Cell(base + k)).collect()
    }

    
    fn keccak_operand(&mut self, e: &Expr, n: usize) -> Vec<SpongeCell> {
        let cells = self.sponge_cells(e);
        if cells.len() != n {
            match e {
                Expr::ListLit(_) => self.fail(format!(
                    "a keccak operand written as a list needs exactly {n} words, got {}",
                    cells.len()
                )),
                _ => self.fail(format!(
                    "this keccak operand spans exactly {n} cells; slice a larger buffer: `buf[lo:lo + {n}]`"
                )),
            }
        }
        cells
    }

    
    
    fn prev_state(&mut self, e: &Expr, n: u32) -> Option<Off> {
        match self.try_cell_run(e).ok()? {
            CellRun::Stack { base, len } if len >= STATE_CELLS => Some(base + STATE_CELLS - n),
            CellRun::Stack { base, len } if len == n => Some(base),
            CellRun::Heap { ptr, lo, len } if len == STATE_CELLS || len == n => {
                Some(self.heap_to_stack(ptr, lo + len - n, n))
            }
            _ => None,
        }
    }

    
    fn try_cell_run(&mut self, e: &Expr) -> Result<CellRun, ()> {
        match e {
            Expr::Var(_) | Expr::Slice(..) => Ok(self.cell_run(e)),
            _ => Err(()),
        }
    }

    
    fn sponge_cell(&mut self, c: SpongeCell) -> Off {
        match c {
            SpongeCell::Zero => self.keccak_pad_run() + 1,
            SpongeCell::Const(v) if v == keccak_pad_value() => self.keccak_pad_run(),
            SpongeCell::Const(v) => self.const_cell(v),
            SpongeCell::Cell(o) => o,
        }
    }

    
    
    
    pub(super) fn keccak_pad_run(&mut self) -> Off {
        if let Some(o) = self.scope.keccak_pad {
            return o;
        }
        let o = self.alloc_stack(5);
        for k in 0..5 {
            let value = if k == 0 { keccak_pad_value() } else { F192::ZERO };
            self.set_const(o + k, value);
            self.scope
                .const_cells
                .entry([value.c0, value.c1, value.c2])
                .or_insert(o + k);
        }
        self.scope.keccak_pad = Some(o);
        o
    }

    
    
    
    pub(super) fn bits_dest(&mut self, e: &Expr, nbits: u32, what: &str) -> BitsDest {
        match self.stack_of(e) {
            Some((base, len)) => {
                if len < nbits {
                    self.fail(format!(
                        "{what} needs {nbits} cells, its StackBuf destination has {len}"
                    ))
                };
                
                BitsDest::Stack(base)
            }
            None => {
                
                
                
                
                
                self.check_heap_bound(e, 0, u128::from(nbits));
                BitsDest::Heap(self.expr(e))
            }
        }
    }

    
    
    
    pub(super) fn lower_hint_witness(&mut self, dest: &Expr, name: &str) {
        let name = name.to_string();
        let hint = match self.cell_run(dest) {
            CellRun::Stack { base, len } => RHint::WitnessStack { name, base, len },
            CellRun::Heap { ptr, lo, len } => RHint::WitnessHeap { name, ptr, lo, len },
        };
        self.pending.push(Hint::Resolved(hint));
    }
}


const STATE_CELLS: u32 = leanvm_core::keccak::STATE_CELLS as u32;

const BLOCK_CELLS: u32 = leanvm_core::keccak::RATE_CELLS as u32;

const RATE: usize = primitives::hash::RATE;


pub(super) fn two_to_one_close() -> F192 {
    F192::new(0x80 << 56, 0, 0)
}


fn keccak_pad_value() -> F192 {
    F192::new(u64::from(primitives::hash::PAD_FIRST), 0, 0)
}



struct KeccakOut {
    state: Off,
    copy: Option<CellRun>,
}


#[derive(Clone, Copy, Debug)]
enum SpongeCell {
    Zero,
    Const(F192),
    Cell(Off),
}
