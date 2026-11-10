












use super::*;

impl FnLower<'_> {
    
    
    
    
    
    pub(super) fn cell_run(&mut self, e: &Expr) -> CellRun {
        match e {
            Expr::Var(_) => {
                let (base, len) = self.stack_of(e).unwrap_or_else(|| {
                    self.fail(format!(
                        "only a StackBuf names a run of cells unsliced, got `{e:?}`; slice a \
                             HeapBuf instead: `buf[lo:lo + k]`"
                    ))
                });
                CellRun::Stack { base, len }
            }
            Expr::Slice(arr, lo, hi) => match (self.try_const_index(lo), self.try_const_index(hi)) {
                
                
                (Some(lo), Some(hi)) => {
                    if lo >= hi {
                        self.fail(format!("empty slice {lo}:{hi}"))
                    };
                    let len = hi - lo;
                    if let Some((base, size)) = self.stack_of(arr) {
                        if hi > size {
                            self.fail(format!("slice {lo}:{hi} out of bounds (StackBuf size {size})"))
                        };
                        CellRun::Stack { base: base + lo, len }
                    } else {
                        self.check_heap_bound(arr, lo as u128, len as u128);
                        let (ptr, lo) = self.heap_base(arr, lo as u128);
                        CellRun::Heap { ptr, lo, len }
                    }
                }
                
                
                
                
                _ => {
                    if self.stack_of(arr).is_some() {
                        self.fail(
                            "a StackBuf slice needs compile-time bounds (frame offsets are baked into the bytecode)",
                        )
                    };
                    let k = plus_k(lo, hi).unwrap_or_else(|| {
                        self.fail(format!("a runtime slice must be `buf[i:i + k]`, got `{lo:?}:{hi:?}`"))
                    });
                    let len =
                        u32::try_from(k).unwrap_or_else(|_| self.fail(format!("slice length {k} does not fit in u32")));
                    if len == 0 {
                        self.fail(format!(
                            "a runtime slice `{lo:?}:{hi:?}` has length 0, so it names no cell"
                        ))
                    };
                    
                    
                    
                    
                    if let Some(GAddr { base: None, exp, .. }) = self.gaddr_of(lo) {
                        self.check_heap_bound(arr, exp, u128::from(len));
                    }
                    let (ptr, lo) = self.heap_addr(arr, lo);
                    CellRun::Heap { ptr, lo, len }
                }
            },
            other => self.fail(format!(
                "expected a StackBuf, a StackBuf slice, or a HeapBuf slice, got `{other:?}`"
            )),
        }
    }

    
    
    pub(super) fn heap_addr(&mut self, arr: &Expr, idx: &Expr) -> (Off, u32) {
        
        
        
        
        
        
        
        
        
        let bare_int = matches!(self.try_lit(idx), Some(n) if n != 1);
        let known = self.eval(idx);
        if (bare_int || known.addr.is_none())
            && let Some(c) = known.field
        {
            
            
            
            let why = match self.const_gpow(idx) {
                Some(k) => format!(
                    "is a plain integer naming cell {k}, while the slice `buf[n:n + 1]` reads the \
                     same number as cell n. Write `buf[GEN ** {k}]` and say which you mean"
                ),
                None => format!(
                    "folds to the field constant {:#x}:{:#x}, which is not a g-power, so it names \
                     no heap cell (did an integer index leak in from a StackBuf conversion?)",
                    c.c1, c.c0
                ),
            };
            self.fail(format!("heap index {why}"));
        }
        match known.addr {
            Some(GAddr { base: None, exp, .. }) => return self.heap_base(arr, exp),
            
            
            
            
            Some(GAddr {
                base: Some(ib), exp, ..
            }) => {
                if let Some(ga) = self.gaddr_of(arr)
                    && let (Some(ab), Some(total)) = (ga.base, ga.exp.checked_add(exp))
                    && total <= FOLD_MAX
                {
                    let ptr = self.pure(PureOp::Mul, ab, ib);
                    return (ptr, total as u32);
                }
            }
            None => {}
        }
        
        
        self.array_ptr(arr, idx)
    }

    
    
    
    
    pub(super) fn check_heap_bound(&self, arr: &Expr, extra: u128, span: u128) {
        let Some(ga) = self.gaddr_of(arr) else { return };
        let (Some(base), Some(exp)) = (ga.base, ga.exp.checked_add(extra)) else {
            return;
        };
        
        
        
        if let Some((start, len)) = ga.run {
            let (start, len) = (start as u128, len as u128);
            if exp < start || exp + span > start + len {
                let off = exp.saturating_sub(start); 
                let what = if span == 1 {
                    format!("index {off}")
                } else {
                    format!("slice {off}:{}", off + span)
                };
                self.fail(format!(
                    "frame {what} out of bounds for the StackBuf({len}) named by `addr`"
                ));
            }
            return;
        }
        let Some(&size) = self.heap_sizes.get(&base) else {
            return;
        };
        if exp + span > size {
            
            
            
            let name = self
                .scope
                .names
                .iter()
                .filter(|(_, b)| matches!(b.val, Binding::Scalar(c) if c == base))
                .map(|(n, _)| n.as_str())
                .min()
                .unwrap_or("?");
            if span == 1 {
                self.fail(format!(
                    "heap index {exp} out of bounds for `{name}` (HeapBuf size {size})"
                ));
            }
            self.fail(format!(
                "heap slice {exp}:{} out of bounds for `{name}` (HeapBuf size {size})",
                exp + span
            ));
        }
    }

    
    
    
    
    
    pub(super) fn stack_addr(&mut self, args: &[Expr]) -> GAddr {
        if args.len() != 1 {
            self.fail("addr(buf) takes one StackBuf")
        };
        let (base, len) = self.stack_of(&args[0]).unwrap_or_else(|| {
            self.fail(format!(
                "addr() names a frame run, so it takes a StackBuf, got `{:?}`",
                args[0]
            ))
        });
        GAddr {
            base: Some(self.self_fp()),
            exp: base as u128,
            run: Some((base, len)),
        }
    }

    
    
    
    fn heap_base(&mut self, arr: &Expr, extra: u128) -> (Off, u32) {
        self.check_heap_bound(arr, extra, 1);
        if let Some(ga) = self.gaddr_of(arr)
            && let (Some(base), Some(exp)) = (ga.base, ga.exp.checked_add(extra))
            && exp <= FOLD_MAX
        {
            return (base, exp as u32);
        }
        let a = self.expr(arr);
        if extra == 0 {
            return (a, 0);
        }
        let k = self.const_cell(g_pow_u128(extra).into());
        (self.pure(PureOp::Mul, a, k), 0)
    }

    
    
    
    
    
    
    
    fn array_ptr(&mut self, arr: &Expr, idx: &Expr) -> (Off, u32) {
        
        
        if let Expr::Mul(a, b) = idx {
            for (c, r) in [(a, b), (b, a)] {
                if let Some(k) = self.const_gpow(c) {
                    let (la, lr) = (self.expr(arr), self.expr(r));
                    return (self.pure(PureOp::Mul, la, lr), k);
                }
            }
        }
        let (la, li) = (self.expr(arr), self.expr(idx));
        (self.pure(PureOp::Mul, la, li), 0)
    }

    
    
    
    pub(super) fn materialize(&mut self, ga: GAddr) -> Off {
        match ga {
            GAddr {
                base: Some(c), exp: 0, ..
            } => c,
            GAddr { base: None, exp, .. } => self.const_cell(g_pow_u128(exp).into()),
            GAddr { base: Some(c), exp, .. } => {
                let mats = self.scope.mat_cells.get(&c).cloned().unwrap_or_default();
                if let Some(&(_, o)) = mats.iter().find(|m| m.0 == exp) {
                    return o;
                }
                let has = |s: &Self, e: u128| {
                    let v: F192 = g_pow_u128(e).into();
                    s.scope.const_cells.contains_key(&[v.c0, v.c1, v.c2])
                };
                
                
                
                let from = if has(self, exp) {
                    None
                } else {
                    std::iter::once((0, c))
                        .chain(mats.iter().copied())
                        .filter(|&(e, _)| e < exp && has(self, exp - e))
                        .max_by_key(|&(e, _)| e)
                };
                let (src, k) = match from {
                    Some((e, src)) => (src, self.const_cell(g_pow_u128(exp - e).into())),
                    None => (c, self.const_cell(g_pow_u128(exp).into())),
                };
                let o = self.pure(PureOp::Mul, src, k);
                self.scope.mat_cells.entry(c).or_default().push((exp, o));
                o
            }
        }
    }

    
    pub(super) fn stack_of(&self, e: &Expr) -> Option<(Off, u32)> {
        match e {
            Expr::Var(v) => self.scope.stack(v),
            _ => None,
        }
    }

    
    
    pub(super) fn alloc_stack(&mut self, n: u32) -> Off {
        let base = self.next;
        self.next = base
            .checked_add(n)
            .unwrap_or_else(|| self.fail("the frame outgrows 2^32 cells"));
        base
    }

    
    pub(super) fn heap_to_stack(&mut self, ptr: Off, lo: u32, len: u32) -> Off {
        let run = self.alloc_stack(len);
        self.deref_run(ptr, lo, len, run);
        run
    }

    
    
    pub(super) fn deref_run(&mut self, ptr: Off, lo: u32, len: u32, run: Off) {
        for k in 0..len {
            self.deref(ptr, lo + k, run + k, DerefMode::Cell);
        }
    }
}
