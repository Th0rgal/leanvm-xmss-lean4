




















use super::*;

mod builtins;
mod call;
mod eval;
mod mem;
use call::ret_binding;
use eval::field_pow;







#[derive(Clone, Copy)]
struct GAddr {
    base: Option<Off>,
    exp: u128,
    
    
    
    
    
    
    run: Option<(Off, u32)>,
}






struct Abi;

impl Abi {
    
    const RET_PC: Off = 0;
    const RET_FP: Off = 1;
    
    fn arg(shapes: impl Iterator<Item = Shape>, i: usize) -> Off {
        2 + shapes.take(i).map(Shape::cells).sum::<u32>()
    }
    
    fn arg_cells(shapes: impl Iterator<Item = Shape>) -> u32 {
        shapes.map(Shape::cells).sum()
    }
    
    fn ret(arg_cells: u32, i: u32) -> Off {
        2 + arg_cells + i
    }
    
    fn end(arg_cells: u32, n_ret_cells: u32) -> Off {
        Self::ret(arg_cells, n_ret_cells)
    }
}





const FOLD_MAX: u128 = 1 << leanvm_core::cpu::MIN_LOG_MEM;



#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum PureOp {
    Xor,
    Mul,
}






#[derive(Clone, Copy)]
enum RetBind {
    Stack(Off, u32),
    Gaddr(GAddr),
    Scalar,
}



#[derive(Clone, Copy)]
enum Binding {
    Scalar(Off),
    Stack(Off, u32),
    Gaddr(GAddr),
    FConst(F192),
}






#[derive(Clone, Copy)]
struct Bound {
    val: Binding,
    int: Option<u128>,
}





#[derive(Clone, Default)]
struct Scope {
    names: HashMap<String, Bound>,
    
    
    
    self_fp_off: Option<Off>,
    
    
    
    
    
    
    
    
    
    
    pure_cells: HashMap<(PureOp, Off, Off), Off>,
    
    
    load_cells: HashMap<(Off, u32), Off>,
    
    
    
    
    
    const_cells: HashMap<[u64; 3], Off>,
    
    
    
    mat_cells: HashMap<Off, Vec<(u128, Off)>>,
    
    
    
    
    keccak_pad: Option<Off>,
}

impl Scope {
    fn bound(&self, n: &str) -> Option<Bound> {
        self.names.get(n).copied()
    }
    fn stack(&self, n: &str) -> Option<(Off, u32)> {
        match self.bound(n)?.val {
            Binding::Stack(base, size) => Some((base, size)),
            _ => None,
        }
    }
    
    fn int(&self, n: &str) -> Option<u128> {
        self.bound(n)?.int
    }
    
    fn set_int(&mut self, n: &str, k: u128) {
        if let Some(b) = self.names.get_mut(n) {
            b.int = Some(k);
        }
    }
}

struct FnLower<'a> {
    scope: Scope,
    next: Off,
    
    
    arg_cells: u32,
    
    
    return_shapes: &'a [Shape],
    is_main: bool,
    code: Vec<LInstr>,
    
    
    
    heap_sizes: HashMap<Off, u128>,
    
    
    
    inline_ret: Option<Vec<Off>>,
    
    
    
    
    inline_stack_ret: Option<Vec<RetBind>>,
    
    
    cur_line: u32,
    
    pending: Vec<Hint>,
    
    
    chain_next: Option<ChainNext>,
    
    
    chain_in: Option<ChainIn>,
    
    
    
    inline_calls: Vec<String>,
    
    
    
    tail_call: bool,
    
    loop_bounds: &'a mut HashMap<String, (u64, Option<u64>)>,
    queue: &'a mut Vec<Func>,
    loop_ctr: &'a mut usize,
    
    fn_name: &'a str,
    
    
    defs: &'a HashMap<&'a str, &'a Func>,
    
    
    const_arrays: &'a HashMap<&'a str, &'a [F192]>,
    
    tables: &'a mut JumpTables,
}


struct ChainNext {
    xo: Off,
    n: usize,
}



struct ChainIn {
    first: usize,
    join: Off,
    jset: usize,
}

impl FnLower<'_> {
    
    
    
    
    fn fail(&self, msg: impl std::fmt::Display) -> ! {
        
        
        
        
        
        
        let site = match (self.cur_line, self.fn_name) {
            (0, "main") => String::new(),
            (0, f) => format!("in {f}: "),
            (n, "main") => format!("line {n}: "),
            (n, f) => format!("line {n} in {f}: "),
        };
        match self.inline_calls.as_slice() {
            [] => panic!("{site}{msg}"),
            chain => panic!("{site}{msg} (inlined through {})", chain.join(" -> ")),
        }
    }

    fn fresh(&mut self) -> Off {
        self.alloc_stack(1)
    }

    fn emit(&mut self, op: LOp) {
        let hints = std::mem::take(&mut self.pending);
        self.code.push(LInstr {
            op,
            line: self.cur_line,
            hints,
        });
    }

    fn set(&mut self, o: Off, k: KVal) {
        self.emit(LOp::Set { o, k });
    }

    fn set_const(&mut self, o: Off, v: F192) {
        self.set(o, KVal::Const(v));
    }

    fn deref(&mut self, o1: Off, o2: u32, o3: Off, mode: DerefMode) {
        self.emit(LOp::Deref { o1, o2, o3, mode });
        if mode == DerefMode::Cell {
            self.scope.load_cells.entry((o1, o2)).or_insert(o3);
        }
    }

    
    
    
    fn anchor(&mut self) {
        let o = self.fresh();
        self.set_const(o, F192::ZERO);
    }

    
    
    
    
    
    
    
    
    fn check_not_reserved(&self, name: &str) {
        if self.const_arrays.contains_key(name) {
            self.fail(format!(
                "`{name}` is a top-level constant array, so the name is reserved: rename the local \
             or parameter (zkDSL.md §Global constants)"
            ))
        };
    }

    
    fn rebind(&mut self, name: &str, b: Binding) {
        self.check_not_reserved(name);
        self.scope.names.insert(name.to_string(), Bound { val: b, int: None });
    }

    
    
    fn bind_targets(&mut self, binds: &[(&str, Off)]) {
        for (name, cell) in binds {
            self.rebind(name, Binding::Scalar(*cell));
        }
    }

    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    fn pure(&mut self, op: PureOp, a: Off, b: Off) -> Off {
        let key = (op, a.min(b), a.max(b));
        if let Some(&o) = self.scope.pure_cells.get(&key) {
            return o;
        }
        let o = self.fresh();
        match op {
            PureOp::Xor => self.emit(LOp::Xor { a, b, c: o }),
            PureOp::Mul => self.emit(LOp::Mul { a, b, c: o }),
        }
        self.scope.pure_cells.insert(key, o);
        o
    }

    
    
    
    
    
    
    fn frame_cell(&mut self, arr: &Expr, idx: &Expr) -> Option<Off> {
        let (base, size) = self.stack_of(arr)?;
        let k = self.const_index(idx);
        if k >= size {
            self.fail(format!("index {k} out of bounds (StackBuf size {size})"))
        };
        Some(base + k)
    }

    
    fn one(&mut self) -> Off {
        self.const_cell(F192::ONE)
    }

    
    
    
    
    
    
    
    
    
    
    
    fn const_cell(&mut self, v: F192) -> Off {
        let key = [v.c0, v.c1, v.c2];
        if let Some(&o) = self.scope.const_cells.get(&key) {
            return o;
        }
        let o = self.fresh();
        self.set_const(o, v);
        self.scope.const_cells.insert(key, o);
        o
    }

    
    
    fn zero(&mut self) -> Off {
        self.const_cell(F192::ZERO)
    }

    
    
    
    
    fn halt(&mut self) {
        let one = self.one();
        let dest = self.fresh();
        self.set(dest, KVal::EndSentinel);
        self.emit(LOp::Jump {
            oc: one,
            od: dest,
            of: one,
        });
    }

    
    fn copy(&mut self, src: Off, dst: Off) {
        let one = self.one();
        self.emit(LOp::Mul { a: src, b: one, c: dst });
    }

    
    
    
    
    
    
    fn self_fp(&mut self) -> Off {
        if self.is_main {
            return self.one();
        }
        if let Some(o) = self.scope.self_fp_off {
            return o;
        }
        let q = self.fresh();
        self.pending.push(Hint::AllocBuffer { ptr: q, size: 1 });
        self.deref(q, 0, 0, DerefMode::Fp); 
        let o = self.fresh();
        self.deref(q, 0, o, DerefMode::Cell); 
        self.scope.self_fp_off = Some(o);
        o
    }

    
    
    fn patch_local(&mut self, set_idx: usize, target: usize) {
        match &mut self.code[set_idx].op {
            LOp::Set { k: KVal::Local(t), .. } => *t = target as u32,
            other => unreachable!("patch_local on {other:?}"),
        }
    }

    
    
    
    
    fn scoped(&mut self, f: impl FnOnce(&mut Self)) {
        let saved_scope = self.scope.clone();
        f(self);
        
        
        
        if !self.pending.is_empty() {
            self.anchor();
        }
        self.scope = saved_scope;
    }

    
    fn branch(&mut self, body: &[Stmt]) {
        self.scoped(|s| {
            for st in body {
                s.stmt(st);
            }
        });
    }

    
    
    
    
    fn ret_targets<'a>(&mut self, targets: &'a [Expr]) -> (Vec<Off>, Vec<(&'a str, Off)>) {
        let mut cells = Vec::with_capacity(targets.len());
        let mut binds = Vec::new();
        for t in targets {
            match t {
                
                
                
                
                
                Expr::Index(arr, idx) => match self.frame_cell(arr, idx) {
                    Some(c) => cells.push(c),
                    None => self.fail(format!(
                        "a multi-value target must be a name or a StackBuf element, got `{t:?}`"
                    )),
                },
                Expr::Var(n) => {
                    let c = self.fresh();
                    cells.push(c);
                    binds.push((n.as_str(), c));
                }
                other => self.fail(format!(
                    "a multi-value target must be a name or a StackBuf element, got `{other:?}`"
                )),
            }
        }
        (cells, binds)
    }

    
    
    
    
    
    fn lower_match(&mut self, targets: &[Expr], x: &Expr, arms: &[Expr]) {
        for arm in arms {
            if let Expr::Call(f, _) = arm
                && self
                    .defs
                    .get(f.as_str())
                    .is_some_and(|d| !d.inline && d.return_shapes.iter().any(|s| matches!(s, Shape::StackBuf(_))))
            {
                self.fail("a normal function's StackBuf return cannot cross a match join; bind it with `let`");
            }
        }
        
        
        
        
        
        if arms
            .iter()
            .all(|a| matches!(a, Expr::Call(f, _) if self.defs.get(f.as_str()).is_some_and(|d| !d.inline)))
        {
            let specialized: Vec<(String, Vec<&Expr>)> = arms
                .iter()
                .map(|a| {
                    let Expr::Call(f, cargs) = a else { unreachable!() };
                    self.specialize(f, cargs)
                })
                .collect();
            let rt0 = &specialized[0].1;
            if specialized.iter().all(|(_, rt)| rt == rt0) {
                let callees: Vec<String> = specialized.iter().map(|(c, _)| c.clone()).collect();
                self.lower_dispatched_call(targets, x, &callees, rt0);
                return;
            }
            
            
        }
        
        
        
        let (chain_next, chain_in) = (self.chain_next.take(), self.chain_in.take());
        let entered = chain_in.is_some();
        let before = self.code.len();
        let xo = if entered { 0 } else { self.expr(x) };
        let (rcells, binds) = self.ret_targets(targets);
        
        
        
        if !entered && self.all_inline(arms) {
            self.keccak_pad_run();
            self.const_cell(crate::lower::builtins::two_to_one_close());
        }
        assert!(
            !entered || self.code.len() == before,
            "a chained match emitted code above its arms"
        );
        (self.chain_next, self.chain_in) = (chain_next, chain_in);
        self.lower_match_dispatch(xo, arms.len(), |s, j| {
            s.scoped(|s| {
                if let [rcell] = rcells.as_slice() {
                    s.expr_into(&arms[j], *rcell);
                } else {
                    let Expr::Call(f, cargs) = &arms[j] else {
                        s.fail(format!(
                            "a multi-target match arm must be a function call, got `{:?}`",
                            arms[j]
                        ));
                    };
                    s.inline_stack_ret = None;
                    s.call_into(f, cargs, &rcells);
                    
                    
                    if let Some(binds) = s.inline_stack_ret.take() {
                        for (b, &rc) in binds.iter().zip(&rcells) {
                            match *b {
                                RetBind::Gaddr(ga) => {
                                    let c = s.materialize(ga);
                                    s.copy(c, rc);
                                }
                                RetBind::Stack(base, size) => {
                                    if size != 1 {
                                        s.fail("a multi-cell StackBuf return cannot cross a match join")
                                    }
                                    
                                    s.copy(base, rc);
                                }
                                RetBind::Scalar => {}
                            }
                        }
                    }
                }
            });
        });
        self.bind_targets(&binds);
    }

    
    
    
    fn free_cell(&self, e: &Expr, targets: &[Expr]) -> Option<Off> {
        let mut names = Vec::new();
        crate::ast::free_vars_expr(e, &mut names);
        if names
            .iter()
            .any(|n| targets.iter().any(|t| matches!(t, Expr::Var(v) if v == n)))
        {
            return None;
        }
        match e {
            Expr::Var(n) => match self.scope.bound(n)?.val {
                Binding::Scalar(o) => Some(o),
                _ => None,
            },
            Expr::Index(b, i) => {
                let (Expr::Var(n), Some(k)) = (&**b, self.try_const_index(i)) else {
                    return None;
                };
                let (base, len) = self.scope.stack(n)?;
                (k < len).then_some(base + k)
            }
            _ => None,
        }
    }

    
    
    fn all_inline(&self, arms: &[Expr]) -> bool {
        arms.iter()
            .all(|a| matches!(a, Expr::Call(f, _) if self.defs.get(f.as_str()).is_some_and(|d| d.inline)))
    }

    
    
    pub(super) fn table_jump(&mut self, xo: Off, first: usize, one: Off, of: Off) {
        let entry = self.fresh();
        self.emit(LOp::Slot {
            x: xo,
            first: first as u32,
            dst: entry,
        });
        self.emit(LOp::Jump { oc: one, od: entry, of });
    }

    
    
    
    
    
    
    fn lower_match_dispatch(&mut self, xo: Off, n: usize, mut body: impl FnMut(&mut Self, usize)) {
        let next = self.chain_next.take();
        let entered = self.chain_in.take();
        let before = self.code.len();
        
        let sfp = self.self_fp();
        let one = self.one();
        
        let (join, jset) = match &entered {
            Some(ci) => (ci.join, ci.jset),
            None => {
                let join = self.fresh();
                let jset = self.code.len();
                self.set(join, KVal::Local(0)); 
                (join, jset)
            }
        };
        let name = self.fn_name.to_string();
        let first = match &entered {
            
            Some(ci) => ci.first,
            None => {
                let first = self.tables.slots.len();
                self.tables.slots.extend((0..n).map(|_| KVal::At(name.clone(), 0)));
                self.table_jump(xo, first, one, sfp);
                first
            }
        };
        assert!(
            entered.is_none() || self.code.len() == before,
            "a chained match emitted code above its arms"
        );
        let next_first = next.as_ref().map(|nx| {
            let first = self.tables.slots.len();
            self.tables.slots.extend((0..nx.n).map(|_| KVal::At(name.clone(), 0)));
            first
        });
        
        
        let arms_base = self.next;
        let mut arms_end = arms_base;
        for j in 0..n {
            self.next = arms_base;
            self.tables.slots[first + j] = KVal::At(name.clone(), self.code.len() as u32);
            body(self, j);
            if let (Some(nx), Some(nf)) = (&next, next_first) {
                self.table_jump(nx.xo, nf, one, sfp);
            } else if j + 1 != n {
                self.emit(LOp::Jump {
                    oc: one,
                    od: join,
                    of: sfp,
                });
            }
            arms_end = arms_end.max(self.next);
            
            self.heap_sizes.retain(|&o, _| o < arms_base);
        }
        self.next = arms_end;
        match next_first {
            Some(first) => self.chain_in = Some(ChainIn { first, join, jset }),
            None => self.patch_local(jset, self.code.len()),
        }
    }

    
    fn lower_if(&mut self, eq: bool, lhs: &Expr, rhs: &Expr, then: &[Stmt], els: &[Stmt], force_const: bool) {
        
        
        
        
        
        
        
        let (a, b) = (self.eval(lhs), self.eval(rhs));
        if let (Some(ai), Some(bi)) = (a.int, b.int) {
            
            
            
            
            
            
            
            if !force_const {
                for (e, known) in [(lhs, a), (rhs, b)] {
                    if let Some((n, f)) = known.diverging_readings() {
                        self.fail(format!(
                            "`{e:?}` reads as the integer {n} where a condition folds, and as the field \
                             element {:#x}:{:#x} where a value is wanted, so this branch would be decided \
                             by one reading and its body run under the other. Write `if const(...)` to \
                             decide it with integer arithmetic, or spell the operand so the two agree.",
                            f.c1, f.c0
                        ))
                    }
                }
            }
            for st in if (ai == bi) == eq { then } else { els } {
                self.stmt(st);
            }
            return;
        }
        
        
        
        if force_const {
            if let (Some(fa), Some(fb)) = (a.field, b.field) {
                for st in if (fa == fb) == eq { then } else { els } {
                    self.stmt(st);
                }
                return;
            }
            self.fail("`if const(...)` asks for a compile-time decision, but this condition is not one: both sides must be compile-time constants")
        }
        
        let x = if self.try_lit(rhs) == Some(0) {
            self.expr(lhs)
        } else if self.try_lit(lhs) == Some(0) {
            self.expr(rhs)
        } else {
            let (la, lb) = (self.expr(lhs), self.expr(rhs));
            
            self.pure(PureOp::Xor, la, lb)
        };
        
        let sfp = self.self_fp();
        let one = self.one();
        let (a_block, b_block) = if eq { (then, els) } else { (els, then) };
        let bdest = self.fresh();
        let bset = self.code.len();
        self.set(bdest, KVal::Local(0)); 
        self.emit(LOp::Jump {
            oc: x,
            od: bdest,
            of: sfp,
        });
        self.branch(a_block);
        if b_block.is_empty() {
            self.patch_local(bset, self.code.len());
        } else {
            let edest = self.fresh();
            let eset = self.code.len();
            self.set(edest, KVal::Local(0)); 
            self.emit(LOp::Jump {
                oc: one,
                od: edest,
                of: sfp,
            });
            self.patch_local(bset, self.code.len());
            self.branch(b_block);
            self.patch_local(eset, self.code.len());
        }
    }

    
    
    
    
    
    fn lower_assert_ne(&mut self, a: &Expr, b: &Expr) {
        
        
        
        
        if let (Expr::Lit(x), Expr::Lit(y)) = (a, b) {
            if x == y {
                self.fail(format!("assert a != b: sides are the compile-time-equal literal {x}"))
            };
            return;
        }
        let (la, lb) = (self.expr(a), self.expr(b));
        
        let x = self.pure(PureOp::Xor, la, lb);
        let inv = self.fresh();
        self.pending.push(Hint::Resolved(RHint::Inverse { value: x, dst: inv }));
        let p = self.fresh();
        self.emit(LOp::Mul { a: x, b: inv, c: p });
        self.set_const(p, F192::ONE);
    }

    
    
    
    
    
    
    
    
    fn bound_cell(&mut self, k: u64) -> Off {
        self.const_cell(g_pow_u128((k - 1) as u128).into())
    }

    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    fn lower_assert_lt(&mut self, e: &Expr, bound: &LtBound) {
        let kcell = match bound {
            LtBound::Const(k) => {
                if *k < 1 {
                    self.fail("range-check bound GEN ** 0 names the empty set")
                };
                if *k > 1 << leanvm_core::cpu::MIN_LOG_MEM {
                    self.fail(format!(
                        "range-check bound GEN ** {k} exceeds 2^{} (the minimum memory size)",
                        leanvm_core::cpu::MIN_LOG_MEM
                    ))
                };
                self.bound_cell(*k)
            }
            LtBound::Runtime(b) => {
                
                
                
                
                if self.try_field_const(b).is_some() {
                    self.fail(format!(
                        "a compile-time range-check bound must be written as `log GEN ** k` or an \
                     integer, so that the 2^{} cap applies",
                        leanvm_core::cpu::MIN_LOG_MEM
                    ))
                };
                
                if let Some(
                    ga @ GAddr {
                        base: Some(_),
                        exp: 1..,
                        run: None,
                    },
                ) = self.gaddr_of(b)
                {
                    let kcell = self.materialize(GAddr { exp: ga.exp - 1, ..ga });
                    return self.range_check(e, kcell);
                }
                let bcell = self.expr(b);
                let inv = self.const_cell(F192::new(primitives::field::G.inv().0, 0, 0));
                
                
                self.pure(PureOp::Mul, bcell, inv)
            }
        };
        self.range_check(e, kcell);
    }

    
    fn range_check(&mut self, e: &Expr, kcell: Off) {
        let x = self.expr(e);
        let y = self.fresh(); 
        let t1 = self.fresh(); 
        let t2 = self.fresh();
        self.deref(x, 0, t1, DerefMode::Cell);
        self.emit(LOp::Mul { a: x, b: y, c: kcell });
        self.deref(y, 0, t2, DerefMode::Cell);
    }

    fn expr(&mut self, e: &Expr) -> Off {
        
        
        if let Some(v) = self.try_field_const(e) {
            return self.const_cell(v);
        }
        match e {
            Expr::Lit(_) | Expr::Gen | Expr::GPow(_) => unreachable!("a literal folds above"),
            
            
            Expr::GenPow(e) => {
                let k = self.gpow_exp(e);
                self.const_cell(g_pow_u128(k).into())
            }
            Expr::Pow(b, e) => self.pow_expr(b, e),
            Expr::Var(v) => match self.scope.bound(v).map(|b| b.val) {
                Some(Binding::Stack(..)) => {
                    self.fail(format!("StackBuf `{v}` used as a scalar; index it (`{v}[k]`) or pass it to keccak"));
                }
                Some(Binding::Gaddr(ga)) => self.materialize(ga),
                Some(Binding::Scalar(o)) => o,
                _ => {
                    
                    
                    
                    
                    
                    
                    
                    if self.fn_name.starts_with("__loop") {
                        self.fail(format!(
                            "unbound variable `{v}` in a `for` loop body. If `{v}` names a value from \
                             outside the loop that this body also assigns to, the loop cannot carry it: \
                             the helper threads its captures in, not out. Assign to a new name inside \
                             the body, or carry state through a `HeapBuf`."
                        ))
                    }
                    self.fail(format!("unbound variable `{v}`"))
                }
            },
            Expr::Add(a, b) => {
                if let Some(x) = self.add_identity(a, b) {
                    return self.expr(x);
                }
                let (la, lb) = (self.expr(a), self.expr(b));
                self.pure(PureOp::Xor, la, lb)
            }
            Expr::Mul(a, b) => {
                if let Some(x) = self.mul_identity(a, b) {
                    return self.expr(x);
                }
                
                
                if let Some(ga @ GAddr { base: Some(_), .. }) = self.gaddr_of(e) {
                    return self.materialize(ga);
                }
                let (la, lb) = (self.expr(a), self.expr(b));
                self.pure(PureOp::Mul, la, lb)
            }
            Expr::FieldDiv(a, b) => {
                
                
                
                
                
                let (la, lb) = (self.expr(a), self.expr(b));
                let q = self.fresh();
                self.emit(LOp::Mul { a: q, b: lb, c: la });
                q
            }
            
            Expr::Call(f, _) if f == "f192" => self.fail("f192 needs three literal u64 limbs"),
            
            
            Expr::Call(f, args) if f == "const" => {
                if args.len() != 1 {
                    self.fail(format!("const(...) takes one expression, got {}", args.len()))
                };
                self.fail(format!(
                    "const(...) asks for a compile-time integer, and `{:?}` is not one",
                    args[0]
                ))
            }
            Expr::Call(f, args) if f == "addr" => {
                let ga = self.stack_addr(args);
                self.materialize(ga)
            }
            Expr::Call(f, args) if f == "hint_log2_ceil" => {
                
                
                
                
                if args.len() != 3 {
                    self.fail(format!(
                        "hint_log2_ceil takes three arguments, `(bits, nbits, floor)`, got {}",
                        args.len()
                    ))
                }
                let nbits = self.const_index(&args[1]);
                if nbits > 128 {
                    self.fail(format!("hint_log2_ceil reads at most 128 bits, got {nbits}"))
                }
                let floor = self.const_index(&args[2]);
                let bits = self.bits_dest(&args[0], nbits, "hint_log2_ceil");
                let dst = self.fresh();
                self.pending.push(Hint::Resolved(RHint::Log2Ceil {
                    bits,
                    dst,
                    nbits,
                    floor,
                }));
                dst
            }
            Expr::Call(f, args) => {
                let d = self.call(f, args, 1)[0];
                self.take_inline_ret_cell(d)
            }
            Expr::HeapBuf(n) => {
                let arr = self.fresh();
                self.heap_sizes.insert(arr, u128::from(*n));
                
                self.pending.push(Hint::AllocBuffer { ptr: arr, size: *n });
                arr
            }
            Expr::HeapBufDyn(e) => {
                
                
                let size = self.expr(e);
                let arr = self.fresh();
                self.pending.push(Hint::AllocBufferDyn { ptr: arr, size });
                arr
            }
            Expr::StackBuf(_) => self.fail("StackBuf(n) must be bound to a name: `x = StackBuf(n)`"),
            
            Expr::Index(arr, idx) => {
                if let Some(c) = self.frame_cell(arr, idx) {
                    return c;
                }
                let (ptr, o2) = self.heap_addr(arr, idx);
                if let Some(&cell) = self.scope.load_cells.get(&(ptr, o2)) {
                    return cell;
                }
                let dst = self.fresh();
                self.deref(ptr, o2, dst, DerefMode::Cell);
                dst
            }
            Expr::Sub(..) | Expr::Div(..) | Expr::Mod(..) => {
                self.fail(format!(
                    "`-`, `//`, `%` are compile-time only (field subtraction is `+`); use them in an index, a bound, or a `Const` argument, got `{e:?}`"
                ))
            }
            Expr::Slice(..) => self.fail("a slice is not a scalar; it is only a keccak operand"),
            Expr::ListLit(..) => self.fail("a list literal must be bound to a name: `x = [a, b]`"),
            Expr::ListComp(..) => self.fail("a list comprehension is only a keccak_cells argument"),
        }
    }

    
    
    fn pow_expr(&mut self, b: &Expr, e: &Expr) -> Off {
        let k = self
            .try_const_index(e)
            .unwrap_or_else(|| self.fail(format!("`**` exponent must be a compile-time integer, got `{e:?}`")));
        
        if let Some(bc) = self.try_field_const(b) {
            return self.const_cell(field_pow(bc, k));
        }
        if k == 0 {
            let o = self.fresh();
            self.set_const(o, F192::ONE);
            return o;
        }
        
        let base = self.expr(b);
        let hi = 31 - k.leading_zeros(); 
        let mut acc = base;
        for bit in (0..hi).rev() {
            acc = self.pure(PureOp::Mul, acc, acc);
            if (k >> bit) & 1 == 1 {
                acc = self.pure(PureOp::Mul, acc, base);
            }
        }
        acc
    }

    
    
    fn expr_into(&mut self, e: &Expr, dst: Off) {
        
        
        if let Some(v) = self.try_field_const(e) {
            self.set_const(dst, v);
            return;
        }
        match e {
            
            
            
            
            Expr::Index(arr, idx) => match self.frame_cell(arr, idx) {
                Some(c) => self.copy(c, dst),
                None => {
                    let (ptr, o2) = self.heap_addr(arr, idx);
                    
                    
                    self.deref(ptr, o2, dst, DerefMode::Cell);
                }
            },
            Expr::Pow(b, e) => {
                let v = self.pow_expr(b, e);
                self.copy(v, dst);
            }
            Expr::Add(a, b) => {
                if let Some(x) = self.add_identity(a, b) {
                    self.expr_into(x, dst);
                } else {
                    
                    
                    let (la, lb) = (self.expr(a), self.expr(b));
                    self.emit(LOp::Xor { a: la, b: lb, c: dst });
                }
            }
            Expr::Mul(a, b) => {
                if let Some(x) = self.mul_identity(a, b) {
                    self.expr_into(x, dst);
                } else {
                    let (la, lb) = (self.expr(a), self.expr(b));
                    self.emit(LOp::Mul { a: la, b: lb, c: dst });
                }
            }
            
            
            Expr::Call(f, args) if self.defs.contains_key(f.as_str()) => {
                self.inline_stack_ret = None;
                self.call_into(f, args, &[dst]);
                let v = self.take_inline_ret_cell(dst);
                if v != dst {
                    self.copy(v, dst);
                }
            }
            _ => {
                let v = self.expr(e);
                self.copy(v, dst);
            }
        }
    }

    fn stmt(&mut self, s: &Stmt) {
        let tail = std::mem::take(&mut self.tail_call);
        
        
        self.cur_line = s.line;
        match &s.kind {
            StmtKind::Let(name, e) => match e {
                
                Expr::StackBuf(n) => {
                    let base = self.alloc_stack(*n);
                    self.rebind(name, Binding::Stack(base, *n));
                }
                
                
                
                
                Expr::ListLit(es) => {
                    let base = self.alloc_stack(es.len() as u32);
                    for (k, el) in es.iter().enumerate() {
                        self.expr_into(el, base + k as u32);
                    }
                    self.rebind(name, Binding::Stack(base, es.len() as u32));
                }
                
                
                
                Expr::Call(f, cargs) if f == "addr" => {
                    let ga = self.stack_addr(cargs);
                    self.rebind(name, Binding::Gaddr(ga));
                }
                
                
                
                Expr::Var(v) if self.scope.stack(v).is_some() => {
                    let (base, size) = self.scope.stack(v).expect("guarded above");
                    self.rebind(name, Binding::Stack(base, size));
                }
                _ => {
                    
                    
                    
                    
                    
                    
                    
                    let known = self.eval(e);
                    
                    
                    
                    if let Some(ga) = known.addr {
                        self.rebind(name, Binding::Gaddr(ga));
                    } else if let Some(c) = known.field {
                        self.rebind(name, Binding::FConst(c));
                    } else if let Some(k) = known.int {
                        
                        
                        
                        self.rebind(name, Binding::FConst(lit_field(k)));
                    } else if let Expr::Call(cf, cargs) = e
                        && self.defs.contains_key(cf.as_str())
                    {
                        
                        
                        
                        
                        
                        
                        
                        let o = self.call(cf, cargs, 1)[0];
                        let b = ret_binding(self.inline_stack_ret.take().and_then(|b| b.into_iter().next()), o);
                        self.rebind(name, b);
                    } else {
                        let o = self.expr(e);
                        self.rebind(name, Binding::Scalar(o));
                    }
                    
                    
                    
                    
                    if let Some(k) = known.int {
                        self.scope.set_int(name, k);
                    }
                }
            },
            StmtKind::LetTuple(names, f, args) => {
                let dsts = self.call(f, args, names.len());
                
                
                
                let binds = self.inline_stack_ret.take();
                for (i, (n, d)) in names.iter().zip(&dsts).enumerate() {
                    let b = ret_binding(binds.as_ref().and_then(|b| b.get(i).copied()), *d);
                    self.rebind(n, b);
                }
            }
            
            
            
            
            StmtKind::AssertEq(a, b) => {
                let (la, lb) = (self.expr(a), self.expr(b));
                let one = self.one();
                self.emit(LOp::Mul { a: la, b: one, c: lb });
            }
            StmtKind::AssertNe(a, b) => self.lower_assert_ne(a, b),
            StmtKind::AssertLt(e, bound) => self.lower_assert_lt(e, bound),
            StmtKind::HintWitness { dest, name } => self.lower_hint_witness(dest, name),
            
            
            
            StmtKind::LetHintWitness { name, stream } => {
                let dst = self.fresh();
                self.pending.push(Hint::Resolved(RHint::WitnessStack {
                    name: stream.clone(),
                    base: dst,
                    len: 1,
                }));
                self.rebind(name, Binding::Scalar(dst));
            }
            StmtKind::Print { label, value } => {
                
                
                
                let cell = self.expr(value);
                self.pending.push(Hint::Resolved(RHint::Print {
                    label: label.clone(),
                    cell,
                }));
                self.anchor();
            }
            StmtKind::If {
                eq,
                lhs,
                rhs,
                then,
                els,
                force_const,
            } => self.lower_if(*eq, lhs, rhs, then, els, *force_const),
            StmtKind::Match { targets, x, arms } => self.lower_match(targets, x, arms),
            StmtKind::Call(f, args) => {
                if !self.lower_builtin(f, args) {
                    self.call(f, args, 0);
                }
            }
            StmtKind::Store(arr, idx, val) => {
                
                
                
                
                
                if let Some(c) = self.frame_cell(arr, idx) {
                    self.expr_into(val, c);
                } else {
                    let v = self.expr(val);
                    let (ptr, o2) = self.heap_addr(arr, idx);
                    self.deref(ptr, o2, v, DerefMode::Cell);
                }
            }
            StmtKind::Return(es) => self.lower_return(es),
            StmtKind::CallIfNe(lhs, rhs, callee, args) => {
                
                
                
                
                
                
                let (la, lb) = (self.expr(lhs), self.expr(rhs));
                
                let x = self.pure(PureOp::Xor, la, lb);
                self.lower_call(callee, args, Some(x), &[], tail);
            }
            StmtKind::For { var, lo, hi, body } => self.lower_for(var, *lo, hi, body),
            
            
            
            
            StmtKind::Unroll { var, lo, hi, body } => {
                let bound = |s: &Self, e: &Expr| {
                    s.try_const_index(e).unwrap_or_else(|| {
                        self.fail(format!("unroll bounds must be compile-time integers, got `{e:?}`"))
                    })
                };
                let (lo, hi) = (bound(self, lo), bound(self, hi));
                if lo > hi {
                    self.fail(format!("unroll(a, b) needs a <= b, got ({lo}, {hi})"))
                };
                let stmts: Vec<Stmt> = (lo..hi)
                    .flat_map(|j| subst_stmts(body, var, &Expr::Lit(j as u128)))
                    .collect();
                for (i, s) in stmts.iter().enumerate() {
                    
                    if let (StmtKind::Match { targets, arms, .. }, Some(next)) = (&s.kind, stmts.get(i + 1))
                        && let StmtKind::Match { x: nx, arms: narms, .. } = &next.kind
                        && self.all_inline(arms)
                        && self.all_inline(narms)
                        && let Some(xo) = self.free_cell(nx, targets)
                    {
                        self.chain_next = Some(ChainNext { xo, n: narms.len() });
                    }
                    self.stmt(s);
                }
            }
        }
    }

    
    
    
    
    
    
    
    
    
    
    
    
    
    
    fn lower_for(&mut self, var: &str, lo: u64, hi: &ForBound, body: &[Stmt]) {
        let id = *self.loop_ctr;
        *self.loop_ctr += 1;
        let loop_name = format!("__loop{id}");
        let mut shadowed = std::collections::HashSet::new();
        binds_anywhere(body, &mut shadowed);
        
        if !contains_return(body) && !shadowed.contains(var) {
            self.loop_bounds.insert(
                loop_name.clone(),
                (
                    lo,
                    match hi {
                        ForBound::Const(end) => Some(*end),
                        ForBound::Runtime(_) => None,
                    },
                ),
            );
        }
        if std::env::var("DBG_LOOPS").is_ok() {
            let bound = match hi {
                ForBound::Const(h) => format!("g^{lo}..g^{h}"),
                ForBound::Runtime(e) => format!("g^{lo}..{e:?}"),
            };
            eprintln!("DBG_LOOPS {loop_name} in {} for {var} in {bound}", self.fn_name);
        }
        
        
        
        let bound_var = format!("__bound{id}");
        let (exit, entry_bound): (Expr, Expr) = match hi {
            ForBound::Const(hi) => (Expr::GPow(*hi as u128), Expr::GPow(*hi as u128)),
            ForBound::Runtime(e) => (Expr::Var(bound_var.clone()), e.clone()),
        };

        
        
        let mut referenced = Vec::new();
        let mut bound = std::collections::HashSet::new();
        bound.insert(var);
        for s in body {
            free_vars_stmt(s, &mut referenced, &mut bound);
        }
        
        
        
        
        
        let mut captures = Vec::new();
        let mut seen = std::collections::HashSet::new();
        for r in &referenced {
            if bound.contains(r) {
                continue;
            }
            
            
            if let Some((_, len)) = self.scope.stack(r)
                && !shadowed.contains(r)
            {
                if seen.insert(*r) {
                    captures.push(((*r).to_string(), Shape::StackBuf(len)));
                }
                continue;
            }
            
            
            
            
            
            
            if matches!(
                self.scope.bound(r).map(|b| b.val),
                Some(Binding::Scalar(_) | Binding::Gaddr(_) | Binding::FConst(_))
            ) && seen.insert(*r)
            {
                captures.push(((*r).to_string(), Shape::Scalar));
            }
        }

        
        
        
        let runtime = matches!(hi, ForBound::Runtime(_));
        let mut params = vec![(var.to_string(), Shape::Scalar)];
        if runtime {
            params.push((bound_var.clone(), Shape::Scalar));
        }
        params.extend(captures.iter().cloned());
        let cap_args = |first: Expr, bound: Expr| {
            let mut a = vec![first];
            if runtime {
                a.push(bound);
            }
            a.extend(captures.iter().map(|(c, _)| Expr::Var(c.clone())));
            a
        };

        
        
        
        
        
        let next_var = format!("__next{id}");
        let next = Expr::Mul(Box::new(Expr::Var(var.to_string())), Box::new(Expr::Gen));
        let mut loop_body: Vec<Stmt> = body.to_vec();
        
        let at = |kind| Stmt::new(self.cur_line, kind);
        loop_body.push(at(StmtKind::Let(next_var.clone(), next)));
        loop_body.push(at(StmtKind::CallIfNe(
            Expr::Var(next_var.clone()),
            exit,
            loop_name.clone(),
            cap_args(Expr::Var(next_var), Expr::Var(bound_var.clone())),
        )));
        loop_body.push(at(StmtKind::Return(vec![])));
        self.queue.push(Func {
            name: loop_name.clone(),
            params: params
                .into_iter()
                .map(|(name, shape)| Param {
                    name,
                    kind: ParamKind::Runtime(shape),
                })
                .collect(),
            return_shapes: vec![],
            body: loop_body,
            inline: false,
        });

        
        
        
        match hi {
            ForBound::Const(hi) => {
                if lo != *hi {
                    self.call(
                        &loop_name,
                        &cap_args(Expr::GPow(lo as u128), Expr::GPow(*hi as u128)),
                        0,
                    );
                }
            }
            ForBound::Runtime(_) => {
                
                
                let entry_bound = if calls_or_allocates(&entry_bound) {
                    let name = format!("__entry{id}");
                    self.stmt(&Stmt::new(self.cur_line, StmtKind::Let(name.clone(), entry_bound)));
                    Expr::Var(name)
                } else {
                    entry_bound
                };
                let stmt = Stmt::new(
                    self.cur_line,
                    StmtKind::CallIfNe(
                        Expr::GPow(lo as u128),
                        entry_bound.clone(),
                        loop_name,
                        cap_args(Expr::GPow(lo as u128), entry_bound),
                    ),
                );
                self.stmt(&stmt);
            }
        }
    }
}

fn contains_return(body: &[Stmt]) -> bool {
    body.iter().any(|stmt| match &stmt.kind {
        StmtKind::Return(_) => true,
        StmtKind::If { then, els, .. } => contains_return(then) || contains_return(els),
        StmtKind::For { body, .. } | StmtKind::Unroll { body, .. } => contains_return(body),
        _ => false,
    })
}



fn calls_or_allocates(e: &Expr) -> bool {
    match e {
        Expr::Call(..)
        | Expr::HeapBuf(_)
        | Expr::HeapBufDyn(_)
        | Expr::StackBuf(_)
        | Expr::ListLit(_)
        | Expr::ListComp(..) => true,
        Expr::Add(a, b)
        | Expr::Mul(a, b)
        | Expr::Sub(a, b)
        | Expr::Div(a, b)
        | Expr::FieldDiv(a, b)
        | Expr::Mod(a, b)
        | Expr::Index(a, b)
        | Expr::Pow(a, b) => calls_or_allocates(a) || calls_or_allocates(b),
        Expr::Slice(a, lo, hi) => calls_or_allocates(a) || calls_or_allocates(lo) || calls_or_allocates(hi),
        Expr::GenPow(x) => calls_or_allocates(x),
        Expr::Lit(_) | Expr::Gen | Expr::GPow(_) | Expr::Var(_) => false,
    }
}




fn plus_k(lo: &Expr, hi: &Expr) -> Option<u128> {
    match hi {
        Expr::Add(a, b) => match (a.as_ref(), b.as_ref()) {
            (Expr::Lit(k), other) | (other, Expr::Lit(k)) if other == lo => Some(*k),
            _ => None,
        },
        _ => None,
    }
}


pub(crate) fn lower_func(
    f: &Func,
    queue: &mut Vec<Func>,
    loop_ctr: &mut usize,
    defs: &HashMap<&str, &Func>,
    const_arrays: &HashMap<&str, &[F192]>,
    loop_bounds: &mut HashMap<String, (u64, Option<u64>)>,
    tables: &mut JumpTables,
) -> Lowered {
    let mut names: HashMap<String, Bound> = HashMap::new();
    for (i, p) in f.params.iter().enumerate() {
        assert!(
            !const_arrays.contains_key(p.name.as_str()),
            "`{}`: parameter `{}` collides with a top-level constant array, whose name is \
             reserved (zkDSL.md §Global constants)",
            f.name,
            p.name
        );
        
        
        let off = Abi::arg(f.param_shapes(), i);
        let val = match p.shape() {
            Shape::StackBuf(n) => Binding::Stack(off, n),
            Shape::Scalar => Binding::Scalar(off),
        };
        names.insert(p.name.clone(), Bound { val, int: None });
    }
    
    
    let n_ret_cells: u32 = f.return_shapes.iter().map(|s| s.cells()).sum();
    let arg_cells = Abi::arg_cells(f.param_shapes());
    let abi_end = Abi::end(arg_cells, n_ret_cells);
    
    
    let loop_frame = loop_bounds.contains_key(&f.name);
    let mut lowerer = FnLower {
        scope: Scope {
            self_fp_off: loop_frame.then_some(abi_end),
            names,
            ..Default::default()
        },
        next: abi_end + u32::from(loop_frame),
        arg_cells,
        return_shapes: &f.return_shapes,
        is_main: f.name == "main",
        fn_name: &f.name,
        tail_call: false,
        code: Vec::new(),
        cur_line: 0,
        heap_sizes: HashMap::new(),
        inline_ret: None,
        inline_stack_ret: None,

        pending: Vec::new(),
        chain_next: None,
        chain_in: None,
        inline_calls: Vec::new(),
        loop_bounds,
        queue,
        loop_ctr,
        defs,
        const_arrays,
        tables,
    };
    for (i, s) in f.body.iter().enumerate() {
        
        
        
        
        lowerer.tail_call = !lowerer.is_main
            && f.return_shapes.is_empty()
            && matches!(s.kind, StmtKind::CallIfNe(..))
            && matches!(f.body.get(i + 1).map(|n| &n.kind), Some(StmtKind::Return(r)) if r.is_empty());
        lowerer.stmt(s);
    }
    if lowerer.is_main {
        lowerer.halt(); 
    } else if !matches!(f.body.last().map(|s| &s.kind), Some(StmtKind::Return(_))) {
        
        
        let last = f.body.last().map_or(0, |s| s.line);
        lowerer.stmt(&Stmt::new(last, StmtKind::Return(vec![])));
    }
    Lowered {
        name: f.name.clone(),
        code: lowerer.code,
        frame_size: lowerer.next,
    }
}
