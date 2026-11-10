














use super::*;
use std::borrow::Cow;




pub(super) fn ret_binding(b: Option<RetBind>, dst: Off) -> Binding {
    match b {
        Some(RetBind::Stack(base, size)) => Binding::Stack(base, size),
        Some(RetBind::Gaddr(ga)) => Binding::Gaddr(ga),
        _ => Binding::Scalar(dst),
    }
}

fn substitute_body<'a>(body: &'a [Stmt], substs: &[(&str, Expr)]) -> Cow<'a, [Stmt]> {
    if substs.is_empty() {
        return Cow::Borrowed(body);
    }
    let subs: Vec<(&str, &Expr)> = substs.iter().map(|(name, value)| (*name, value)).collect();
    Cow::Owned(crate::parser::subst_all(body, &subs))
}


fn body_inlinable(body: &[Stmt]) -> bool {
    matches!(body.split_last(), Some((last, rest)) if matches!(last.kind, StmtKind::Return(_))
        && rest.iter().all(stmt_inline_safe))
}

fn stmt_inline_safe(s: &Stmt) -> bool {
    match &s.kind {
        StmtKind::Let(..)
        | StmtKind::Store(..)
        | StmtKind::HintWitness { .. }
        | StmtKind::LetHintWitness { .. }
        | StmtKind::Print { .. }
        | StmtKind::AssertEq(..)
        | StmtKind::AssertNe(..)
        | StmtKind::AssertLt(..)
        
        
        | StmtKind::Call(..)
        | StmtKind::LetTuple(..)
        | StmtKind::Match { .. } => true,
        StmtKind::If { then, els, .. } => then.iter().all(stmt_inline_safe) && els.iter().all(stmt_inline_safe),
        StmtKind::Unroll { body, .. } => body.iter().all(stmt_inline_safe),
        _ => false,
    }
}

impl FnLower<'_> {
    
    
    pub(super) fn lower_call(&mut self, callee: &str, args: &[Expr], cond: Option<Off>, dsts: &[Off], tail: bool) {
        
        
        
        
        
        
        match self.callee_def(callee).map(|f| f.params.len()) {
            Some(want) if want != args.len() => {
                let plural = if want == 1 { "argument" } else { "arguments" };
                self.fail(format!("`{callee}` takes {want} {plural}, got {}", args.len()))
            }
            
            
            
            
            
            None => self.fail(format!(
                "no function named `{callee}`. A builtin that writes into a destination \
                 (`keccak`, `assert_in_k`, a `hint_*`) is a statement and returns nothing, so it \
                 cannot be called for a value"
            )),
            _ => {}
        }
        let (callee, args) = self.specialize(callee, args);
        let (callee, args) = (callee.as_str(), args.as_slice());
        
        
        
        let shapes = self
            .callee_def(callee)
            .map(|f| f.param_shapes().collect::<Vec<_>>())
            .unwrap_or_else(|| vec![Shape::Scalar; args.len()]);
        let mut arg_offs: Vec<(Off, Off)> = Vec::new();
        for (i, a) in args.iter().enumerate() {
            let base = Abi::arg(shapes.iter().copied(), i);
            match shapes.get(i).copied().unwrap_or(Shape::Scalar) {
                Shape::StackBuf(n) => {
                    let (src, len) = self.stack_of(a).unwrap_or_else(|| {
                        self.fail(format!(
                            "`{callee}` parameter {i} is a StackBuf({n}); pass one, got `{a:?}`"
                        ))
                    });
                    if len != n {
                        self.fail(format!(
                            "`{callee}` parameter {i} is a StackBuf({n}), got a StackBuf({len})"
                        ))
                    }
                    arg_offs.extend((0..n).map(|k| (base + k, src + k)));
                }
                Shape::Scalar => {
                    let cell = self.expr(a);
                    arg_offs.push((base, cell));
                }
            }
        }
        let callee_arg_cells = Abi::arg_cells(shapes.iter().copied());
        if tail && callee == self.fn_name && self.loop_bounds.contains_key(callee) {
            let own_fp = self.self_fp();
            let scale = self.fresh();
            self.set(scale, KVal::FrameSize);
            self.pending.push(Hint::NextFrameAddress);
            let nfp = self.pure(PureOp::Mul, own_fp, scale);
            let entry = self.fresh();
            let oc = cond.unwrap_or_else(|| self.one());
            let one = self.one();
            self.set(entry, KVal::Entry(callee.to_string()));
            for &(off, ao) in &arg_offs {
                self.emit(LOp::MulNextFrame { a: ao, b: one, c: off });
            }
            self.emit(LOp::MulNextFrame {
                a: nfp,
                b: one,
                c: Abi::end(callee_arg_cells, 0),
            });
            self.emit(LOp::MulNextFrame {
                a: 1,
                b: one,
                c: Abi::RET_FP,
            });
            self.emit(LOp::MulNextFrame {
                a: 0,
                b: one,
                c: Abi::RET_PC,
            });
            self.emit(LOp::Jump { oc, od: entry, of: nfp });
            return;
        }
        let nfp = self.fresh();
        let entry = self.fresh();
        
        
        
        let oc = cond.unwrap_or_else(|| self.one());
        self.set(entry, KVal::Entry(callee.to_string()));

        
        if let Some(&(start, end)) = self.loop_bounds.get(callee) {
            let count = match end {
                Some(end) => LoopCount::Constant(end - start + 1),
                None => LoopCount::Bound {
                    cell: arg_offs[1].1,
                    start,
                },
            };
            self.pending.push(Hint::AllocLoopFrames {
                ptr: nfp,
                callee: callee.to_string(),
                count,
                tail: Abi::end(callee_arg_cells, 0) + 1,
            });
        } else {
            self.pending.push(Hint::AllocFrame {
                ptr: nfp,
                callee: callee.to_string(),
            });
        }
        for &(off, ao) in &arg_offs {
            self.deref(nfp, off, ao, DerefMode::Cell);
        }
        if self.loop_bounds.contains_key(callee) {
            self.deref(nfp, Abi::end(callee_arg_cells, 0), nfp, DerefMode::Cell);
        }
        if tail {
            
            
            
            self.deref(nfp, 1, 1, DerefMode::Cell); 
            self.deref(nfp, 0, 0, DerefMode::Cell); 
        } else {
            self.deref(nfp, 1, 0, DerefMode::Fp); 
            self.deref(nfp, 0, 0, DerefMode::Pc); 
        }
        self.emit(LOp::Jump { oc, od: entry, of: nfp });

        for (i, &d) in dsts.iter().enumerate() {
            self.deref(nfp, Abi::ret(callee_arg_cells, i as u32), d, DerefMode::Cell);
        }
    }

    
    
    
    
    
    
    pub(super) fn lower_dispatched_call(&mut self, targets: &[Expr], x: &Expr, callees: &[String], rt_args: &[&Expr]) {
        
        
        
        
        if let Some(shared) = callees.iter().find_map(|c| self.callee_def(c)) {
            for c in callees {
                if let Some(def) = self.callee_def(c)
                    && !def.param_shapes().eq(shared.param_shapes())
                {
                    self.fail(format!(
                        "`{c}` does not take the same parameter shapes as the other arms of this dispatch"
                    ))
                }
            }
            
            if let Some(i) = shared.param_shapes().position(|s| s != Shape::Scalar) {
                self.fail(format!(
                    "a `match` arm cannot pass a `StackBuf` parameter (parameter {i} of `{}`): the \
                     fused dispatch writes one cell per argument. Give the arms `Const` arguments so each \
                     specializes into its own call instead of fusing",
                    callees.first().map(String::as_str).unwrap_or("?")
                ))
            }
        }
        let n_args = rt_args.len() as u32;
        
        
        
        
        
        
        
        for callee in callees {
            
            
            
            let Some(def) = self.callee_def(callee) else {
                continue;
            };
            let want = def.params.len();
            if want != rt_args.len() {
                let plural = if want == 1 { "argument" } else { "arguments" };
                self.fail(format!(
                    "`{callee}` takes {want} {plural}, dispatched call passes {}",
                    rt_args.len()
                ))
            }
            let shapes = &def.return_shapes;
            if shapes.len() != targets.len() {
                self.fail(format!(
                    "`{callee}` returns {} values, dispatched call binds {}",
                    shapes.len(),
                    targets.len()
                ))
            };
            if shapes.iter().any(|s| *s != Shape::Scalar) {
                self.fail(format!(
                    "`{callee}`: a multi-cell StackBuf return cannot cross a dispatched join"
                ))
            };
        }
        let (rcells, binds) = self.ret_targets(targets);

        
        
        let arg_offs: Vec<Off> = rt_args.iter().map(|a| self.expr(a)).collect();
        let xo = self.expr(x);
        let one = self.one();

        let nfp = self.fresh();
        self.pending.push(Hint::AllocFrameMax {
            ptr: nfp,
            callees: callees.to_vec(),
        });
        for (i, &ao) in arg_offs.iter().enumerate() {
            self.deref(
                nfp,
                Abi::arg(std::iter::repeat_n(Shape::Scalar, rt_args.len()), i),
                ao,
                DerefMode::Cell,
            );
        }
        self.deref(nfp, Abi::RET_FP, 0, DerefMode::Fp);
        let join_cell = self.fresh();
        let join_set = self.code.len();
        self.set(join_cell, KVal::Local(0)); 
        self.deref(nfp, Abi::RET_PC, join_cell, DerefMode::Cell); 

        
        
        let tables = &mut *self.tables;
        let first = *tables.shared.entry(callees.to_vec()).or_insert_with(|| {
            tables.slots.extend(callees.iter().map(|c| KVal::Entry(c.clone())));
            tables.slots.len() - callees.len()
        });
        self.table_jump(xo, first, one, nfp);

        
        self.patch_local(join_set, self.code.len());
        for (i, &r) in rcells.iter().enumerate() {
            self.deref(nfp, Abi::ret(n_args, i as u32), r, DerefMode::Cell);
        }

        self.bind_targets(&binds);
    }

    
    
    
    
    
    pub(super) fn try_inline(&mut self, callee: &str, args: &[Expr], dsts: &[Off]) -> bool {
        let Some(def) = self.defs.get(callee).copied().filter(|d| d.inline) else {
            return false;
        };
        let substs = self
            .const_substs(def, args)
            .unwrap_or_else(|e| self.fail(format!("`@inline {callee}`: {e}")));
        let body = substitute_body(&def.body, &substs);
        let n_ret = def.return_shapes.len();
        if n_ret != dsts.len() {
            self.fail(format!(
                "`@inline {callee}` returns {n_ret} values, call binds {}",
                dsts.len()
            ))
        };
        if !body_inlinable(&body) {
            self.fail(format!(
                "`@inline {callee}` requires one tail `return`, with no nested returns or mul_range loops"
            ))
        };
        if self.inline_calls.iter().any(|f| f == callee) {
            self.fail(format!(
                "recursive @inline expansion is not supported: {} -> {callee}",
                self.inline_calls.join(" -> ")
            ))
        };
        
        
        
        
        
        
        let mut binds: Vec<(String, Binding)> = Vec::new();
        for (i, (p, a)) in def.params.iter().zip(args).enumerate() {
            if p.kind == ParamKind::Const {
                continue;
            }
            
            if let Shape::StackBuf(n) = p.shape() {
                match self.stack_of(a) {
                    Some((_, len)) if len == n => {}
                    Some((_, len)) => self.fail(format!(
                        "`{callee}` parameter {i} is a StackBuf({n}), got a StackBuf({len})"
                    )),
                    None => self.fail(format!(
                        "`{callee}` parameter {i} is a StackBuf({n}); pass one, got `{a:?}`"
                    )),
                }
            }
            let b = if let Some((base, size)) = self.stack_of(a) {
                Binding::Stack(base, size)
            } else if let Some(ga) = self.gaddr_of(a) {
                Binding::Gaddr(ga)
            } else {
                Binding::Scalar(self.expr(a))
            };
            binds.push((p.name.clone(), b));
        }
        
        
        
        let saved = std::mem::take(&mut self.scope.names);
        for (p, b) in binds {
            self.check_not_reserved(&p);
            self.scope.names.insert(p, Bound { val: b, int: None });
        }
        let saved_ret = self.inline_ret.replace(dsts.to_vec());
        
        
        
        
        let saved_line = self.cur_line;
        self.inline_calls.push(callee.to_string());
        for s in body.iter() {
            self.stmt(s);
        }
        let popped = self.inline_calls.pop();
        debug_assert_eq!(popped.as_deref(), Some(callee));
        self.inline_ret = saved_ret;
        self.cur_line = saved_line;
        self.scope.names = saved;
        true
    }

    pub(super) fn lower_return(&mut self, exprs: &[Expr]) {
        
        
        if let Some(dsts) = self.inline_ret.take() {
            
            
            
            
            
            
            
            
            let mut binds = Vec::with_capacity(dsts.len());
            for (e, &d) in exprs.iter().zip(&dsts) {
                binds.push(if let Some((base, size)) = self.stack_of(e) {
                    RetBind::Stack(base, size)
                } else if let Some(ga) = self.gaddr_of(e) {
                    RetBind::Gaddr(ga)
                } else {
                    self.expr_into(e, d);
                    RetBind::Scalar
                });
            }
            self.inline_stack_ret = Some(binds);
            return;
        }
        if self.is_main {
            return; 
        }
        let ret_base = Abi::ret(self.arg_cells, 0);
        if exprs.len() != self.return_shapes.len() {
            self.fail(format!(
                "function returns {} values here, but its ABI declares {}",
                exprs.len(),
                self.return_shapes.len()
            ))
        };
        
        
        
        let mut ret = ret_base;
        for (e, &shape) in exprs.iter().zip(self.return_shapes) {
            match shape {
                Shape::Scalar => self.expr_into(e, ret),
                Shape::StackBuf(size) => {
                    let (base, actual) = self
                        .stack_of(e)
                        .unwrap_or_else(|| self.fail(format!("expected a StackBuf({size}) return, got `{e:?}`")));
                    if actual != size {
                        self.fail(format!("returned StackBuf has size {actual}, expected {size}"))
                    };
                    for k in 0..size {
                        self.copy(base + k, ret + k);
                    }
                }
            }
            ret += shape.cells();
        }
        let one = self.one();
        self.emit(LOp::Jump { oc: one, od: 0, of: 1 });
    }

    
    
    
    
    pub(super) fn specialize<'a>(&mut self, callee: &str, args: &'a [Expr]) -> (String, Vec<&'a Expr>) {
        
        
        if callee == "main" {
            self.fail("`main` is the entry point, so it cannot be called")
        }
        let Some(def) = self.defs.get(callee).copied() else {
            return (callee.to_string(), args.iter().collect()); 
        };
        if !def.has_const_params() {
            return (callee.to_string(), args.iter().collect());
        }
        let substs = self.const_substs(def, args).unwrap_or_else(|e| self.fail(e));
        let mut name = format!("{callee}_");
        for (_, c) in &substs {
            match c {
                Expr::Lit(n) => write!(name, "_L{n}"),
                Expr::GPow(k) => write!(name, "_G{k}"),
                _ => unreachable!(),
            }
            .unwrap();
        }
        let runtime = def.params.iter().zip(args).filter(|(p, _)| p.kind != ParamKind::Const);
        if !self.queue.iter().any(|f| f.name == name) {
            if self.queue.len() >= 10_000 {
                self.fail("Const specialization explosion (recursive constants?)")
            };
            self.queue.push(Func {
                name: name.clone(),
                params: runtime.clone().map(|(p, _)| p.clone()).collect(),
                return_shapes: def.return_shapes.clone(),
                body: substitute_body(&def.body, &substs).into_owned(),
                inline: false,
            });
        }
        (name, runtime.map(|(_, a)| a).collect())
    }

    
    
    
    
    pub(super) fn call(&mut self, callee: &str, args: &[Expr], n_ret: usize) -> Vec<Off> {
        if callee == "keccak" || callee == "keccak_cells" {
            self.fail(format!(
                "{callee} is a statement: it writes the state or the digest into its `out` run"
            ))
        };
        self.inline_stack_ret = None;
        if self.defs.get(callee).is_some_and(|d| d.inline) {
            let dsts: Vec<Off> = (0..n_ret).map(|_| self.fresh()).collect();
            self.call_into(callee, args, &dsts);
            return dsts;
        }

        let def = self.defs.get(callee).copied();
        if let Some(def) = def
            && def.return_shapes.len() != n_ret
        {
            self.fail(format!(
                "`{callee}` returns {} values, call binds {n_ret}",
                def.return_shapes.len()
            ))
        };
        let mut logical = Vec::with_capacity(n_ret);
        let mut physical = Vec::new();
        let mut binds = Vec::with_capacity(n_ret);
        for i in 0..n_ret {
            match def.map_or(Shape::Scalar, |d| d.return_shapes[i]) {
                Shape::Scalar => {
                    let dst = self.fresh();
                    logical.push(dst);
                    physical.push(dst);
                    binds.push(RetBind::Scalar);
                }
                Shape::StackBuf(size) => {
                    if size == 0 {
                        self.fail("a returned StackBuf must not be empty")
                    };
                    let base = self.alloc_stack(size);
                    logical.push(base);
                    physical.extend(base..base + size);
                    binds.push(RetBind::Stack(base, size));
                }
            }
        }
        self.lower_call(callee, args, None, &physical, false);
        self.inline_stack_ret = Some(binds);
        logical
    }

    
    
    pub(super) fn call_into(&mut self, callee: &str, args: &[Expr], dsts: &[Off]) {
        if callee == "keccak" || callee == "keccak_cells" {
            self.fail(format!("{callee} is a statement, not a value-returning call"))
        };
        if !self.try_inline(callee, args, dsts) {
            if let Some(def) = self.defs.get(callee) {
                if def.return_shapes.len() != dsts.len() {
                    self.fail(format!(
                        "`{callee}` returns {} values, call binds {}",
                        def.return_shapes.len(),
                        dsts.len()
                    ))
                };
                if def.return_shapes.iter().any(|s| *s != Shape::Scalar) {
                    self.fail("a normal function's multi-cell StackBuf return needs a `let` binding")
                };
            }
            self.lower_call(callee, args, None, dsts, false);
        }
    }

    fn const_substs<'a>(&self, def: &'a Func, args: &[Expr]) -> Result<Vec<(&'a str, Expr)>, String> {
        if args.len() != def.params.len() {
            return Err(format!("call to `{}`: wrong arity", def.name));
        }
        let mut substs = Vec::new();
        for (p, a) in def.params.iter().zip(args) {
            if p.kind == ParamKind::Const {
                let c = self.const_arg(a).ok_or_else(|| {
                    format!(
                        "argument for Const parameter `{}` of `{}` must be a compile-time \
                         constant, got `{a:?}`",
                        p.name, def.name
                    )
                })?;
                substs.push((p.name.as_str(), c));
            }
        }
        Ok(substs)
    }

    
    fn callee_def(&self, callee: &str) -> Option<&Func> {
        self.defs
            .get(callee)
            .copied()
            .or_else(|| self.queue.iter().find(|f| f.name == callee))
    }

    
    
    
    
    
    
    
    pub(super) fn take_inline_ret_cell(&mut self, dst: Off) -> Off {
        match self.inline_stack_ret.take().and_then(|b| b.into_iter().next()) {
            Some(RetBind::Gaddr(ga)) => self.materialize(ga),
            Some(RetBind::Stack(base, size)) => {
                if size != 1 {
                    self.fail("a multi-cell StackBuf return needs a `let` binding, not an expression use")
                };
                
                
                
                base
            }
            _ => dst,
        }
    }
    
    
    
    
    
    fn const_arg(&self, a: &Expr) -> Option<Expr> {
        Some(match a {
            Expr::Lit(n) => Expr::Lit(*n),
            Expr::Gen => Expr::GPow(1),
            Expr::GPow(k) => Expr::GPow(*k),
            other => Expr::Lit(self.try_const_index(other)? as u128),
        })
    }
}
