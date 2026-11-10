












use super::*;







pub(crate) fn subst_stmts(stmts: &[Stmt], name: &str, to: &Expr) -> Vec<Stmt> {
    subst_all(stmts, &[(name, to)])
}





pub(crate) fn subst_all(stmts: &[Stmt], subs: &[(&str, &Expr)]) -> Vec<Stmt> {
    let mut active = subs.to_vec();
    let mut out = Vec::with_capacity(stmts.len());
    for s in stmts {
        if active.is_empty() {
            out.push(s.clone());
            continue;
        }
        out.push(s.at(subst_kind(&s.kind, &active)));
        active.retain(|(name, _)| !binds(&s.kind, name));
    }
    out
}

fn subst_kind(s: &StmtKind, subs: &[(&str, &Expr)]) -> StmtKind {
    let e = |x: &Expr| subst_vars(x, subs);
    let es = |xs: &[Expr]| xs.iter().map(e).collect();
    
    let body = |var: &str, body: &[Stmt]| {
        if subs.iter().any(|(name, _)| *name == var) {
            let rest: Vec<_> = subs.iter().copied().filter(|(name, _)| *name != var).collect();
            subst_all(body, &rest)
        } else {
            subst_all(body, subs)
        }
    };
    match s {
        StmtKind::Let(n, x) => StmtKind::Let(n.clone(), e(x)),
        StmtKind::LetTuple(ns, f, args) => StmtKind::LetTuple(ns.clone(), f.clone(), es(args)),
        StmtKind::AssertEq(a, b) => StmtKind::AssertEq(e(a), e(b)),
        StmtKind::AssertNe(a, b) => StmtKind::AssertNe(e(a), e(b)),
        StmtKind::AssertLt(a, bound) => StmtKind::AssertLt(
            e(a),
            match bound {
                LtBound::Const(k) => LtBound::Const(*k),
                LtBound::Runtime(b) => LtBound::Runtime(e(b)),
            },
        ),
        StmtKind::Call(f, args) => StmtKind::Call(f.clone(), es(args)),
        StmtKind::Print { label, value } => StmtKind::Print {
            label: label.clone(),
            value: e(value),
        },
        StmtKind::LetHintWitness { name, stream } => StmtKind::LetHintWitness {
            name: name.clone(),
            stream: stream.clone(),
        },
        StmtKind::HintWitness { dest, name } => StmtKind::HintWitness {
            dest: e(dest),
            name: name.clone(),
        },
        StmtKind::Store(a, i, v) => StmtKind::Store(e(a), e(i), e(v)),
        StmtKind::Return(xs) => StmtKind::Return(es(xs)),
        StmtKind::CallIfNe(a, b, f, args) => StmtKind::CallIfNe(e(a), e(b), f.clone(), es(args)),
        StmtKind::For { var, lo, hi, body: b } => StmtKind::For {
            var: var.clone(),
            lo: *lo,
            hi: match hi {
                ForBound::Const(k) => ForBound::Const(*k),
                ForBound::Runtime(x) => ForBound::Runtime(e(x)),
            },
            body: body(var, b),
        },
        StmtKind::Unroll { var, lo, hi, body: b } => StmtKind::Unroll {
            var: var.clone(),
            lo: e(lo),
            hi: e(hi),
            body: body(var, b),
        },
        StmtKind::If {
            eq,
            lhs,
            rhs,
            then,
            els,
            force_const,
        } => StmtKind::If {
            eq: *eq,
            lhs: e(lhs),
            rhs: e(rhs),
            then: subst_all(then, subs),
            els: subst_all(els, subs),
            force_const: *force_const,
        },
        
        
        
        StmtKind::Match { targets, x, arms } => StmtKind::Match {
            targets: targets
                .iter()
                .map(|t| if matches!(t, Expr::Var(_)) { t.clone() } else { e(t) })
                .collect(),
            x: e(x),
            arms: es(arms),
        },
    }
}



pub(crate) fn subst_var(e: &Expr, name: &str, to: &Expr) -> Expr {
    subst_vars(e, &[(name, to)])
}

fn subst_vars(e: &Expr, subs: &[(&str, &Expr)]) -> Expr {
    let s = |b: &Expr| Box::new(subst_vars(b, subs));
    match e {
        Expr::Var(v) => match subs.iter().find(|(name, _)| name == v) {
            Some((_, to)) => (*to).clone(),
            None => e.clone(),
        },
        Expr::Add(a, b) => Expr::Add(s(a), s(b)),
        Expr::Mul(a, b) => Expr::Mul(s(a), s(b)),
        Expr::Sub(a, b) => Expr::Sub(s(a), s(b)),
        Expr::Div(a, b) => Expr::Div(s(a), s(b)),
        Expr::FieldDiv(a, b) => Expr::FieldDiv(s(a), s(b)),
        Expr::Mod(a, b) => Expr::Mod(s(a), s(b)),
        Expr::Index(a, b) => Expr::Index(s(a), s(b)),
        Expr::Slice(a, lo, hi) => Expr::Slice(s(a), s(lo), s(hi)),
        Expr::GenPow(e) => Expr::GenPow(s(e)),
        Expr::Pow(a, b) => Expr::Pow(s(a), s(b)),
        Expr::HeapBufDyn(sz) => Expr::HeapBufDyn(s(sz)),
        Expr::ListLit(es) => Expr::ListLit(es.iter().map(|a| subst_vars(a, subs)).collect()),
        Expr::ListComp(body, var, lo, hi) => Expr::ListComp(
            if subs.iter().any(|(name, _)| name == var) {
                let rest: Vec<_> = subs.iter().copied().filter(|(name, _)| name != var).collect();
                Box::new(subst_vars(body, &rest))
            } else {
                s(body)
            },
            var.clone(),
            s(lo),
            s(hi),
        ),
        Expr::Call(f, args) => Expr::Call(f.clone(), args.iter().map(|a| subst_vars(a, subs)).collect()),
        other => other.clone(),
    }
}
