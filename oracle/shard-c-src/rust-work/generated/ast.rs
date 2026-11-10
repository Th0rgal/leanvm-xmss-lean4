

use primitives::field::F192;


#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    
    
    Lit(u128),
    
    
    Gen,
    
    
    GPow(u128),
    
    
    
    GenPow(Box<Expr>),
    
    
    
    Pow(Box<Expr>, Box<Expr>),
    
    Var(String),
    Add(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    
    
    
    Sub(Box<Expr>, Box<Expr>),
    
    
    
    
    Div(Box<Expr>, Box<Expr>),
    Mod(Box<Expr>, Box<Expr>),
    
    
    
    
    
    
    
    FieldDiv(Box<Expr>, Box<Expr>),
    
    Call(String, Vec<Expr>),
    
    HeapBuf(u32),
    
    
    
    
    
    
    HeapBufDyn(Box<Expr>),
    
    
    
    
    StackBuf(u32),
    
    
    
    Index(Box<Expr>, Box<Expr>),
    
    
    
    
    
    Slice(Box<Expr>, Box<Expr>, Box<Expr>),
    
    
    
    
    
    ListLit(Vec<Expr>),
    
    
    
    ListComp(Box<Expr>, String, Box<Expr>, Box<Expr>),
}





#[derive(Clone, Debug)]
pub struct Stmt {
    pub line: u32,
    pub kind: StmtKind,
}

impl Stmt {
    pub fn new(line: u32, kind: StmtKind) -> Self {
        Self { line, kind }
    }

    
    
    pub fn at(&self, kind: StmtKind) -> Self {
        Self { line: self.line, kind }
    }
}


#[derive(Clone, Debug)]
pub enum StmtKind {
    
    Let(String, Expr),
    
    LetTuple(Vec<String>, String, Vec<Expr>),
    
    AssertEq(Expr, Expr),
    
    
    
    AssertNe(Expr, Expr),
    
    
    AssertLt(Expr, LtBound),
    
    Call(String, Vec<Expr>),
    
    
    
    
    
    HintWitness { dest: Expr, name: String },
    
    
    
    
    LetHintWitness { name: String, stream: String },
    
    Print { label: String, value: Expr },
    
    
    
    
    
    If {
        eq: bool,
        lhs: Expr,
        rhs: Expr,
        then: Vec<Stmt>,
        els: Vec<Stmt>,
        
        
        
        
        force_const: bool,
    },
    
    
    
    
    
    
    Match {
        targets: Vec<Expr>,
        x: Expr,
        arms: Vec<Expr>,
    },
    
    Store(Expr, Expr, Expr),
    
    
    
    
    
    For {
        var: String,
        lo: u64,
        hi: ForBound,
        body: Vec<Stmt>,
    },
    
    
    
    
    
    Unroll {
        var: String,
        lo: Expr,
        hi: Expr,
        body: Vec<Stmt>,
    },
    
    Return(Vec<Expr>),
    
    
    CallIfNe(Expr, Expr, String, Vec<Expr>),
}




#[derive(Clone, Debug)]
pub enum ForBound {
    Const(u64),
    Runtime(Expr),
}








#[derive(Clone, Debug)]
pub enum LtBound {
    Const(u64),
    Runtime(Expr),
}


#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Shape {
    
    
    Scalar,
    
    StackBuf(u32),
}

impl Shape {
    
    pub(crate) fn cells(self) -> u32 {
        match self {
            Self::StackBuf(n) => n,
            Self::Scalar => 1,
        }
    }
}


#[derive(Clone, Debug)]
pub(crate) struct Param {
    pub name: String,
    pub kind: ParamKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ParamKind {
    
    Const,
    Runtime(Shape),
}

impl Param {
    pub(crate) fn shape(&self) -> Shape {
        match self.kind {
            ParamKind::Const => Shape::Scalar,
            ParamKind::Runtime(shape) => shape,
        }
    }
}


#[derive(Clone, Debug)]
pub(crate) struct Func {
    pub name: String,
    
    
    pub params: Vec<Param>,
    
    
    pub(crate) return_shapes: Vec<Shape>,
    pub body: Vec<Stmt>,
    
    
    
    pub inline: bool,
}

impl Func {
    pub(crate) fn has_const_params(&self) -> bool {
        self.params.iter().any(|p| p.kind == ParamKind::Const)
    }

    pub(crate) fn param_shapes(&self) -> impl Iterator<Item = Shape> + '_ {
        self.params.iter().map(Param::shape)
    }
}


#[derive(Clone, Debug)]
pub struct Ast {
    pub(crate) funcs: Vec<Func>,
    
    
    
    
    pub const_arrays: Vec<(String, Vec<F192>)>,
}




use std::collections::HashSet;


pub(crate) fn free_vars_expr<'a>(e: &'a Expr, refs: &mut Vec<&'a str>) {
    match e {
        Expr::Var(v) => refs.push(v.as_str()),
        Expr::Add(a, b)
        | Expr::Mul(a, b)
        | Expr::Sub(a, b)
        | Expr::Div(a, b)
        | Expr::FieldDiv(a, b)
        | Expr::Mod(a, b)
        | Expr::Index(a, b)
        | Expr::Pow(a, b) => {
            free_vars_expr(a, refs);
            free_vars_expr(b, refs);
        }
        Expr::Slice(a, lo, hi) => {
            free_vars_expr(a, refs);
            free_vars_expr(lo, refs);
            free_vars_expr(hi, refs);
        }
        Expr::Call(_, args) | Expr::ListLit(args) => args.iter().for_each(|a| free_vars_expr(a, refs)),
        Expr::ListComp(body, var, lo, hi) => {
            let mut inner = Vec::new();
            free_vars_expr(body, &mut inner);
            refs.extend(inner.into_iter().filter(|v| v != var));
            free_vars_expr(lo, refs);
            free_vars_expr(hi, refs);
        }
        Expr::HeapBufDyn(sz) | Expr::GenPow(sz) => free_vars_expr(sz, refs),
        Expr::Lit(_) | Expr::Gen | Expr::GPow(_) | Expr::HeapBuf(_) | Expr::StackBuf(_) => {}
    }
}




pub(crate) fn binds_anywhere<'a>(body: &'a [Stmt], out: &mut HashSet<&'a str>) {
    for s in body {
        match &s.kind {
            StmtKind::Let(n, _) | StmtKind::LetHintWitness { name: n, .. } => {
                out.insert(n.as_str());
            }
            StmtKind::LetTuple(ns, ..) => ns.iter().for_each(|n| {
                out.insert(n.as_str());
            }),
            StmtKind::Match { targets, .. } => targets.iter().for_each(|t| {
                if let Expr::Var(n) = t {
                    out.insert(n.as_str());
                }
            }),
            StmtKind::If { then, els, .. } => {
                binds_anywhere(then, out);
                binds_anywhere(els, out);
            }
            StmtKind::For { var, body, .. } | StmtKind::Unroll { var, body, .. } => {
                out.insert(var.as_str());
                binds_anywhere(body, out);
            }
            _ => {}
        }
    }
}


fn scoped_vars<'a>(body: &'a [Stmt], refs: &mut Vec<&'a str>) {
    let mut inner = HashSet::new();
    for s in body {
        free_vars_stmt(s, refs, &mut inner);
    }
}


pub(crate) fn free_vars_stmt<'a>(s: &'a Stmt, refs: &mut Vec<&'a str>, bound: &mut HashSet<&'a str>) {
    match &s.kind {
        StmtKind::Let(n, e) => {
            free_vars_expr(e, refs);
            bound.insert(n.as_str());
        }
        StmtKind::LetTuple(ns, _, args) => {
            args.iter().for_each(|a| free_vars_expr(a, refs));
            ns.iter().for_each(|n| {
                bound.insert(n.as_str());
            });
        }
        StmtKind::AssertEq(a, b) | StmtKind::AssertNe(a, b) => {
            free_vars_expr(a, refs);
            free_vars_expr(b, refs);
        }
        StmtKind::AssertLt(e, bound) => {
            free_vars_expr(e, refs);
            if let LtBound::Runtime(b) = bound {
                free_vars_expr(b, refs);
            }
        }
        StmtKind::HintWitness { dest, .. } => free_vars_expr(dest, refs),
        StmtKind::LetHintWitness { name, .. } => {
            bound.insert(name.as_str());
        }
        StmtKind::Print { value, .. } => free_vars_expr(value, refs),
        StmtKind::If {
            lhs,
            rhs,
            then,
            els,
            force_const,
            ..
        } => {
            free_vars_expr(lhs, refs);
            free_vars_expr(rhs, refs);
            
            
            
            
            
            
            
            
            
            
            
            if *force_const || matches!((lhs, rhs), (Expr::Lit(_), Expr::Lit(_))) {
                then.iter().for_each(|s| free_vars_stmt(s, refs, bound));
                els.iter().for_each(|s| free_vars_stmt(s, refs, bound));
            } else {
                scoped_vars(then, refs);
                scoped_vars(els, refs);
            }
        }
        StmtKind::Match { targets, x, arms } => {
            free_vars_expr(x, refs);
            arms.iter().for_each(|a| free_vars_expr(a, refs));
            for t in targets {
                match t {
                    Expr::Var(n) => {
                        bound.insert(n.as_str());
                    }
                    
                    other => free_vars_expr(other, refs),
                }
            }
        }
        StmtKind::CallIfNe(a, b, _, args) => {
            free_vars_expr(a, refs);
            free_vars_expr(b, refs);
            args.iter().for_each(|e| free_vars_expr(e, refs));
        }
        StmtKind::Call(_, args) => args.iter().for_each(|a| free_vars_expr(a, refs)),
        StmtKind::Store(arr, idx, val) => {
            free_vars_expr(arr, refs);
            free_vars_expr(idx, refs);
            free_vars_expr(val, refs);
        }
        StmtKind::Return(es) => es.iter().for_each(|e| free_vars_expr(e, refs)),
        StmtKind::For { hi, body, .. } => {
            if let ForBound::Runtime(b) = hi {
                free_vars_expr(b, refs);
            }
            
            
            
            
            scoped_vars(body, refs);
        }
        StmtKind::Unroll { var, lo, hi, body } => {
            free_vars_expr(lo, refs);
            free_vars_expr(hi, refs);
            
            
            let fresh = bound.insert(var.as_str());
            body.iter().for_each(|s| free_vars_stmt(s, refs, bound));
            if fresh && !binds_through(body, var) {
                bound.remove(var.as_str());
            }
        }
    }
}


pub(crate) fn binds(s: &StmtKind, name: &str) -> bool {
    match s {
        StmtKind::Let(n, _) | StmtKind::LetHintWitness { name: n, .. } => n == name,
        StmtKind::LetTuple(ns, ..) => ns.iter().any(|n| n == name),
        StmtKind::Match { targets, .. } => targets.iter().any(|t| matches!(t, Expr::Var(n) if n == name)),
        _ => false,
    }
}





fn binds_through(body: &[Stmt], name: &str) -> bool {
    body.iter().any(|s| match &s.kind {
        StmtKind::If { then, els, .. } => binds_through(then, name) || binds_through(els, name),
        StmtKind::Unroll { body, .. } => binds_through(body, name),
        kind => binds(kind, name),
    })
}








pub(crate) fn rebinds_in_block(body: &[Stmt], name: &str) -> bool {
    body.iter().any(|s| match &s.kind {
        StmtKind::If { then, els, .. } => [then, els]
            .iter()
            .any(|arm| binds_through(arm, name) || rebinds_in_block(arm, name)),
        StmtKind::Unroll { body, .. } => binds_through(body, name) || rebinds_in_block(body, name),
        
        StmtKind::For { var, body, .. } => var != name && rebinds_in_block(body, name),
        _ => false,
    })
}
