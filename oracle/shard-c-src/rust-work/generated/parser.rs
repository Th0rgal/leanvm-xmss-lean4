













use super::*;
use std::collections::BTreeMap;

mod consts;
mod expr;
mod subst;
pub use consts::parse_const;
use consts::{
    apply_replacements, const_int_expr, eval_const_int, gpow_bound, is_int_arith, parse_f192_const, parse_gpow_bound,
};
use expr::{
    binding_name, call_args, is_ident, parse_expr, split_assign, split_aug, split_once_top, split_top, string_lit,
    strip_comment, strip_const_wrapper, top_level_cmp,
};
pub(crate) use subst::{subst_all, subst_stmts, subst_var};



pub fn parse(src: &str) -> Result<Ast, String> {
    parse_with_replacements(src, &BTreeMap::new())
}








pub fn parse_with_replacements(src: &str, replacements: &BTreeMap<String, String>) -> Result<Ast, String> {
    
    
    
    
    
    
    
    
    if let Some((k, _)) = replacements
        .iter()
        .find(|(_, v)| v.contains('\n') || v.contains('#') || v.contains('"'))
    {
        return Err(format!(
            "placeholder `{k}` contains a newline, `#` or `\"`, which would reshape the line"
        ));
    }
    let src = apply_replacements(src, replacements);
    
    
    
    let mut lines: Vec<Line> = Vec::new();
    for (src_line, raw) in src.lines().enumerate() {
        let no_comment = strip_comment(raw);
        if no_comment.trim().is_empty() {
            continue;
        }
        let t = no_comment.trim();
        if let Some(rest) = t.strip_prefix("import ").or_else(|| t.strip_prefix("from ")) {
            let module = rest.split_whitespace().next().unwrap_or("");
            if module != "snark_lib" {
                return Err(locate(
                    src_line + 1,
                    format!("file imports are not supported (only the `snark_lib` stub): `{t}`"),
                ));
            }
            continue; 
        }
        let indent = no_comment.len() - no_comment.trim_start().len();
        lines.push(Line {
            src: src_line + 1,
            indent,
            text: no_comment.trim().to_string(),
        });
    }
    
    
    
    
    
    
    let mut consts: BTreeMap<String, String> = BTreeMap::new();
    let mut const_arrays: Vec<(String, Vec<F192>)> = Vec::new();
    let mut start = 0;
    while start < lines.len() {
        let Line {
            src,
            indent,
            text: line,
        } = &lines[start];
        let at = |e: String| locate(*src, e);
        if *indent == 0 && (line.starts_with("def ") || line.starts_with('@')) {
            break;
        }
        if *indent != 0 {
            return Err(at(format!("unexpected indentation at top level: `{line}`")));
        }
        let (lhs, rhs) = split_assign(line).ok_or_else(|| {
            at(format!(
                "top level: expected `def`, a global constant `NAME = value`, or the `snark_lib` import, got `{line}`"
            ))
        })?;
        let name = lhs.trim().to_string();
        if !is_ident(&name) {
            return Err(at(format!(
                "global constant name must be a plain identifier: `{}`",
                lhs.trim()
            )));
        }
        if consts.contains_key(&name) || const_arrays.iter().any(|(n, _)| n == &name) {
            return Err(at(format!("global constant `{name}` is declared twice")));
        }
        
        
        
        
        if BUILTINS.contains(&name.as_str()) {
            return Err(at(format!(
                "`{name}` is a builtin, so a global constant of that name would be substituted \
                 into its own call sites. Rename it"
            )));
        }
        
        let rhs = apply_replacements(rhs.trim(), &consts);
        let rhs = rhs.trim();
        if let Some(inner) = rhs.strip_prefix('[').and_then(|s| s.strip_suffix(']')) {
            
            
            
            let mut elems = Vec::new();
            for part in split_top(inner, ',') {
                let p = part.trim();
                if p.is_empty() {
                    continue; 
                }
                let elem = if let Some(v) = parse_f192_const(p) {
                    v.map_err(|e| at(format!("global constant array `{name}`: {e}")))?
                } else {
                    let n = eval_const_int(p).map_err(|e| at(format!("global constant array `{name}`: {e}")))?;
                    F192::new(n as u64, (n >> 64) as u64, 0)
                };
                elems.push(elem);
            }
            const_arrays.push((name, elems));
        } else {
            
            
            if let Some(value) = parse_f192_const(rhs) {
                let v = value.map_err(|e| at(format!("global constant `{name}`: {e}")))?;
                consts.insert(name, format!("f192({},{},{})", v.c0, v.c1, v.c2));
            } else if let Ok(value) = eval_const_int(rhs) {
                consts.insert(name, value.to_string());
            } else if parse_expr(rhs).is_ok_and(|e| is_int_arith(&e)) {
                
                
                return Err(at(format!(
                    "global constant `{name}`: `{rhs}` overflows a u128, goes negative or divides by zero"
                )));
            } else {
                
                
                
                
                
                let v = parse_const(rhs).map_err(|e| at(format!("global constant `{name}`: {e}")))?;
                consts.insert(
                    name,
                    if v.c2 == 0 {
                        (v.c0 as u128 | ((v.c1 as u128) << 64)).to_string()
                    } else {
                        format!("f192({},{},{})", v.c0, v.c1, v.c2)
                    },
                );
            }
        }
        start += 1;
    }
    
    let func_lines: Vec<Line> = lines[start..]
        .iter()
        .map(|l| Line {
            src: l.src,
            indent: l.indent,
            text: apply_replacements(&l.text, &consts),
        })
        .collect();
    let mut p = Parser {
        lines: &func_lines,
        i: 0,
    };
    let mut funcs = Vec::new();
    while p.i < p.lines.len() {
        funcs.push(p.func()?);
    }
    
    
    
    
    
    
    for (i, f) in funcs.iter().enumerate() {
        if funcs[..i].iter().any(|g| g.name == f.name) {
            return Err(format!("function `{}` is defined twice", f.name));
        }
        if f.name.contains("__") {
            return Err(format!(
                "function name `{}` may not contain `__`, which is reserved for the names the \
                 compiler generates (a loop helper, a `Const` specialization)",
                f.name
            ));
        }
        
        
        
        
        if BUILTINS.contains(&f.name.as_str()) {
            return Err(format!(
                "`{}` is a builtin, so a function of that name could never be called: \
                 the builtin takes every call site. Rename it",
                f.name
            ));
        }
    }
    infer_return_shapes(&mut funcs);
    Ok(Ast { funcs, const_arrays })
}




const BUILTINS: &[&str] = &[
    "GEN",
    "log",
    "print",
    "range",
    "unroll",
    "mul_range",
    "addr",
    "assert_in_k",
    "assert_gpow",
    "keccak",
    "keccak_cells",
    "const",
    "f192",
    "hint_decompose_bits",
    "hint_decompose_bits_exponent",
    "hint_decompose_digits_exponent",
    "hint_windows_exponent",
    "hint_f192_limbs",
    "hint_log2_ceil",
    "hint_witness",
    "len",
    "match",
    "HeapBuf",
    "StackBuf",
];





fn infer_return_shapes(funcs: &mut [Func]) {
    fn expr_shape(e: &Expr, locals: &HashMap<&str, Shape>, known: &HashMap<String, Vec<Shape>>) -> Shape {
        match e {
            Expr::Var(v) => locals.get(v.as_str()).copied().unwrap_or(Shape::Scalar),
            Expr::StackBuf(n) => Shape::StackBuf(*n),
            Expr::ListLit(es) => Shape::StackBuf(es.len() as u32),
            Expr::Call(f, _) => known
                .get(f)
                .filter(|r| r.len() == 1)
                .and_then(|r| r.first())
                .copied()
                .unwrap_or(Shape::Scalar),
            _ => Shape::Scalar,
        }
    }

    fn scan(body: &[Stmt], params: &[Param], known: &HashMap<String, Vec<Shape>>, n_ret: usize) -> Vec<Shape> {
        
        
        
        let mut locals: HashMap<&str, Shape> = params.iter().map(|p| (p.name.as_str(), p.shape())).collect();
        let mut returns = vec![Shape::Scalar; n_ret];
        for stmt in body {
            match &stmt.kind {
                StmtKind::Let(name, e) => {
                    let shape = expr_shape(e, &locals, known);
                    locals.insert(name.as_str(), shape);
                }
                StmtKind::LetTuple(names, f, _) => {
                    let shapes = known.get(f);
                    for (i, name) in names.iter().enumerate() {
                        let shape = shapes.and_then(|s| s.get(i)).copied().unwrap_or(Shape::Scalar);
                        locals.insert(name.as_str(), shape);
                    }
                }
                
                
                
                StmtKind::Unroll { var, body, .. } => {
                    locals.insert(var.as_str(), Shape::Scalar);
                    for inner in body {
                        if let StmtKind::Let(name, e) = &inner.kind {
                            let shape = expr_shape(e, &locals, known);
                            locals.insert(name.as_str(), shape);
                        }
                    }
                }
                StmtKind::LetHintWitness { name, .. } => {
                    locals.insert(name.as_str(), Shape::Scalar);
                }
                StmtKind::Return(es) => {
                    returns = es.iter().map(|e| expr_shape(e, &locals, known)).collect();
                }
                _ => {}
            }
        }
        returns
    }

    let mut known: HashMap<String, Vec<Shape>> = funcs
        .iter()
        .map(|f| (f.name.clone(), f.return_shapes.clone()))
        .collect();
    
    
    
    for _ in 0..=funcs.len() {
        let next: HashMap<String, Vec<Shape>> = funcs
            .iter()
            .map(|f| (f.name.clone(), scan(&f.body, &f.params, &known, f.return_shapes.len())))
            .collect();
        if next == known {
            break;
        }
        known = next;
    }
    for f in funcs {
        f.return_shapes = known
            .remove(&f.name)
            .expect("every function has inferred return shapes");
    }
}











fn whole_call(s: &str) -> bool {
    let Some(inner) = s.find('(').map(|i| &s[i + 1..]) else {
        return false;
    };
    let (mut depth, mut in_str) = (0i32, false);
    for (i, c) in inner.bytes().enumerate() {
        if in_str {
            in_str = c != b'"';
            continue;
        }
        match c {
            b'"' => in_str = true,
            b'(' | b'[' => depth += 1,
            b')' | b']' => {
                depth -= 1;
                
                
                if depth < 0 {
                    return i + 1 == inner.len();
                }
            }
            _ => {}
        }
    }
    false
}

fn locate(line: usize, e: String) -> String {
    if e.starts_with("line ") {
        e
    } else {
        format!("line {line}: {e}")
    }
}

struct Line {
    src: usize,
    indent: usize,
    text: String,
}

struct Parser<'a> {
    lines: &'a [Line],
    i: usize,
}

impl Parser<'_> {
    
    
    
    fn here(&self) -> usize {
        self.lines
            .get(self.i)
            .or_else(|| self.lines.last())
            .map_or(0, |l| l.src)
    }

    fn func(&mut self) -> Result<Func, String> {
        let here = self.lines.get(self.i).map_or(0, |l| l.src);
        self.func_inner().map_err(|e| locate(here, e))
    }

    fn func_inner(&mut self) -> Result<Func, String> {
        let mut line = &self.lines[self.i];
        
        let inline = if let Some(dec) = line.text.strip_prefix('@') {
            if dec.trim() != "inline" {
                return Err(format!("unknown decorator `@{}` (only `@inline`)", dec.trim()));
            }
            self.i += 1;
            line = self.lines.get(self.i).ok_or("`@inline` must precede a `def`")?;
            true
        } else {
            false
        };
        
        
        let at_def = self.here();
        self.func_header(inline, line.indent, &line.text)
            .map_err(|e| locate(at_def, e))
    }

    fn func_header(&mut self, inline: bool, indent: usize, line: &str) -> Result<Func, String> {
        let header = line
            .strip_prefix("def ")
            .ok_or_else(|| format!("expected `def`, got `{line}`"))?;
        let header = header.strip_suffix(':').ok_or("function header needs `:`")?;
        let open = header.find('(').ok_or("function header needs `(`")?;
        let name = header[..open].trim().to_string();
        let close = header
            .rfind(')')
            .filter(|&c| c > open)
            .ok_or("function header needs `)` after `(`")?;
        let params_str = header[open + 1..close].trim();
        let mut params = Vec::new();
        if !params_str.is_empty() {
            for part in params_str.split(',') {
                if part.trim().is_empty() {
                    return Err(format!("`def {name}`: empty parameter (a trailing comma?)"));
                }
                
                
                let (param_name, annotation) = part.split_once(':').map_or((part, None), |(n, a)| (n, Some(a.trim())));
                let kind = match annotation {
                    None => ParamKind::Runtime(Shape::Scalar),
                    Some("Const") => ParamKind::Const,
                    Some(ann) => {
                        let size = ann.strip_prefix("StackBuf(").and_then(|r| r.strip_suffix(')')).ok_or_else(|| {
                            format!("unsupported parameter annotation `{ann}` (`Const`, or `StackBuf(n)` to pass a run of cells)")
                        })?;
                        let k =
                            eval_const_int(size).map_err(|e| format!("`def {name}`: StackBuf parameter size: {e}"))?;
                        let k = u32::try_from(k).map_err(|_| format!("`def {name}`: StackBuf({k}) is too large"))?;
                        if k == 0 {
                            return Err(format!("`def {name}`: a StackBuf parameter needs at least one cell"));
                        }
                        ParamKind::Runtime(Shape::StackBuf(k))
                    }
                };
                params.push(Param {
                    name: binding_name(param_name, "parameter name")?,
                    kind,
                });
            }
        }
        if let Some(dup) = params
            .iter()
            .enumerate()
            .find_map(|(i, p)| params[..i].iter().any(|q| q.name == p.name).then_some(&p.name))
        {
            return Err(format!("parameter `{dup}` is declared twice"));
        }
        self.i += 1;
        let body = self.block(indent)?;
        if let Some(p) = params
            .iter()
            .find(|p| p.kind == ParamKind::Const && rebinds_in_block(&body, &p.name))
        {
            return Err(format!(
                "`def {name}`: `{}` is a Const parameter, substituted as a literal into the body, so it \
                 cannot be rebound inside an `if` or an `unroll`; bind a new name",
                p.name
            ));
        }
        let n_ret = body
            .iter()
            .filter_map(|s| {
                if let StmtKind::Return(es) = &s.kind {
                    Some(es.len())
                } else {
                    None
                }
            })
            .max()
            .unwrap_or(0);
        Ok(Func {
            name,
            params,
            return_shapes: vec![Shape::Scalar; n_ret],
            body,
            inline,
        })
    }

    
    fn block(&mut self, parent: usize) -> Result<Vec<Stmt>, String> {
        let mut stmts = Vec::new();
        let block_indent = match self.lines.get(self.i) {
            Some(Line { indent: ind, .. }) if *ind > parent => *ind,
            _ => return Err(locate(self.here(), "expected an indented block".into())),
        };
        while let Some(Line { indent: ind, .. }) = self.lines.get(self.i) {
            if *ind != block_indent {
                if *ind > parent && *ind > block_indent {
                    return Err(locate(self.here(), "inconsistent indentation".into()));
                }
                break;
            }
            stmts.push(self.stmt(block_indent)?);
        }
        Ok(stmts)
    }

    fn stmt(&mut self, indent: usize) -> Result<Stmt, String> {
        let here = self.lines.get(self.i).map_or(0, |l| l.src);
        self.stmt_inner(indent)
            .map(|kind| Stmt::new(here as u32, kind))
            .map_err(|e| locate(here, e))
    }

    fn stmt_inner(&mut self, indent: usize) -> Result<StmtKind, String> {
        let line = self.lines[self.i].text.as_str();
        if let Some(rest) = line.strip_prefix("for ") {
            
            
            
            let rest = rest.strip_suffix(':').ok_or("`for` needs `:`")?;
            let (var, iter) = rest.split_once(" in ").ok_or("`for` needs `in`")?;
            
            
            
            if let Some(parts) = call_args(iter, "unroll") {
                if parts.len() != 2 {
                    return Err("unroll needs `a, b` (compile-time integers)".into());
                }
                let (lo, hi) = (parse_expr(parts[0])?, parse_expr(parts[1])?);
                let var = binding_name(var, "loop counter")?;
                self.i += 1;
                let body = self.block(indent)?;
                if rebinds_in_block(&body, &var) {
                    return Err(format!(
                        "the `unroll` counter `{var}` is substituted as a literal into each copy of the body, \
                         so it cannot be rebound inside an `if` or an `unroll`; bind a new name"
                    ));
                }
                return Ok(StmtKind::Unroll { var, lo, hi, body });
            }
            let parts = call_args(iter, "mul_range").ok_or("`for` needs `mul_range(start, stop)` or `unroll(a, b)`")?;
            if parts.len() != 2 {
                return Err("mul_range needs `start, stop`".into());
            }
            let lo = parse_gpow_bound(parts[0])?;
            
            
            let hi = match parse_gpow_bound(parts[1]) {
                Ok(hi) => {
                    if lo > hi {
                        return Err(format!("mul_range: start GEN**{lo} must not exceed stop GEN**{hi}"));
                    }
                    ForBound::Const(hi)
                }
                Err(_) => {
                    let stop = parse_expr(parts[1])?;
                    
                    
                    
                    
                    
                    
                    
                    
                    
                    
                    
                    
                    if let Expr::Lit(n) = stop {
                        return Err(format!(
                            "mul_range stop bound `{n}` is not a power of GEN, so the multiplicative walk \
                             never reaches it: write `GEN ** k`"
                        ));
                    }
                    ForBound::Runtime(stop)
                }
            };
            self.i += 1;
            let body = self.block(indent)?;
            return Ok(StmtKind::For {
                var: binding_name(var, "loop counter")?,
                lo,
                hi,
                body,
            });
        }
        if let Some(rest) = line.strip_prefix("if ") {
            return self.if_stmt(rest, indent);
        }
        self.i += 1;
        if line == "return" {
            return Ok(StmtKind::Return(vec![]));
        }
        if let Some(rest) = line.strip_prefix("return ") {
            return Ok(StmtKind::Return(
                split_top(rest, ',')
                    .iter()
                    .map(|e| parse_expr(e))
                    .collect::<Result<_, _>>()?,
            ));
        }
        
        
        if let Some(parts) = call_args(line, "print") {
            let (label, value) = match parts.as_slice() {
                [l, v] if l.trim().starts_with('"') => {
                    let l = string_lit(l).ok_or("print's label is a string literal: print(\"label\", expr)")?;
                    (l.to_string(), v.trim())
                }
                [v] => (v.trim().to_string(), v.trim()),
                _ => return Err("print takes `print(expr)` or `print(\"label\", expr)`".into()),
            };
            return Ok(StmtKind::Print {
                label,
                value: parse_expr(value)?,
            });
        }
        
        
        
        
        if let Some(parts) = call_args(line, "hint_witness").filter(|_| whole_call(line)) {
            let [dest, name] = parts.as_slice() else {
                return Err("hint_witness(dest, \"name\") takes two arguments".into());
            };
            let name = string_lit(name).ok_or("hint_witness's second argument is a string literal: \"name\"")?;
            return Ok(StmtKind::HintWitness {
                dest: parse_expr(dest)?,
                name: name.to_string(),
            });
        }
        if let Some(rest) = line.strip_prefix("assert ") {
            if let Some((a, b)) = split_once_top(rest, "==") {
                return Ok(StmtKind::AssertEq(parse_expr(a)?, parse_expr(b)?));
            }
            if let Some((a, b)) = split_once_top(rest, "!=") {
                return Ok(StmtKind::AssertNe(parse_expr(a)?, parse_expr(b)?));
            }
            
            
            
            if let Some((a, b)) = split_once_top(rest, "<") {
                let x =
                    strip_log(a)?.ok_or("a `<` assert compares logs: `assert log X < log Y` or `assert log X < k`")?;
                let bound = match strip_log(b)? {
                    
                    
                    
                    
                    
                    
                    Some(y) => {
                        let y = parse_expr(y)?;
                        match gpow_bound(&y) {
                            Ok(k) => LtBound::Const(k),
                            Err(e) if const_int_expr(&y).is_some() => return Err(e),
                            Err(_) => LtBound::Runtime(y),
                        }
                    }
                    
                    None => match const_int_expr(&parse_expr(b)?) {
                        Some(k) => {
                            LtBound::Const(u64::try_from(k).map_err(|_| format!("log bound {k} does not fit in u64"))?)
                        }
                        None => {
                            return Err(format!(
                                "a log bound must be `log _` or a parse-time integer, got `{b}`"
                            ));
                        }
                    },
                };
                return Ok(StmtKind::AssertLt(parse_expr(x)?, bound));
            }
            return Err("`assert` needs `==`, `!=`, or `log _ < _`".into());
        }
        
        
        let expanded = split_aug(line)?.map(|(lhs, op, rhs)| format!("{lhs} = {lhs} {op} ({rhs})"));
        let line = expanded.as_deref().unwrap_or(line);
        
        if let Some((lhs, rhs)) = split_assign(line) {
            
            
            if rhs.trim_start().starts_with("match(") {
                return parse_match(lhs, rhs);
            }
            
            
            
            if let Some(parts) = call_args(rhs.trim(), "hint_witness").filter(|_| whole_call(rhs.trim())) {
                let [stream] = parts.as_slice() else {
                    return Err(
                        "`x = hint_witness(\"stream\")` takes one argument; to fill a run, write \
                         `hint_witness(dest, \"stream\")` as a statement"
                            .into(),
                    );
                };
                let stream = string_lit(stream).ok_or("hint_witness's argument is a string literal: \"stream\"")?;
                return Ok(StmtKind::LetHintWitness {
                    name: binding_name(lhs, "binding name")?,
                    stream: stream.to_string(),
                });
            }
            let rhs_expr = parse_expr(rhs)?;
            
            if lhs.trim_end().ends_with(']') {
                let lhs = lhs.trim();
                let open = lhs.find('[').ok_or("malformed store target")?;
                let arr = parse_expr(&lhs[..open])?;
                let idx = parse_expr(&lhs[open + 1..lhs.len() - 1])?;
                return Ok(StmtKind::Store(arr, idx, rhs_expr));
            }
            let targets = split_top(lhs, ',');
            if targets.len() == 1 {
                return Ok(StmtKind::Let(binding_name(targets[0], "binding name")?, rhs_expr));
            }
            
            if let Expr::Call(f, args) = rhs_expr {
                let names = targets
                    .iter()
                    .map(|t| binding_name(t, "binding name"))
                    .collect::<Result<Vec<_>, _>>()?;
                return Ok(StmtKind::LetTuple(names, f, args));
            }
            return Err("tuple assignment requires a call on the right".into());
        }
        
        
        
        
        
        
        let keyword = ["while ", "elif ", "else", "for ", "def "]
            .iter()
            .any(|k| line.starts_with(k));
        if let Some(op) = top_level_cmp(line).filter(|_| !keyword) {
            let fix = if matches!(op, "==" | "!=") {
                format!("write `assert {line}`")
            } else {
                format!("`{op}` is not a predicate: order facts come from `assert log x < k`")
            };
            return Err(format!("`{line}` is a comparison, not a statement: {fix}"));
        }
        
        if let Expr::Call(f, args) = parse_expr(line)? {
            return Ok(StmtKind::Call(f, args));
        }
        Err(format!("statement has no effect: `{line}`"))
    }

    
    
    
    
    fn if_stmt(&mut self, header: &str, indent: usize) -> Result<StmtKind, String> {
        let cond = header.strip_suffix(':').ok_or("`if` needs `:`")?;
        let (cond, force_const) = match strip_const_wrapper(cond) {
            Some(inner) => (inner, true),
            
            
            
            
            
            
            
            
            None if top_level_cmp(cond).is_none()
                && cond
                    .trim_start()
                    .strip_prefix("const")
                    .is_some_and(|r| r.trim_start().starts_with('(')) =>
            {
                return Err(
                    "`const(...)` must wrap the WHOLE condition and balance its brackets: `if const(a == b):`".into(),
                );
            }
            None => (cond, false),
        };
        let (eq, l, r) = if let Some((l, r)) = split_once_top(cond, "==") {
            (true, l, r)
        } else if let Some((l, r)) = split_once_top(cond, "!=") {
            (false, l, r)
        } else {
            return Err("an `if` condition must be `a == b` or `a != b`".into());
        };
        let (lhs, rhs) = (parse_expr(l)?, parse_expr(r)?);
        self.i += 1;
        let then = self.block(indent)?;
        let mut els = Vec::new();
        if let Some(Line {
            indent: ind,
            text: line,
            ..
        }) = self.lines.get(self.i)
            && *ind == indent
        {
            if line == "else:" {
                self.i += 1;
                els = self.block(indent)?;
            } else if let Some(rest) = line.strip_prefix("elif ") {
                
                
                let at_elif = self.here();
                els = vec![Stmt::new(
                    at_elif as u32,
                    self.if_stmt(rest, indent).map_err(|e| locate(at_elif, e))?,
                )];
            }
        }
        Ok(StmtKind::If {
            eq,
            lhs,
            rhs,
            then,
            els,
            force_const,
        })
    }
}

type Aug<'a> = Option<(&'a str, &'static str, &'a str)>;






fn strip_log(s: &str) -> Result<Option<&str>, String> {
    let Some(r) = s.trim().strip_prefix("log").filter(|r| r.starts_with([' ', '('])) else {
        return Ok(None);
    };
    let r = r.trim_start();
    if r.starts_with('(') && !whole_call(r) {
        return Err(format!("`{}`: put the whole operand inside `log(…)`", s.trim()));
    }
    Ok(Some(r))
}







fn parse_match(lhs: &str, rhs: &str) -> Result<StmtKind, String> {
    
    
    
    let targets = split_top(lhs, ',')
        .iter()
        .map(|t| match parse_expr(t)? {
            e @ (Expr::Var(_) | Expr::Index(..)) => Ok(e),
            other => Err(format!(
                "a `match` target must be a name or a StackBuf element, got `{other:?}`"
            )),
        })
        .collect::<Result<Vec<_>, _>>()?;
    let chunks = call_args(rhs, "match").ok_or("malformed `match(…)`")?;
    let (first, pairs) = chunks.split_first().ok_or("match needs arguments")?;
    let x = strip_log(first)?.ok_or("`match` matches logs: `match(log(x), …)`")?;
    let x = parse_expr(x)?;
    if pairs.is_empty() || !pairs.len().is_multiple_of(2) {
        return Err("match needs `range(a, b), lambda i: …` pairs after the scrutinee".into());
    }
    let mut arms = Vec::new();
    for pair in pairs.chunks(2) {
        let (lo, hi) = match parse_expr(pair[0])? {
            Expr::Call(f, args) if f == "range" => match args.as_slice() {
                [Expr::Lit(a), Expr::Lit(b)] if a < b => (*a, *b),
                _ => return Err("match needs `range(a, b)` with integer literals, a < b".into()),
            },
            other => return Err(format!("expected `range(a, b)`, got `{other:?}`")),
        };
        if lo != arms.len() as u128 {
            return Err(format!(
                "match ranges must be contiguous from 0: expected a range starting at {}, got {lo}",
                arms.len()
            ));
        }
        let lam = pair[1]
            .trim()
            .strip_prefix("lambda ")
            .ok_or("expected `lambda i: …` after each range")?;
        let (param, body) = split_once_top(lam, ":").ok_or("`lambda` needs `:`")?;
        let param = binding_name(param, "lambda parameter")?;
        let body = parse_expr(body)?;
        for j in lo..hi {
            arms.push(subst_var(&body, &param, &Expr::Lit(j)));
        }
    }
    Ok(StmtKind::Match { targets, x, arms })
}
