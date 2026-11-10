















use super::*;



pub(super) fn parse_expr(s: &str) -> Result<Expr, String> {
    let s = s.trim();
    
    
    let (segs, ops) = split_add(s);
    if !ops.is_empty() {
        return fold_ops(&segs, &ops, |op, l, r| match op {
            b'+' => Expr::Add(l, r),
            _ => Expr::Sub(l, r),
        });
    }
    
    let (segs, ops) = split_mul(s);
    if !ops.is_empty() {
        return fold_ops(&segs, &ops, |op, l, r| match op {
            b'*' => Expr::Mul(l, r),
            b'/' => Expr::Div(l, r),
            b'd' => Expr::FieldDiv(l, r),
            _ => Expr::Mod(l, r),
        });
    }
    
    
    
    
    if let Some((base, exp)) = split_once_top(s, "**") {
        let base = parse_expr(base)?;
        let exp_e = parse_expr(exp)?;
        return match base {
            
            
            
            
            Expr::Gen => match const_int_expr(&exp_e) {
                Some(k) => Ok(Expr::GPow(k)),
                None => Ok(Expr::GenPow(Box::new(exp_e))),
            },
            
            _ => Ok(Expr::Pow(Box::new(base), Box::new(exp_e))),
        };
    }
    
    if s.starts_with('(') && s.ends_with(')') {
        return parse_expr(&s[1..s.len() - 1]);
    }
    if s == "GEN" {
        return Ok(Expr::Gen);
    }
    if let Ok(n) = s.parse::<u128>() {
        return Ok(Expr::Lit(n));
    }
    
    
    if s.starts_with('[') && s.ends_with(']') {
        let inner = s[1..s.len() - 1].trim();
        if inner.is_empty() {
            return Err("a list literal needs at least one element".into());
        }
        if let Some((body, range)) = split_once_top(inner, " for ") {
            let bad = || format!("a list comprehension is `[body for var in unroll(lo, hi)]`, got `{s}`");
            let (var, range) = range.split_once(" in ").ok_or_else(bad)?;
            let args = range
                .trim()
                .strip_prefix("unroll(")
                .and_then(|r| r.strip_suffix(')'))
                .ok_or_else(bad)?;
            let [lo, hi] = split_top(args, ',')[..] else {
                return Err(bad());
            };
            if !is_ident(var.trim()) {
                return Err(bad());
            }
            return Ok(Expr::ListComp(
                Box::new(parse_expr(body)?),
                var.trim().to_string(),
                Box::new(parse_expr(lo)?),
                Box::new(parse_expr(hi)?),
            ));
        }
        return Ok(Expr::ListLit(
            split_top(inner, ',')
                .iter()
                .map(|e| parse_expr(e))
                .collect::<Result<_, _>>()?,
        ));
    }
    
    if s.ends_with(']') {
        let open = s.find('[').ok_or_else(|| format!("unbalanced `]` in `{s}`"))?;
        let base = parse_expr(&s[..open])?;
        let inner = &s[open + 1..s.len() - 1];
        if let Some((lo, hi)) = split_once_top(inner, ":") {
            return Ok(Expr::Slice(
                Box::new(base),
                Box::new(parse_expr(lo)?),
                Box::new(parse_expr(hi)?),
            ));
        }
        let idx = parse_expr(inner)?;
        return Ok(Expr::Index(Box::new(base), Box::new(idx)));
    }
    if let Some(open) = s.find('(')
        && s.ends_with(')')
    {
        let name = s[..open].trim().to_string();
        let args_str = s[open + 1..s.len() - 1].trim();
        let mut args = if args_str.is_empty() {
            vec![]
        } else {
            split_top(args_str, ',')
                .iter()
                .map(|a| {
                    if let Some((key, value)) = split_once_top(a, "=") {
                        let key = key.trim();
                        if key.is_empty() || !key.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
                            return Err(format!("invalid keyword argument `{key}`"));
                        }
                        Ok(Expr::Call(format!("__kw_{key}"), vec![parse_expr(value)?]))
                    } else {
                        parse_expr(a)
                    }
                })
                .collect::<Result<_, _>>()?
        };
        
        
        
        
        
        let cells = |n: u128| u32::try_from(n).map_err(|_| format!("{name} size {n} does not fit in u32"));
        if name == "HeapBuf" || name == "StackBuf" {
            let size = match args.as_slice() {
                [arg] => const_int_expr(arg),
                _ => None,
            };
            return match (name.as_str(), size) {
                ("HeapBuf", Some(n)) => Ok(Expr::HeapBuf(cells(n)?)),
                ("StackBuf", Some(n)) => Ok(Expr::StackBuf(cells(n)?)),
                ("HeapBuf", None) if args.len() == 1 => Ok(Expr::HeapBufDyn(Box::new(args.pop().unwrap()))),
                ("HeapBuf", None) => Err("HeapBuf(size) takes one argument".into()),
                _ => Err("StackBuf(n) needs a parse-time integer size".into()),
            };
        }
        return Ok(Expr::Call(name, args));
    }
    if s.chars().all(|c| c.is_alphanumeric() || c == '_') && !s.is_empty() {
        return Ok(Expr::Var(s.to_string()));
    }
    if s.is_empty() {
        return Err("expected an expression".into());
    }
    Err(format!("cannot parse expression `{s}`"))
}



fn fold_ops(segs: &[&str], ops: &[u8], node: impl Fn(u8, Box<Expr>, Box<Expr>) -> Expr) -> Result<Expr, String> {
    
    
    
    if let Some(i) = segs.iter().position(|seg| seg.trim().is_empty()) {
        let (op, side) = if i == 0 {
            (ops[0], "left")
        } else {
            (ops[i - 1], "right")
        };
        
        let shown = match op {
            b'/' => "//".to_string(),
            b'd' => "/".to_string(),
            c => (c as char).to_string(),
        };
        let hint = if op == b'-' && i == 0 {
            ": there is no unary minus, and field subtraction is `+`"
        } else {
            ""
        };
        return Err(format!("`{shown}` has no {side} operand{hint}"));
    }
    let mut acc = parse_expr(segs[0])?;
    for (&op, seg) in ops.iter().zip(&segs[1..]) {
        let rhs = Box::new(parse_expr(seg)?);
        acc = node(op, Box::new(acc), rhs);
    }
    Ok(acc)
}




pub(super) fn depth0(s: &str) -> impl Iterator<Item = (usize, u8)> + '_ {
    let mut depth = 0i32;
    let mut in_str = false;
    s.as_bytes().iter().enumerate().filter_map(move |(i, &c)| {
        
        
        
        if in_str {
            in_str = c != b'"';
            return None;
        }
        match c {
            b'"' => {
                in_str = true;
                None
            }
            b'(' | b'[' => {
                depth += 1;
                None
            }
            b')' | b']' => {
                depth -= 1;
                None
            }
            _ => (depth == 0).then_some((i, c)),
        }
    })
}




fn split_add(s: &str) -> (Vec<&str>, Vec<u8>) {
    let (mut segs, mut ops) = (Vec::new(), Vec::new());
    let mut start = 0usize;
    for (i, c) in depth0(s) {
        if c == b'+' || c == b'-' {
            segs.push(&s[start..i]);
            ops.push(c);
            start = i + 1;
        }
    }
    segs.push(&s[start..]);
    (segs, ops)
}





fn split_mul(s: &str) -> (Vec<&str>, Vec<u8>) {
    let b = s.as_bytes();
    let (mut segs, mut ops) = (Vec::new(), Vec::new());
    let (mut start, mut next) = (0usize, 0usize);
    for (i, c) in depth0(s) {
        if i < next {
            continue; 
        }
        let (op, len) = match c {
            b'*' if b.get(i + 1) == Some(&b'*') || (i > 0 && b[i - 1] == b'*') => continue, 
            b'*' => (b'*', 1),
            b'/' if b.get(i + 1) == Some(&b'/') => (b'/', 2), 
            b'/' => (b'd', 1),                                
            b'%' => (b'%', 1),
            _ => continue,
        };
        segs.push(&s[start..i]);
        ops.push(op);
        next = i + len;
        start = next;
    }
    segs.push(&s[start..]);
    (segs, ops)
}


pub(super) fn split_once_top<'a>(s: &'a str, op: &str) -> Option<(&'a str, &'a str)> {
    let b = s.as_bytes();
    for (i, _) in depth0(s) {
        if b[i..].starts_with(op.as_bytes()) {
            return Some((&s[..i], &s[i + op.len()..]));
        }
    }
    None
}


pub(super) fn split_top(s: &str, sep: char) -> Vec<&str> {
    let sep = sep as u8;
    let mut parts = Vec::new();
    let mut start = 0;
    for (i, c) in depth0(s) {
        if c == sep {
            parts.push(&s[start..i]);
            start = i + 1;
        }
    }
    parts.push(&s[start..]);
    parts
}






pub(super) fn split_assign(s: &str) -> Option<(&str, &str)> {
    let b = s.as_bytes();
    for (i, c) in depth0(s) {
        if c != b'=' || b.get(i + 1) == Some(&b'=') {
            continue;
        }
        if i > 0 && matches!(b[i - 1], b'=' | b'<' | b'>' | b'!' | b'+' | b'-' | b'*' | b'/' | b'%') {
            continue;
        }
        return Some((&s[..i], &s[i + 1..]));
    }
    None
}










pub(super) fn split_aug(s: &str) -> Result<Aug<'_>, String> {
    let b = s.as_bytes();
    for (i, c) in depth0(s) {
        if c != b'=' {
            continue;
        }
        
        
        if i == 0 {
            return Ok(None);
        }
        
        if b.get(i + 1) == Some(&b'=') || matches!(b[i - 1], b'=' | b'<' | b'>' | b'!') {
            return Ok(None);
        }
        let prev2 = b.get(i.wrapping_sub(2)).copied();
        let (op, plen): (&str, usize) = match b[i - 1] {
            b'+' => ("+", 1),
            b'-' => ("-", 1),
            b'%' => ("%", 1),
            b'*' if prev2 == Some(b'*') => {
                return Err("`**=` is not supported; write `x = x ** k`".into());
            }
            b'*' => ("*", 1),
            b'/' if prev2 == Some(b'/') => ("//", 2),
            b'/' => {
                return Err(
                    "`/=` is not supported; `/` is runtime field division, so write `x = x / y` (or `//=` for the \
                     compile-time floor division)"
                        .into(),
                );
            }
            _ => return Ok(None),
        };
        return Ok(Some((s[..i - plen].trim(), op, s[i + 1..].trim())));
    }
    Ok(None)
}




pub(super) fn call_args<'a>(line: &'a str, name: &str) -> Option<Vec<&'a str>> {
    let inner = line.trim().strip_prefix(name)?.strip_prefix('(')?.strip_suffix(')')?;
    Some(split_top(inner, ','))
}


pub(super) fn string_lit(s: &str) -> Option<&str> {
    s.trim().strip_prefix('"')?.strip_suffix('"')
}




pub(super) fn strip_comment(raw: &str) -> &str {
    let mut in_str = false;
    for (i, c) in raw.char_indices() {
        match c {
            '"' => in_str = !in_str,
            '#' if !in_str => return &raw[..i],
            _ => {}
        }
    }
    raw
}




pub(super) fn top_level_cmp(s: &str) -> Option<&'static str> {
    let b = s.as_bytes();
    for (i, c) in depth0(s) {
        let eq = b.get(i + 1) == Some(&b'=');
        match c {
            b'=' if eq => return Some("=="),
            b'!' if eq => return Some("!="),
            b'<' => return Some(if eq { "<=" } else { "<" }),
            b'>' => return Some(if eq { ">=" } else { ">" }),
            _ => {}
        }
    }
    None
}



pub(super) fn is_ident(s: &str) -> bool {
    let mut cs = s.chars();
    matches!(cs.next(), Some(c) if c.is_alphabetic() || c == '_') && s.chars().all(|c| c.is_alphanumeric() || c == '_')
}






pub(super) fn binding_name(raw: &str, what: &str) -> Result<String, String> {
    let n = raw.trim();
    if is_ident(n) {
        return Ok(n.to_string());
    }
    Err(format!(
        "`{n}` is not a valid {what}: a name must be a plain identifier. A top-level constant's name is \
         reserved, and is substituted before parsing, so a parameter or local may not reuse one."
    ))
}





pub(super) fn strip_const_wrapper(s: &str) -> Option<&str> {
    let inner = s.trim().strip_prefix("const(")?.strip_suffix(')')?;
    let mut depth = 0i32;
    for c in inner.bytes() {
        match c {
            b'(' | b'[' => depth += 1,
            b')' | b']' => {
                depth -= 1;
                if depth < 0 {
                    return None;
                }
            }
            _ => {}
        }
    }
    Some(inner)
}
