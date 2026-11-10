














use super::*;









pub(super) fn eval_const_int(s: &str) -> Result<u128, String> {
    parse_expr(s)
        .ok()
        .and_then(|e| const_int_expr(&e))
        .ok_or_else(|| format!("not a compile-time integer constant expression: `{}`", s.trim()))
}





pub(super) fn const_int_expr(e: &Expr) -> Option<u128> {
    match e {
        Expr::Lit(k) => Some(*k),
        
        
        
        
        
        
        Expr::Call(f, args) if f == "const" && args.len() == 1 => const_int_expr(&args[0]),
        Expr::Add(a, b) => const_int_expr(a)?.checked_add(const_int_expr(b)?),
        Expr::Sub(a, b) => const_int_expr(a)?.checked_sub(const_int_expr(b)?),
        Expr::Mul(a, b) => const_int_expr(a)?.checked_mul(const_int_expr(b)?),
        
        
        Expr::Div(a, b) | Expr::FieldDiv(a, b) => match const_int_expr(b)? {
            0 => None,
            d => Some(const_int_expr(a)? / d),
        },
        Expr::Mod(a, b) => match const_int_expr(b)? {
            0 => None,
            d => Some(const_int_expr(a)? % d),
        },
        Expr::Pow(a, b) => const_int_expr(a)?.checked_pow(u32::try_from(const_int_expr(b)?).ok()?),
        _ => None,
    }
}



pub(super) fn is_int_arith(e: &Expr) -> bool {
    match e {
        Expr::Lit(_) => true,
        Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::FieldDiv(a, b)
        | Expr::Mod(a, b)
        | Expr::Pow(a, b) => is_int_arith(a) && is_int_arith(b),
        Expr::Call(f, args) if f == "const" && args.len() == 1 => is_int_arith(&args[0]),
        _ => false,
    }
}





pub fn parse_const(s: &str) -> Result<F192, String> {
    fn eval(e: &Expr) -> Result<F192, String> {
        match e {
            
            Expr::Lit(n) => Ok(F192::new(*n as u64, (*n >> 64) as u64, 0)),
            Expr::Gen => Ok(g_pow(1).into()),
            Expr::GPow(k) => Ok(g_pow_u128(*k).into()),
            Expr::Add(a, b) => Ok(eval(a)? + eval(b)?),
            Expr::Mul(a, b) => Ok(eval(a)? * eval(b)?),
            other => Err(format!("not a constant expression: `{other:?}`")),
        }
    }
    eval(&parse_expr(s)?)
}

pub(super) fn parse_f192_const(s: &str) -> Option<Result<F192, String>> {
    let inner = s.trim().strip_prefix("f192(")?.strip_suffix(')')?;
    let parts = split_top(inner, ',');
    Some((|| {
        if parts.len() != 3 {
            return Err("f192 needs exactly three limbs".into());
        }
        let mut limbs = [0u64; 3];
        for (i, p) in parts.iter().enumerate() {
            limbs[i] =
                u64::try_from(eval_const_int(p.trim())?).map_err(|_| "an f192 limb does not fit in u64".to_string())?;
        }
        Ok(F192::new(limbs[0], limbs[1], limbs[2]))
    })())
}






pub(super) fn gpow_bound(e: &Expr) -> Result<u64, String> {
    match e {
        
        
        
        
        
        Expr::Lit(n) if (n.is_power_of_two() && *n < (1 << 64)) || *n == 1 => Ok(n.trailing_zeros() as u64),
        Expr::Gen => Ok(1),
        Expr::GPow(k) => u64::try_from(*k).map_err(|_| format!("bound exponent {k} does not fit in u64")),
        other => Err(format!(
            "a range bound must be a power of GEN (`1`, `GEN`, or `GEN ** k`), got `{other:?}`"
        )),
    }
}

pub(super) fn parse_gpow_bound(s: &str) -> Result<u64, String> {
    gpow_bound(&parse_expr(s)?)
}







pub(super) fn apply_replacements(src: &str, replacements: &BTreeMap<String, String>) -> String {
    if replacements.is_empty() {
        return src.to_string();
    }
    let mut out = String::with_capacity(src.len());
    let mut start = 0;
    let mut in_str = false;
    let flush = |out: &mut String, word: &str, in_str: bool| {
        out.push_str(if in_str {
            word
        } else {
            replacements.get(word).map_or(word, String::as_str)
        });
    };
    for (i, c) in src.char_indices() {
        if !(c.is_alphanumeric() || c == '_') {
            flush(&mut out, &src[start..i], in_str);
            out.push(c);
            start = i + c.len_utf8();
            
            
            in_str = match c {
                '"' => !in_str,
                '\n' => false,
                _ => in_str,
            };
        }
    }
    flush(&mut out, &src[start..], in_str);
    out
}
