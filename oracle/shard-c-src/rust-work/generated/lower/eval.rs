









use super::*;



#[derive(Clone, Copy, Default)]
pub(super) struct Known {
    
    pub(super) int: Option<u128>,
    
    pub(super) field: Option<F192>,
    
    pub(super) addr: Option<GAddr>,
}

impl Known {
    
    pub(super) fn diverging_readings(self) -> Option<(u128, F192)> {
        let (n, f) = (self.int?, self.field?);
        (f != lit_field(n)).then_some((n, f))
    }
}



fn gmul(a: GAddr, b: GAddr) -> Option<GAddr> {
    let base = match (a.base, b.base) {
        (None, x) | (x, None) => x,
        (Some(_), Some(_)) => return None,
    };
    Some(GAddr {
        base,
        exp: a.exp.checked_add(b.exp)?,
        
        
        run: a.run.or(b.run),
    })
}


pub(super) fn field_pow(b: F192, mut k: u32) -> F192 {
    let (mut acc, mut sq) = (F192::ONE, b);
    while k > 0 {
        if k & 1 == 1 {
            acc *= sq;
        }
        k >>= 1;
        if k > 0 {
            sq *= sq;
        }
    }
    acc
}

impl FnLower<'_> {
    
    
    
    
    
    
    
    
    
    
    pub(super) fn eval(&self, e: &Expr) -> Known {
        
        
        
        
        
        
        
        let int = |n: u128| Known {
            int: Some(n),
            field: Some(lit_field(n)),
            addr: None,
        };
        let gpow = |exp: u128| Known {
            int: None,
            field: Some(g_pow_u128(exp).into()),
            addr: Some(GAddr {
                base: None,
                exp,
                run: None,
            }),
        };
        match e {
            
            
            
            
            
            Expr::Lit(n) => Known {
                addr: (n.is_power_of_two() && *n < (1 << 64)).then(|| GAddr {
                    base: None,
                    exp: n.trailing_zeros() as u128,
                    run: None,
                }),
                ..int(*n)
            },
            Expr::Gen => gpow(1),
            Expr::GPow(k) => gpow(*k),
            Expr::GenPow(x) => match self.eval(x).int.and_then(|n| u32::try_from(n).ok()) {
                Some(k) => gpow(u128::from(k)),
                None => Known::default(),
            },
            Expr::Var(v) => {
                let Some(b) = self.scope.bound(v) else {
                    return Known::default();
                };
                let int = b.int;
                match b.val {
                    Binding::FConst(c) => Known {
                        int,
                        field: Some(c),
                        addr: None,
                    },
                    Binding::Gaddr(ga) => Known {
                        int,
                        
                        field: (ga.base.is_none()).then(|| g_pow_u128(ga.exp).into()),
                        addr: Some(ga),
                    },
                    
                    Binding::Scalar(c) => Known {
                        int,
                        field: None,
                        addr: Some(GAddr {
                            base: Some(c),
                            exp: 0,
                            run: None,
                        }),
                    },
                    Binding::Stack(..) => Known {
                        int,
                        ..Known::default()
                    },
                }
            }
            
            
            
            
            
            Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Mul(a, b) | Expr::Div(a, b) | Expr::Mod(a, b) => {
                let (x, y) = (self.eval(a), self.eval(b));
                if matches!(e, Expr::Div(..) | Expr::Mod(..)) && y.int == Some(0) {
                    self.fail(match e {
                        Expr::Div(..) => "compile-time division by zero",
                        _ => "compile-time modulo by zero",
                    })
                };
                let int = || {
                    let (n, m) = (x.int?, y.int?);
                    match e {
                        Expr::Add(..) => n.checked_add(m),
                        Expr::Sub(..) => n.checked_sub(m),
                        Expr::Mul(..) => n.checked_mul(m),
                        Expr::Div(..) => Some(n / m),
                        _ => Some(n % m),
                    }
                };
                Known {
                    int: int(),
                    field: match e {
                        Expr::Add(..) => x.field.and_then(|f| Some(f + y.field?)),
                        Expr::Mul(..) => x.field.and_then(|f| Some(f * y.field?)),
                        _ => None,
                    },
                    addr: match e {
                        Expr::Mul(..) => x.addr.and_then(|p| gmul(p, y.addr?)),
                        _ => None,
                    },
                }
            }
            Expr::Pow(b, x) => {
                let (base, exp) = (self.eval(b), self.eval(x).int.and_then(|n| u32::try_from(n).ok()));
                Known {
                    int: base.int.and_then(|n| n.checked_pow(exp?)),
                    field: base.field.and_then(|f| Some(field_pow(f, exp?))),
                    addr: None,
                }
            }
            
            
            Expr::Index(..) => match self.const_array_elem(e) {
                Some(v) => Known {
                    int: (v.c2 == 0).then_some(v.c0 as u128 | ((v.c1 as u128) << 64)),
                    field: Some(v),
                    addr: None,
                },
                None => Known::default(),
            },
            Expr::Call(f, args) if f == "f192" && args.len() == 3 => {
                let limb = |i: usize| match &args[i] {
                    Expr::Lit(n) => u64::try_from(*n).ok(),
                    _ => None,
                };
                Known {
                    field: (|| Some(F192::new(limb(0)?, limb(1)?, limb(2)?)))(),
                    ..Known::default()
                }
            }
            
            
            
            Expr::Call(f, args) if f == "const" && args.len() == 1 => {
                self.check_const_leaves(&args[0]);
                match self.eval(&args[0]).int {
                    Some(n) => int(n),
                    None => Known::default(),
                }
            }
            Expr::Call(..) => match self.const_len(e) {
                Some(n) => int(n as u128),
                None => Known::default(),
            },
            _ => Known::default(),
        }
    }

    
    
    pub(super) fn try_const_int(&self, e: &Expr) -> Option<u128> {
        self.eval(e).int
    }

    
    pub(super) fn gaddr_of(&self, e: &Expr) -> Option<GAddr> {
        self.eval(e).addr
    }

    
    
    
    pub(super) fn try_field_const(&self, e: &Expr) -> Option<F192> {
        self.eval(e).field
    }

    
    
    pub(super) fn try_const_index(&self, idx: &Expr) -> Option<u32> {
        u32::try_from(self.try_const_int(idx)?).ok()
    }

    
    
    pub(super) fn const_index(&self, idx: &Expr) -> u32 {
        let k = self.try_const_int(idx).unwrap_or_else(|| {
            self.fail(format!(
                "a StackBuf index must be a compile-time integer, got `{idx:?}`"
            ))
        });
        u32::try_from(k).unwrap_or_else(|_| self.fail(format!("stack index {k} does not fit in u32")))
    }

    
    pub(super) fn gpow_exp(&self, e: &Expr) -> u128 {
        self.try_const_index(e)
            .unwrap_or_else(|| self.fail(format!("`GEN ** e` needs a compile-time integer exponent, got `{e:?}`")))
            as u128
    }

    
    
    fn const_array_elem(&self, e: &Expr) -> Option<F192> {
        if let Expr::Index(arr, idx) = e
            && let Expr::Var(v) = arr.as_ref()
            && let Some(a) = self.const_arrays.get(v.as_str())
        {
            let i = self.try_const_index(idx)? as usize;
            return Some(
                *a.get(i).unwrap_or_else(|| {
                    self.fail(format!("const array `{v}` index {i} out of bounds (len {})", a.len()))
                }),
            );
        }
        None
    }

    
    fn const_len(&self, e: &Expr) -> Option<usize> {
        if let Expr::Call(f, args) = e
            && f == "len"
            && args.len() == 1
            && let Expr::Var(v) = &args[0]
        {
            return self.const_arrays.get(v.as_str()).map(|a| a.len());
        }
        None
    }

    
    
    
    
    pub(super) fn add_identity<'e>(&self, a: &'e Expr, b: &'e Expr) -> Option<&'e Expr> {
        if self.try_field_const(a) == Some(F192::ZERO) {
            return Some(b);
        }
        (self.try_field_const(b) == Some(F192::ZERO)).then_some(a)
    }

    
    
    
    pub(super) fn mul_identity<'e>(&self, a: &'e Expr, b: &'e Expr) -> Option<&'e Expr> {
        if self.try_field_const(a) == Some(F192::ONE) {
            return Some(b);
        }
        (self.try_field_const(b) == Some(F192::ONE)).then_some(a)
    }

    
    
    
    pub(super) fn try_lit(&self, e: &Expr) -> Option<u64> {
        match e {
            Expr::Lit(n) => u64::try_from(*n).ok(),
            Expr::Var(v) => self.scope.int(v).and_then(|n| u64::try_from(n).ok()),
            Expr::GPow(0) => Some(1),
            _ => None,
        }
    }

    
    
    
    
    
    
    
    
    
    
    
    fn check_const_leaves(&self, e: &Expr) {
        match e {
            Expr::Add(a, b)
            | Expr::Sub(a, b)
            | Expr::Mul(a, b)
            | Expr::Div(a, b)
            | Expr::Mod(a, b)
            | Expr::Pow(a, b) => {
                self.check_const_leaves(a);
                self.check_const_leaves(b);
            }
            Expr::Call(f, args) if f == "const" && args.len() == 1 => self.check_const_leaves(&args[0]),
            leaf => {
                if let Some((n, f)) = self.eval(leaf).diverging_readings() {
                    self.fail(format!(
                        "const(...) reads its operators as integer arithmetic, but it cannot reinterpret \
                         `{leaf:?}`, which is the integer {n} and the value {:#x}:{:#x}: two different \
                         numbers. Bind it in one regime and name that one",
                        f.c1, f.c0
                    ))
                }
            }
        }
    }

    
    
    
    
    
    
    pub(super) fn const_gpow(&self, e: &Expr) -> Option<u32> {
        let k = self.eval(e);
        if let Some(GAddr { base: None, exp, .. }) = k.addr
            && exp <= FOLD_MAX
        {
            return Some(exp as u32);
        }
        
        
        
        let n = k.int?;
        if !n.is_power_of_two() || n >= (1 << 64) {
            return None;
        }
        let j = n.trailing_zeros();
        (u128::from(j) <= FOLD_MAX && k.field? == g_pow_u128(u128::from(j)).into()).then_some(j)
    }
}
