use std::io::{self, BufRead};
use verifier::VerifierError;
#[path = "../../../../../references/leanVM/crates/verifier/src/field.rs"]
mod field;
use field::{E, K, Scaled};

fn require(condition: bool, error: VerifierError) -> Result<(), VerifierError> {
    if condition { Ok(()) } else { Err(error) }
}

fn main() {
    for line in io::stdin().lock().lines() {
        let line = line.unwrap();
        let n: Vec<u64> = line.split_whitespace().map(|s| s.parse().unwrap()).collect();
        assert_eq!(n.len(), 7);
        let a = E::new(n[0], n[1], n[2]);
        let b = E::new(n[3], n[4], n[5]);
        let sum = a + b;
        let product = a * b;
        let mixed = a * K(n[6]);
        let square = a.square();
        let mut bytes = Vec::new();
        for c in [a.c0, a.c1, a.c2] { bytes.extend(c.to_le_bytes()); }
        assert_eq!(E::from_bytes(&bytes).unwrap(), a);
        let inverse = a.inv();
        let power = a.pow(n[6] % 17);
        let frob = E::new(a.c0, a.c2, a.c1 ^ a.c2);
        let scaled = Scaled::new(a).mul(b);
        let mut kpower = K(1);
        for _ in 0..n[6] % 17 { kpower = kpower * K(n[0]); }
        let values = [(K(n[0]) + K(n[3])).0, (K(n[0]) * K(n[3])).0, K(n[0]).square().0,
            sum.c0, sum.c1, sum.c2, product.c0, product.c1, product.c2,
            mixed.c0, mixed.c1, mixed.c2, square.c0, square.c1, square.c2,
            K(n[0]).inv().0, inverse.c0, inverse.c1, inverse.c2,
            power.c0, power.c1, power.c2, frob.c0, frob.c1, frob.c2,
            scaled.c0, scaled.c1, scaled.c2, kpower.0];
        let hex = |data: &[u8]| data.iter().map(|b| format!("{b:02x}")).collect::<String>();
        println!("{} {} {}", values.map(|x| x.to_string()).join(" "), hex(&K(n[0]).to_bytes()), hex(&bytes));
    }
}
