import Proofs.Field.Powers

namespace LeanVmXmss.Proofs.Field

open Spec.Field (K E squareNWith)
open Model.Field

set_option maxRecDepth 20000
set_option maxHeartbeats 200000

theorem esquare_add (a b : E) : esquare (eadd a b) = eadd (esquare a) (esquare b) := by
  simp only [esquare, eadd, square_xor]
  congr 1 <;> simp only [kxor_assoc, kxor_comm, kxor_left_comm]

theorem esquare_zero : esquare Spec.Field.zero = Spec.Field.zero := by decide

theorem esquareN_add (a b : E) (n : Nat) :
    squareNWith esquare (eadd a b) n = eadd (squareNWith esquare a n) (squareNWith esquare b n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [squareNWith.succ, ih, esquare_add]

theorem esquareN_zero (n : Nat) : squareNWith esquare Spec.Field.zero n = Spec.Field.zero := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [squareNWith.succ, ih, esquare_zero]

theorem esquareN_mulBase (a : E) (b : K) (n : Nat) :
    squareNWith esquare (mulBase a b) n = mulBase (squareNWith esquare a n) (squareNWith square b n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change esquare (squareNWith esquare (mulBase a b) n) =
      mulBase (esquare (squareNWith esquare a n)) (square (squareNWith square b n))
    rw [ih]
    simp only [esquare, mulBase, square_mul, mul_xor_left]

theorem esquareN_one (n : Nat) : squareNWith esquare Spec.Field.one n = Spec.Field.one := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [squareNWith.succ, ih]; decide

set_option maxRecDepth 100000 in
theorem esquareN_y64 : squareNWith esquare Spec.Field.y 64 = frobenius Spec.Field.y := by decide

set_option maxRecDepth 100000 in
theorem esquareN_y264 : squareNWith esquare (esquare Spec.Field.y) 64 = frobenius (esquare Spec.Field.y) := by decide

theorem extension_decompose (a : E) :
    a = eadd (mulBase Spec.Field.one a.c0)
      (eadd (mulBase Spec.Field.y a.c1) (mulBase (esquare Spec.Field.y) a.c2)) := by
  cases a
  simp [mulBase, Spec.Field.one, Spec.Field.embed, Spec.Field.y, esquare, square_zero,
    show square 1 = 1 from by decide, mul_zero_left, mul_one_left, eadd]

theorem frobenius_add (a b : E) : frobenius (eadd a b) = eadd (frobenius a) (frobenius b) := by
  simp only [frobenius, eadd]
  congr 1 <;> simp only [kxor_assoc, kxor_comm, kxor_left_comm]

theorem frobenius_mulBase (a : E) (b : K) : frobenius (mulBase a b) = mulBase (frobenius a) b := by
  simp only [frobenius, mulBase, mul_xor_left]

theorem esquareN_frobenius (a : E) : squareNWith esquare a 64 = frobenius a := by
  conv => lhs; rw [extension_decompose a]
  simp only [esquareN_add, esquareN_mulBase, squareN_order, esquareN_one, esquareN_y64, esquareN_y264]
  conv => rhs; rw [extension_decompose a]
  simp only [frobenius_add, frobenius_mulBase]
  rfl

theorem epow_one (a : E) : epow a 1 = a := emul_one_left a

theorem esquareN_pow (a : E) (n k : Nat) : squareNWith esquare (epow a n) k = epow a (n * 2^k) :=
  squareN_pow karatsubaMul Spec.Field.one a esquare emul_assoc
    (fun a => (emul_comm a Spec.Field.one).trans (emul_one_left a))
    (fun a => (esquare_refines_polynomial a).trans (karatsuba_refines_polynomial a a).symm) n k

theorem frobenius_eq_pow (a : E) : frobenius a = epow a (2^64) := by
  have h := esquareN_pow a 1 64
  simpa only [epow_one, Nat.one_mul, esquareN_frobenius] using h

theorem squareN_add {α : Type} (sq : α → α) (a : α) (n k : Nat) :
    squareNWith sq a (n + k) = squareNWith sq (squareNWith sq a n) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change sq (squareNWith sq a (n + k)) = sq (squareNWith sq (squareNWith sq a n) k)
    rw [ih]

theorem frobenius2_eq_pow (a : E) : frobenius2 a = epow a (2^128) := by
  have h := esquareN_pow a 1 128
  rw [epow_one, Nat.one_mul, show 128 = 64 + 64 from rfl, squareN_add,
    esquareN_frobenius, esquareN_frobenius] at h
  exact h

end LeanVmXmss.Proofs.Field
