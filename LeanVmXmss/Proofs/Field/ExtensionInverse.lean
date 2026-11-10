import Proofs.Field.Inverse

namespace LeanVmXmss.Proofs.Field

open Spec.Field (K E squareNWith powWith)
open Model.Field

set_option maxRecDepth 20000
set_option maxHeartbeats 200000

theorem epow_add (a : E) (n k : Nat) : epow a (n + k) = karatsubaMul (epow a n) (epow a k) :=
  powWith_add karatsubaMul Spec.Field.one a emul_assoc
    (fun a => (emul_comm a Spec.Field.one).trans (emul_one_left a)) n k

theorem epow_mul (a : E) (n k : Nat) : epow (epow a n) k = epow a (n * k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change karatsubaMul (epow (epow a n) k) (epow a n) = _
    rw [ih, ← epow_add, Nat.mul_succ]

theorem emul_zero_left (a : E) : karatsubaMul Spec.Field.zero a = Spec.Field.zero := by
  simp [karatsuba_refines_polynomial, polynomialMul, Spec.Field.zero, mul_zero_left]

theorem emul_zero_right (a : E) : karatsubaMul a Spec.Field.zero = Spec.Field.zero :=
  (emul_comm _ _).trans (emul_zero_left a)

theorem epow_zero (n : Nat) (h : n ≠ 0) : epow Spec.Field.zero n = Spec.Field.zero := by
  cases n with
  | zero => contradiction
  | succ n => exact emul_zero_right _

theorem epow_order (a : E) : epow a (2^192) = a := by
  have hh := esquareN_pow a 1 192
  rw [epow_one, Nat.one_mul, show 192 = 64 + 64 + 64 from rfl, squareN_add, squareN_add,
    esquareN_frobenius, esquareN_frobenius, esquareN_frobenius, frobenius_order_three] at hh
  exact hh.symm

theorem norm_power (a : E) :
    Spec.Field.embed (norm a) = epow a (1 + 2^64 + 2^128) := by
  rw [← norm_in_base, frobenius_eq_pow, frobenius2_eq_pow, ← epow_add]
  conv => lhs; arg 1; rw [← epow_one a]
  rw [← epow_add]

theorem norm_nonzero (a : E) (h : a ≠ Spec.Field.zero) : norm a ≠ 0 := by
  intro hz
  have hp : epow a (1 + 2^64 + 2^128) = Spec.Field.zero := by
    rw [← norm_power, hz]
    rfl
  have hzpow : epow a (2^192 - 1) = Spec.Field.zero := by
    have hh := epow_mul a (1 + 2^64 + 2^128) (2^64 - 1)
    rw [hp, epow_zero _ (by decide)] at hh
    exact hh.symm
  have hfinal : a = Spec.Field.zero := by
    rw [← epow_order a]
    change epow a ((2^192 - 1) + 1) = _
    rw [epow_add, hzpow, emul_zero_left]
  exact h hfinal

theorem emul_mulBase (a b : E) (k : K) :
    karatsubaMul a (mulBase b k) = mulBase (karatsubaMul a b) k := by
  simp only [karatsuba_refines_polynomial, polynomialMul, mulBase, mul_xor_left, mul_assoc]

theorem emul_inv_nonzero (a : E) (h : a ≠ Spec.Field.zero) :
    karatsubaMul a (einv a) = Spec.Field.one := by
  rw [einv, emul_mulBase, norm_in_base]
  simp only [mulBase, Spec.Field.embed, mul_zero_left, mul_inv_nonzero _ (norm_nonzero a h)]
  rfl

end LeanVmXmss.Proofs.Field
