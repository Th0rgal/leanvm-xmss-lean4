import Proofs.Field.Basic

namespace LeanVmXmss.Proofs.Field

open Spec.Field (K bit parity pack productCoeff polynomialProduct)
open Model.Field

theorem pack_bit (f : Nat → Bool) (n i : Nat) (hi : i < n) :
    (pack n f).getLsbD i = f i := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [pack.succ, BitVec.getLsbD_cons]
    by_cases h : i = n
    · simp [h]
    · simp [h, ih (by omega)]

theorem select_bit (p : Bool) (a : BitVec w) (i : Nat) :
    (if p then a else 0).getLsbD i = (p && a.getLsbD i) := by
  cases p <;> simp

theorem clmulSteps_bit (a b : BitVec 64) (n k : Nat) (hk : k < 128) :
    (clmulSteps a b n).getLsbD k =
      parity n (fun i => if i ≤ k then a.getLsbD (k - i) && b.getLsbD i else false) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [clmulSteps.succ, parity.succ, BitVec.getLsbD_xor, ih]
    congr 1
    simp only [select_bit, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      hk, decide_true, Bool.true_and]
    by_cases h : n ≤ k
    · have hkn : k - n < 128 := by omega
      simp [h, hkn, show ¬ k < n by omega, Bool.and_comm]
    · simp [h, show k < n by omega]

theorem clmul_refines_convolution (a b : K) :
    clmul a b = pack 128 (productCoeff a b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [pack_bit _ _ _ hk]
  unfold clmul
  rw [clmulSteps_bit _ _ _ _ hk]
  rfl

theorem clmul_toNat (a b : K) : (clmul a b).toNat = polynomialProduct a b := by
  rw [clmul_refines_convolution]
  rfl

end LeanVmXmss.Proofs.Field
