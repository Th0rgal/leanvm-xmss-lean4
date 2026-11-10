import Proofs.Field.ExtensionInverse
import Proofs.Field.Codecs

namespace LeanVmXmss.Proofs.Field

open Spec.Field (K E remainderSteps remainder)
open Model.Field

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

theorem remainderSteps_small (n p : Nat) (hp : p < 2^64) :
    remainderSteps 64 Spec.Field.modulus n p = p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hb : p.testBit (64 + n) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hp (Nat.pow_le_pow_right (by decide) (by omega)))
    simp only [remainderSteps.succ, hb, Bool.false_eq_true, ↓reduceIte, ih]

def windowWord (a : K) (n : Nat) : K :=
  UInt64.ofNat (((a.toNat >>> (6*n)) % 64) <<< (6*n))

theorem windowWord_bound (a : K) (n : Nat) :
    ((a.toNat >>> (6*n)) % 64) <<< (6*n) < 2^64 := by
  have h : ((a.toNat >>> (6*n)) % 64) ≤ a.toNat >>> (6*n) := Nat.mod_le _ _
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow] at *
  have hm := Nat.mul_le_mul_right (2^(6*n)) h
  exact Nat.lt_of_le_of_lt (Nat.le_trans hm (Nat.div_mul_le_self _ _)) a.toNat_lt

theorem windowElement_word (a : K) (l : Fin 3) (w : Fin 11) :
    Spec.Field.windowElement l w ⟨(a.toNat >>> (6*w.val)) % 64, Nat.mod_lt _ (by decide)⟩ =
      if l.val = 0 then ⟨windowWord a w.val, 0, 0⟩ else
      if l.val = 1 then ⟨0, windowWord a w.val, 0⟩ else ⟨0, 0, windowWord a w.val⟩ := by
  simp only [Spec.Field.windowElement, remainder, remainderSteps_small _ _ (windowWord_bound a w.val), windowWord]

def windowSum (a : K) : Nat → K :=
  Nat.rec 0 (fun n prev => prev ^^^ windowWord a n)

@[simp] theorem windowSum.zero (a : K) : windowSum a 0 = 0 := rfl

@[simp] theorem windowSum.succ (a : K) (n : Nat) :
    windowSum a (n + 1) = windowSum a n ^^^ windowWord a n := rfl

theorem windowSum_bit (a : K) (n i : Nat) (_hi : i < 64) :
    (windowSum a n).toBitVec.getLsbD i =
      if i < 6*n then a.toBitVec.getLsbD i else false := by
  induction n with
  | zero => simp [windowSum.zero]
  | succ n ih =>
    simp only [windowSum.succ, UInt64.toBitVec_xor, BitVec.getLsbD_xor, ih]
    have hw : (windowWord a n).toBitVec.getLsbD i =
        if 6*n ≤ i ∧ i < 6*n+6 then a.toBitVec.getLsbD i else false := by
      change (((a.toNat >>> (6*n)) % 64) <<< (6*n) % 2^64).testBit i =
        if 6*n ≤ i ∧ i < 6*n+6 then a.toNat.testBit i else false
      rw [Nat.mod_eq_of_lt (windowWord_bound a n)]
      simp only [Nat.testBit_shiftLeft]
      by_cases h : 6*n ≤ i
      · change (decide (6*n ≤ i) && ((a.toNat >>> (6*n)) % 2^6).testBit (i-6*n)) = _
        simp only [h, decide_true, Bool.true_and, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
        by_cases hj : i < 6*n+6
        · simp [hj, show i - 6*n < 6 by omega, show 6*n + (i - 6*n) = i by omega]
        · simp [hj, show ¬ i - 6*n < 6 by omega]
      · simp [h]
    rw [hw]
    by_cases h : i < 6*n
    · simp [h, show i < 6*(n+1) by omega, show ¬6*n ≤ i by omega]
    · by_cases hj : i < 6*(n+1)
      · simp [h, hj, show 6*n ≤ i by omega, show i < 6*n+6 by omega]
      · simp [h, hj, show ¬ i < 6*n+6 by omega]

theorem windowSum_full (a : K) : windowSum a 11 = a := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [windowSum_bit a 11 i hi]
  simp [show i < 6*11 by omega]

def limbEmbed (l : Fin 3) (a : K) : E :=
  if l.val = 0 then ⟨a, 0, 0⟩ else if l.val = 1 then ⟨0, a, 0⟩ else ⟨0, 0, a⟩

theorem limbEmbed_add (l : Fin 3) (a b : K) :
    limbEmbed l (a ^^^ b) = eadd (limbEmbed l a) (limbEmbed l b) := by
  unfold limbEmbed
  split <;> (try split) <;> simp [eadd]

theorem eadd_assoc (a b c : E) : eadd (eadd a b) c = eadd a (eadd b c) := by
  simp only [eadd, kxor_assoc]

theorem eadd_zero_right (a : E) : eadd a Spec.Field.zero = a := by
  cases a
  simp [eadd, Spec.Field.zero]

theorem scaledLimb_correct (r : E) (l : Fin 3) (a : K) (acc : E) (n : Nat) (hn : n ≤ 11) :
    scaledLimb (scaled r) l a acc n = eadd acc (karatsubaMul r (limbEmbed l (windowSum a n))) := by
  induction n with
  | zero =>
    have hz : limbEmbed l 0 = Spec.Field.zero := by simp [limbEmbed, Spec.Field.zero]
    simp only [scaledLimb.zero, windowSum.zero, hz, emul_zero_right, eadd_zero_right]
  | succ n ih =>
    rw [scaledLimb.succ, dite_eq_left (by omega), ih (by omega)]
    have hw := windowElement_word a l ⟨n, by omega⟩
    change Spec.Field.windowElement l ⟨n, by omega⟩ _ = limbEmbed l (windowWord a n) at hw
    simp only [scaled, hw, windowSum.succ, limbEmbed_add, emul_add_right, eadd_assoc]

theorem scaledMul_correct (a b : E) : scaledMul (scaled a) b = karatsubaMul a b := by
  simp only [scaledMul, scaledLimb_correct _ _ _ _ 11 (by decide), windowSum_full]
  rw [eadd_assoc, eadd_assoc, ← emul_add_right, ← emul_add_right]
  have he : eadd (limbEmbed 0 b.c0) (eadd (limbEmbed 1 b.c1) (limbEmbed 2 b.c2)) = b := by
    cases b
    simp [limbEmbed, eadd]
  rw [he]
  cases h : karatsubaMul a b
  simp [eadd, Spec.Field.zero]

end LeanVmXmss.Proofs.Field
