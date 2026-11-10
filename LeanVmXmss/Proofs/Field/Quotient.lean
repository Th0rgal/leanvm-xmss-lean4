import Proofs.Field.Reduction
import Spec.Field.Quotient

namespace LeanVmXmss.Proofs.Field

open Spec.Field

set_option maxRecDepth 20000

theorem polynomialMultiple_append (m : Nat) (xs ys : List Nat) :
    polynomialMultiple m (xs ++ ys) = polynomialMultiple m xs ^^^ polynomialMultiple m ys := by
  induction xs with
  | nil => simp [polynomialMultiple]
  | cons i xs ih => simp only [List.cons_append, polynomialMultiple.cons, ih, Nat.xor_assoc]

theorem polynomialCongruent_refl (m a : Nat) : PolynomialCongruent m a a := by
  exact ⟨[], by simp [polynomialMultiple]⟩

theorem polynomialCongruent_symm {m a b : Nat} (h : PolynomialCongruent m a b) : PolynomialCongruent m b a := by
  obtain ⟨xs, h⟩ := h
  exact ⟨xs, by simpa [Nat.xor_comm] using h⟩

theorem polynomialCongruent_trans {m a b c : Nat}
    (hab : PolynomialCongruent m a b) (hbc : PolynomialCongruent m b c) : PolynomialCongruent m a c := by
  obtain ⟨xs, hab⟩ := hab
  obtain ⟨ys, hbc⟩ := hbc
  refine ⟨xs ++ ys, ?_⟩
  rw [polynomialMultiple_append, ← hab, ← hbc]
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_xor, Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm]

def polynomialSetoid (m : Nat) : Setoid Nat where
  r := PolynomialCongruent m
  iseqv := ⟨polynomialCongruent_refl m, polynomialCongruent_symm, polynomialCongruent_trans⟩

abbrev BinaryQuotient := Quotient (polynomialSetoid modulus)

def polynomialClass (p : Nat) : BinaryQuotient := Quotient.mk (polynomialSetoid modulus) p

theorem polynomialCongruent_step (m p n : Nat) : PolynomialCongruent m p (p ^^^ (m <<< n)) := by
  refine ⟨[n], ?_⟩
  apply Nat.eq_of_testBit_eq
  intro i
  simp [polynomialMultiple, Nat.testBit_xor, Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm]

theorem remainderSteps_congruent (d m n p : Nat) : PolynomialCongruent m p (remainderSteps d m n p) := by
  induction n generalizing p with
  | zero => exact polynomialCongruent_refl m p
  | succ n ih =>
    simp only [remainderSteps.succ]
    split
    · exact polynomialCongruent_trans (polynomialCongruent_step m p n) (ih _)
    · exact ih p

theorem remainder_class (p : Nat) : polynomialClass p = polynomialClass (remainder p) :=
  Quotient.sound (remainderSteps_congruent 64 modulus 64 p)

set_option maxHeartbeats 0 in
theorem remainder_monomial_bounded : ∀ i : Fin 128, remainder (2^i.val) < 2^64 := by decide

theorem remainder_pack_bounded (n : Nat) (hn : n ≤ 128) (bits : Nat → Bool) :
    remainder (pack n bits).toNat < 2^64 := by
  induction n with
  | zero => change remainder 0 < 2^64; rw [remainder, remainderSteps_zero]; decide
  | succ n ih =>
    rw [pack_toNat_step]
    simp only [remainder, remainderSteps_xor]
    cases hb : bits n
    · simpa [remainder, remainderSteps_zero] using ih (by omega)
    · exact Nat.xor_lt_two_pow (ih (by omega)) (remainder_monomial_bounded ⟨n, by omega⟩)

theorem remainder_bounded (p : BitVec 128) : remainder p.toNat < 2^64 := by
  have h := remainder_pack_bounded 128 (by omega) p.getLsbD
  rw [pack_eta] at h
  exact h

theorem mul_class_correct (a b : K) : polynomialClass (mul a b).toNat = polynomialClass (polynomialProduct a b) := by
  have h := remainder_bounded (pack 128 (productCoeff a b))
  change remainder (polynomialProduct a b) < 2^64 at h
  change polynomialClass ((remainder (polynomialProduct a b)) % 2^64) = _
  rw [Nat.mod_eq_of_lt h]
  exact (remainder_class _).symm

theorem extensionRemainder_congruent (p : Fin 5 → K) :
    ExtensionCongruent p (extendRepresentative (extensionRemainder p)) := by
  refine ⟨p 3, p 4, ?_⟩
  intro i
  have hi := i.isLt
  match i with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ =>
    simp only [extendRepresentative, extensionRemainder, extensionMultiple, add]
    apply UInt64.toBitVec_inj.mp
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp [Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm]

theorem extension_product_class_correct (a b : E) :
    ExtensionCongruent (extensionProduct a b) (extendRepresentative (emul a b)) :=
  extensionRemainder_congruent _

end LeanVmXmss.Proofs.Field
