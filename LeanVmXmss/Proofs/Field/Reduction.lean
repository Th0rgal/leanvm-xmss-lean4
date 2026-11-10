import Proofs.Field.Convolution

namespace LeanVmXmss.Proofs.Field

open Spec.Field (pack remainderSteps remainder)

set_option maxRecDepth 20000

theorem correction_xor (p q t : Nat) (a b : Bool) :
    (if a ^^ b then (p ^^^ q) ^^^ t else p ^^^ q) =
      (if a then p ^^^ t else p) ^^^ (if b then q ^^^ t else q) := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases a <;> cases b <;> simp [Nat.testBit_xor, Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm]

theorem remainderSteps_xor (d m n p q : Nat) :
    remainderSteps d m n (p ^^^ q) = remainderSteps d m n p ^^^ remainderSteps d m n q := by
  induction n generalizing p q with
  | zero => rfl
  | succ n ih =>
    simp only [remainderSteps.succ, Nat.testBit_xor, correction_xor, ih]

theorem remainderSteps_zero (d m n : Nat) : remainderSteps d m n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [remainderSteps.succ, Nat.zero_testBit, Bool.false_eq_true, ↓reduceIte] using ih

theorem pack_toNat_step (f : Nat → Bool) (n : Nat) :
    (pack (n + 1) f).toNat = (pack n f).toNat ^^^ (if f n then 2^n else 0) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [← BitVec.getLsbD, pack.succ, BitVec.getLsbD_cons, Nat.testBit_xor]
  change (if i = n then f n else (pack n f).getLsbD i) =
    ((pack n f).getLsbD i ^^ (if f n then 2^n else 0).testBit i)
  by_cases h : i = n
  · subst i
    cases hb : f n <;> simp [hb, BitVec.getLsbD_of_ge, Nat.testBit_two_pow]
  · cases hb : f n <;> simp [h, hb, Nat.testBit_two_pow, Ne.symm h]

theorem xorLinear_eq_pack (F G : Nat → BitVec w)
    (F0 : F 0 = 0) (G0 : G 0 = 0)
    (Fx : ∀ a b, F (a ^^^ b) = F a ^^^ F b)
    (Gx : ∀ a b, G (a ^^^ b) = G a ^^^ G b)
    (n : Nat) (basis : ∀ i, i < n → F (2^i) = G (2^i)) (bits : Nat → Bool) :
    F (pack n bits).toNat = G (pack n bits).toNat := by
  induction n with
  | zero => change F 0 = G 0; exact F0.trans G0.symm
  | succ n ih =>
    rw [pack_toNat_step, Fx, Gx, ih (fun i hi => basis i (by omega))]
    congr 1
    cases hb : bits n <;> simp [F0, G0, basis n (by omega)]

def referenceReduce (p : Nat) : BitVec 64 := BitVec.ofNat 64 (remainder p)

def foldedReduce (p : Nat) : BitVec 64 := (Model.Field.reduce (BitVec.ofNat 128 p)).toBitVec

theorem referenceReduce_zero : referenceReduce 0 = 0 := by
  simp [referenceReduce, remainder, remainderSteps_zero]

theorem referenceReduce_xor (a b : Nat) :
    referenceReduce (a ^^^ b) = referenceReduce a ^^^ referenceReduce b := by
  simp only [referenceReduce, remainder, remainderSteps_xor, BitVec.ofNat_xor]

theorem foldedReduce_zero : foldedReduce 0 = 0 := by decide

theorem foldedReduce_xor (a b : Nat) :
    foldedReduce (a ^^^ b) = foldedReduce a ^^^ foldedReduce b := by
  simp only [foldedReduce, BitVec.ofNat_xor, reduce_xor, UInt64.toBitVec_xor]

set_option maxHeartbeats 0 in
theorem reduction_basis : ∀ i : Fin 128, foldedReduce (2^i.val) = referenceReduce (2^i.val) := by
  decide

theorem pack_eta (p : BitVec n) : pack n p.getLsbD = p := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact pack_bit _ _ _ hi

theorem reduce_refines_remainder (p : BitVec 128) :
    (Model.Field.reduce p).toBitVec = referenceReduce p.toNat := by
  have h := xorLinear_eq_pack foldedReduce referenceReduce foldedReduce_zero referenceReduce_zero
    foldedReduce_xor referenceReduce_xor 128 (fun i hi => reduction_basis ⟨i, hi⟩) p.getLsbD
  rw [pack_eta] at h
  simpa [foldedReduce] using h

theorem mul_refines_spec (a b : Spec.Field.K) : Model.Field.mul a b = Spec.Field.mul a b := by
  apply UInt64.toBitVec_inj.mp
  rw [Model.Field.mul, reduce_refines_remainder, clmul_toNat]
  rfl

end LeanVmXmss.Proofs.Field
