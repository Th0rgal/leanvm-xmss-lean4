import Proofs.Field.Reduction

namespace LeanVmXmss.Proofs.Field

open Spec.Field (K)
open Model.Field

set_option maxRecDepth 20000

theorem xorLinear_eq_word (F G : K → BitVec w)
    (F0 : F 0 = 0) (G0 : G 0 = 0)
    (Fx : ∀ a b, F (a ^^^ b) = F a ^^^ F b)
    (Gx : ∀ a b, G (a ^^^ b) = G a ^^^ G b)
    (basis : ∀ i : Fin 64, F (UInt64.ofNat (2^i.val)) = G (UInt64.ofNat (2^i.val)))
    (a : K) : F a = G a := by
  have h := xorLinear_eq_pack (fun n => F (UInt64.ofNat n)) (fun n => G (UInt64.ofNat n)) F0 G0
    (by intros; simp [Fx]) (by intros; simp [Gx]) 64 (fun i hi => basis ⟨i, hi⟩) a.toBitVec.getLsbD
  rw [pack_eta] at h
  simpa using h

theorem mul_zero_left (a : K) : mul 0 a = 0 := by
  have h := mul_xor_left 0 0 a
  simpa using h

theorem mul_zero_right (a : K) : mul a 0 = 0 := by
  have h := mul_xor_right a 0 0
  simpa using h

set_option maxHeartbeats 0 in
theorem mul_basis_comm : ∀ i j : Fin 64,
    mul (UInt64.ofNat (2^i.val)) (UInt64.ofNat (2^j.val)) =
      mul (UInt64.ofNat (2^j.val)) (UInt64.ofNat (2^i.val)) := by decide

theorem mul_basis_comm_word (i : Fin 64) (a : K) :
    mul (UInt64.ofNat (2^i.val)) a = mul a (UInt64.ofNat (2^i.val)) := by
  apply UInt64.toBitVec_inj.mp
  exact xorLinear_eq_word
    (fun b => (mul (UInt64.ofNat (2^i.val)) b).toBitVec)
    (fun b => (mul b (UInt64.ofNat (2^i.val))).toBitVec)
    (by simp [mul_zero_right]) (by simp [mul_zero_left])
    (by intros; simp [mul_xor_right]) (by intros; simp [mul_xor_left])
    (fun j => congrArg UInt64.toBitVec (mul_basis_comm i j)) a

theorem mul_comm (a b : K) : mul a b = mul b a := by
  apply UInt64.toBitVec_inj.mp
  exact xorLinear_eq_word
    (fun a => (mul a b).toBitVec) (fun a => (mul b a).toBitVec)
    (by simp [mul_zero_left]) (by simp [mul_zero_right])
    (by intros; simp [mul_xor_left]) (by intros; simp [mul_xor_right])
    (fun i => congrArg UInt64.toBitVec (mul_basis_comm_word i b)) a

theorem spreadSteps_xor (a b : BitVec 64) (n : Nat) :
    spreadSteps (a ^^^ b) n = spreadSteps a n ^^^ spreadSteps b n := by
  induction n with
  | zero => simp only [spreadSteps.zero]; decide
  | succ n ih =>
    simp only [spreadSteps.succ, ih, BitVec.getLsbD_xor, select_xor]
    exact xor_shuffle _ _ _ _

theorem square_zero : square 0 = 0 := by decide

theorem square_xor (a b : K) : square (a ^^^ b) = square a ^^^ square b := by
  simp only [square, UInt64.toBitVec_xor, spreadSteps_xor, reduce_xor]

theorem selfMul_xor (a b : K) : mul (a ^^^ b) (a ^^^ b) = mul a a ^^^ mul b b := by
  simp only [mul_xor_left, mul_xor_right]
  rw [mul_comm b a]
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm]

set_option maxHeartbeats 0 in
theorem square_basis : ∀ i : Fin 64,
    square (UInt64.ofNat (2^i.val)) = mul (UInt64.ofNat (2^i.val)) (UInt64.ofNat (2^i.val)) := by decide

theorem square_refines_mul (a : K) : square a = mul a a := by
  apply UInt64.toBitVec_inj.mp
  exact xorLinear_eq_word (fun a => (square a).toBitVec) (fun a => (mul a a).toBitVec)
    (by simp [square_zero]) (by simp [mul_zero_left])
    (by intros; simp [square_xor]) (by intros; simp [selfMul_xor])
    (fun i => congrArg UInt64.toBitVec (square_basis i)) a

theorem square_refines_spec (a : K) : square a = Spec.Field.square a := by
  rw [square_refines_mul, mul_refines_spec]
  rfl

end LeanVmXmss.Proofs.Field
