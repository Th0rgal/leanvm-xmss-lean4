import Proofs.Field.Associativity

namespace LeanVmXmss.Proofs.Field

open Spec.Field (K E powWith squareNWith)
open Model.Field

set_option maxRecDepth 20000
set_option maxHeartbeats 200000

theorem powWith_add {α : Type} (m : α → α → α) (u a : α)
    (assoc : ∀ a b c, m (m a b) c = m a (m b c))
    (unit : ∀ a, m a u = a) (n k : Nat) :
    powWith m u a (n + k) = m (powWith m u a n) (powWith m u a k) := by
  induction k with
  | zero => simp only [Nat.add_zero, powWith.zero, unit]
  | succ k ih =>
    change m (powWith m u a (n + k)) a = m (powWith m u a n) (m (powWith m u a k) a)
    rw [ih, assoc]

theorem squareN_pow {α : Type} (m : α → α → α) (u a : α) (sq : α → α)
    (assoc : ∀ a b c, m (m a b) c = m a (m b c))
    (unit : ∀ a, m a u = a) (self : ∀ a, sq a = m a a) (n k : Nat) :
    squareNWith sq (powWith m u a n) k = powWith m u a (n * 2^k) := by
  induction k with
  | zero => simp only [squareNWith.zero, Nat.pow_zero, Nat.mul_one]
  | succ k ih =>
    rw [squareNWith.succ, ih, self, ← powWith_add m u a assoc unit]
    congr 1
    simp [Nat.pow_succ, Nat.mul_add, Nat.mul_two]

theorem pow_add (a : K) (n k : Nat) : pow a (n + k) = mul (pow a n) (pow a k) :=
  powWith_add mul 1 a mul_assoc (fun a => (mul_comm a 1).trans (mul_one_left a)) n k

theorem pow_one (a : K) : pow a 1 = a := mul_one_left a

theorem squareN_pow_base (a : K) (n k : Nat) : squareNWith square (pow a n) k = pow a (n * 2^k) :=
  squareN_pow mul 1 a square mul_assoc (fun a => (mul_comm a 1).trans (mul_one_left a)) square_refines_mul n k

theorem inv_eq_pow (a : K) : inv a = pow a (2^64 - 2) := by
  have hs (x : K) : square x = squareNWith square x 1 := rfl
  have hc : Spec.Field.inverseChainWith mul square (pow a 1) = pow a (2^64 - 2) := by
    unfold Spec.Field.inverseChainWith
    simp only [hs, squareN_pow_base, ← pow_add]
  simpa only [pow_one, inv] using hc

theorem squareN_zero (n : Nat) : squareNWith square 0 n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [squareNWith.succ, ih, square_zero]

theorem squareN_xor (a b : K) (n : Nat) :
    squareNWith square (a ^^^ b) n = squareNWith square a n ^^^ squareNWith square b n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [squareNWith.succ, ih, square_xor]

theorem square_mul (a b : K) : square (mul a b) = mul (square a) (square b) := by
  simp only [square_refines_mul]
  rw [mul_assoc, ← mul_assoc b a b, mul_comm b a, mul_assoc a b b, ← mul_assoc]

theorem squareN_mul (a b : K) (n : Nat) :
    squareNWith square (mul a b) n = mul (squareNWith square a n) (squareNWith square b n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [squareNWith.succ, ih, square_mul]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem squareN_generator_order : squareNWith square 2 64 = 2 := by decide

theorem squareN_one (n : Nat) : squareNWith square 1 n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [squareNWith.succ, ih]; decide

theorem squareN_monomial_order (i : Nat) (hi : i < 64) :
    squareNWith square (UInt64.ofNat (2^i)) 64 = UInt64.ofNat (2^i) := by
  induction i with
  | zero => exact squareN_one 64
  | succ i ih =>
    rw [← mul_generator_step ⟨i, by omega⟩, squareN_mul, squareN_generator_order, ih (by omega)]

theorem squareN_order (a : K) : squareNWith square a 64 = a := by
  exact xorLinear_eq_uint64 (fun a => squareNWith square a 64) id (squareN_zero 64) rfl
    (fun a b => squareN_xor a b 64) (fun _ _ => rfl)
    (fun i => squareN_monomial_order i.val i.isLt) a

end LeanVmXmss.Proofs.Field
