import Proofs.Field.Operations

namespace LeanVmXmss.Proofs.Field

open Spec.Field (K E)
open Model.Field

set_option maxRecDepth 20000
set_option maxHeartbeats 200000

theorem xorLinear_eq_uint64 (F G : K → K)
    (F0 : F 0 = 0) (G0 : G 0 = 0)
    (Fx : ∀ a b, F (a ^^^ b) = F a ^^^ F b)
    (Gx : ∀ a b, G (a ^^^ b) = G a ^^^ G b)
    (basis : ∀ i : Fin 64, F (UInt64.ofNat (2^i.val)) = G (UInt64.ofNat (2^i.val)))
    (a : K) : F a = G a := by
  apply UInt64.toBitVec_inj.mp
  exact xorLinear_eq_word (fun x => (F x).toBitVec) (fun x => (G x).toBitVec)
    (by simp [F0]) (by simp [G0])
    (by intros; simp [Fx]) (by intros; simp [Gx])
    (fun i => congrArg UInt64.toBitVec (basis i)) a

theorem clmulSteps_monomial (a : BitVec 64) (j n : Nat) (hj : j < 64) :
    clmulSteps a (BitVec.ofNat 64 (2^j)) n =
      if j < n then a.setWidth 128 <<< j else 0 := by
  induction n with
  | zero => simp only [clmulSteps.zero]; simp
  | succ n ih =>
    have hp : 2^j < 2^64 := Nat.pow_lt_pow_of_lt (by decide) hj
    have hb : (BitVec.ofNat 64 (2^j)).getLsbD n = decide (j = n) := by
      simp [BitVec.getLsbD, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp, Nat.testBit_two_pow]
    simp only [clmulSteps.succ, ih, hb]
    by_cases h : j = n
    · subst n
      simp
    · by_cases hlt : j < n
      · simp [h, hlt, show j < n + 1 by omega]
      · simp [h, hlt, show ¬j < n + 1 by omega]

theorem mul_monomial (a : K) (j : Nat) (hj : j < 64) :
    mul a (UInt64.ofNat (2^j)) = reduce (a.toBitVec.setWidth 128 <<< j) := by
  change reduce (clmulSteps a.toBitVec (BitVec.ofNat 64 (2^j)) 64) = _
  rw [clmulSteps_monomial _ _ _ hj, ite_eq_left hj]

set_option maxHeartbeats 0 in
theorem reduce_generator_basis_assoc : ∀ j k : Fin 64,
    reduce ((reduce ((2 : BitVec 128) <<< j.val)).toBitVec.setWidth 128 <<< k.val) =
      reduce ((reduce ((BitVec.ofNat 128 (2^j.val)) <<< k.val)).toBitVec.setWidth 128 <<< 1) := by
  decide

theorem mul_generator_basis_assoc (j k : Fin 64) :
    mul (mul 2 (UInt64.ofNat (2^j.val))) (UInt64.ofNat (2^k.val)) =
      mul 2 (mul (UInt64.ofNat (2^j.val)) (UInt64.ofNat (2^k.val))) := by
  calc
    _ = reduce ((mul 2 (UInt64.ofNat (2^j.val))).toBitVec.setWidth 128 <<< k.val) := mul_monomial _ _ k.isLt
    _ = reduce ((reduce ((2 : BitVec 128) <<< j.val)).toBitVec.setWidth 128 <<< k.val) := by
      rw [mul_monomial _ _ j.isLt]
      rfl
    _ = reduce ((reduce ((BitVec.ofNat 128 (2^j.val)) <<< k.val)).toBitVec.setWidth 128 <<< 1) := reduce_generator_basis_assoc j k
    _ = mul (mul (UInt64.ofNat (2^j.val)) (UInt64.ofNat (2^k.val))) (UInt64.ofNat (2^1)) := by
      rw [mul_monomial _ 1 (by decide)]
      congr 1
      rw [mul_monomial _ _ k.isLt]
      congr 1
      congr 1
      congr 1
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.pow_lt_pow_of_lt (by decide : 1 < (2 : Nat)) j.isLt)]
    _ = _ := mul_comm _ _

theorem mul_generator_assoc (b c : K) : mul (mul 2 b) c = mul 2 (mul b c) := by
  apply xorLinear_eq_uint64 (fun b => mul (mul 2 b) c) (fun b => mul 2 (mul b c))
    (by simp [mul_zero_left, mul_zero_right]) (by simp [mul_zero_left, mul_zero_right])
    (by intros; simp [mul_xor_left, mul_xor_right])
    (by intros; simp [mul_xor_left, mul_xor_right]) _ b
  intro j
  apply xorLinear_eq_uint64 _ _
    (by simp [mul_zero_right]) (by simp [mul_zero_right])
    (by intros; simp [mul_xor_right]) (by intros; simp [mul_xor_right]) _ c
  exact mul_generator_basis_assoc j

theorem mul_generator_step : ∀ i : Fin 63,
    mul 2 (UInt64.ofNat (2^i.val)) = UInt64.ofNat (2^(i.val + 1)) := by decide

theorem mul_basis_assoc_word (i : Nat) (hi : i < 64) (b c : K) :
    mul (mul (UInt64.ofNat (2^i)) b) c = mul (UInt64.ofNat (2^i)) (mul b c) := by
  induction i with
  | zero => simp [mul_one_left]
  | succ i ih =>
    rw [← mul_generator_step ⟨i, by omega⟩]
    rw [mul_generator_assoc, mul_generator_assoc, ih (by omega), mul_generator_assoc]

theorem mul_assoc (a b c : K) : mul (mul a b) c = mul a (mul b c) := by
  apply xorLinear_eq_uint64 (fun a => mul (mul a b) c) (fun a => mul a (mul b c))
    (by simp [mul_zero_left]) (by simp [mul_zero_left])
    (by intros; simp [mul_xor_left]) (by intros; simp [mul_xor_left]) _ a
  exact fun i => mul_basis_assoc_word i.val i.isLt b c

theorem kxor_assoc (a b c : K) : (a ^^^ b) ^^^ c = a ^^^ (b ^^^ c) := by
  apply UInt64.toBitVec_inj.mp
  simp [BitVec.xor_assoc]

theorem kxor_comm (a b : K) : a ^^^ b = b ^^^ a := by
  apply UInt64.toBitVec_inj.mp
  simp [BitVec.xor_comm]

theorem kxor_left_comm (a b c : K) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← kxor_assoc, kxor_comm a b, kxor_assoc]

set_option maxHeartbeats 5000000 in
theorem emul_assoc (a b c : E) : karatsubaMul (karatsubaMul a b) c = karatsubaMul a (karatsubaMul b c) := by
  simp only [karatsuba_refines_polynomial, polynomialMul, mul_xor_left, mul_xor_right, mul_assoc]
  congr 1 <;> simp only [kxor_assoc, kxor_comm, kxor_left_comm]

theorem frobenius_mul (a b : E) : frobenius (karatsubaMul a b) = karatsubaMul (frobenius a) (frobenius b) := by
  simp only [karatsuba_refines_polynomial, polynomialMul, frobenius, mul_xor_left, mul_xor_right]
  congr 1 <;> apply UInt64.toBitVec_inj.mp <;>
    apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    simp [Bool.xor_comm, Bool.xor_left_comm]

theorem frobenius_fixed (a : E) (h : frobenius a = a) : a = Spec.Field.embed a.c0 := by
  have h1 := congrArg E.c1 h
  have h2 := congrArg E.c2 h
  simp only [frobenius] at h1 h2
  have hz : a.c1 = 0 := by
    apply UInt64.toBitVec_inj.mp
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hb := congrArg (fun x : K => x.toBitVec.getLsbD i) h2
    simp only [UInt64.toBitVec_xor, BitVec.getLsbD_xor] at hb
    cases he : a.c1.toBitVec.getLsbD i <;> cases he2 : a.c2.toBitVec.getLsbD i <;> simp_all
  cases a
  simp_all [Spec.Field.embed]

theorem norm_in_base (a : E) :
    karatsubaMul a (karatsubaMul (frobenius a) (frobenius2 a)) = Spec.Field.embed (norm a) := by
  apply frobenius_fixed
  simp only [frobenius_mul, frobenius2, frobenius_order_three]
  rw [← emul_assoc, emul_comm _ a]

end LeanVmXmss.Proofs.Field
