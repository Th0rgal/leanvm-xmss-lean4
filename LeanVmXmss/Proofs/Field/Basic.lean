import Model.Field.Scalar

namespace LeanVmXmss.Proofs.Field

open Spec.Field (K E)
open Model.Field

theorem encode_decode (a : UInt64 × UInt64 × UInt64) :
    Spec.Field.encode (Spec.Field.decode a) = a := by
  cases a with | mk a b => cases b <;> rfl

theorem decode_encode (a : E) : Spec.Field.decode (Spec.Field.encode a) = a := by
  cases a
  rfl

theorem embed_injective {a b : K} (h : Spec.Field.embed a = Spec.Field.embed b) : a = b :=
  congrArg E.c0 h

theorem xor_shuffle (a b c d : BitVec w) :
    (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by
  ac_rfl

theorem select_xor (p q : Bool) (a : BitVec w) :
    (if p ^^ q then a else 0) = (if p then a else 0) ^^^ (if q then a else 0) := by
  cases p <;> cases q <;> simp

theorem clmulSteps_xor_left (a b c : BitVec 64) (n : Nat) :
    clmulSteps (a ^^^ b) c n = clmulSteps a c n ^^^ clmulSteps b c n := by
  induction n with
  | zero => simp only [clmulSteps.zero]; decide
  | succ n ih =>
    simp only [clmulSteps.succ, ih, BitVec.setWidth_xor, BitVec.shiftLeft_xor_distrib]
    split
    · exact xor_shuffle _ _ _ _
    · simp

theorem clmulSteps_xor_right (a b c : BitVec 64) (n : Nat) :
    clmulSteps a (b ^^^ c) n = clmulSteps a b n ^^^ clmulSteps a c n := by
  induction n with
  | zero => simp only [clmulSteps.zero]; decide
  | succ n ih =>
    simp only [clmulSteps.succ, ih, BitVec.getLsbD_xor, select_xor]
    exact xor_shuffle _ _ _ _

theorem reduce_xor (a b : BitVec 128) : reduce (a ^^^ b) = reduce a ^^^ reduce b := by
  apply UInt64.toBitVec_inj.mp
  simp only [reduce, UInt64.toBitVec_ofBitVec, UInt64.toBitVec_xor,
    BitVec.setWidth_xor, BitVec.ushiftRight_xor_distrib, BitVec.shiftLeft_xor_distrib]
  ac_rfl

theorem mul_xor_left (a b c : K) : mul (a ^^^ b) c = mul a c ^^^ mul b c := by
  simp only [mul, clmul, UInt64.toBitVec_xor, clmulSteps_xor_left, reduce_xor]

theorem mul_xor_right (a b c : K) : mul a (b ^^^ c) = mul a b ^^^ mul a c := by
  simp only [mul, clmul, UInt64.toBitVec_xor, clmulSteps_xor_right, reduce_xor]

theorem karatsuba_refines_polynomial (a b : E) : karatsubaMul a b = polynomialMul a b := by
  simp only [karatsubaMul, polynomialMul, mul_xor_left, mul_xor_right]
  congr 1 <;>
    apply UInt64.toBitVec_inj.mp <;>
    apply BitVec.eq_of_getLsbD_eq <;>
    intro i hi <;> simp only [UInt64.toBitVec_xor, BitVec.getLsbD_xor] <;>
    simp [Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]

end LeanVmXmss.Proofs.Field
