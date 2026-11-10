import Model.Field.NativeKernel
import Proofs.Field.Windows
import Proofs.Field.NativeHighShift

namespace LeanVmXmss.Proofs.Field

open Model.Field
open Spec.Field (K E)

set_option maxRecDepth 20000
set_option maxHeartbeats 800000

theorem nativeSelect_toBitVec (a b i : K) :
    (nativeSelect a b i).toBitVec =
      if b.toBitVec.getLsbD (i.toNat % 64) then a.toBitVec else 0 := by
  simp only [nativeSelect, UInt64.toBitVec_and, UInt64.toBitVec_sub,
    UInt64.toBitVec_shiftRight, UInt64.toBitVec_ofNat]
  rw [BitVec.and_one_eq_setWidth_ofBool_getLsbD]
  cases h : b.toBitVec.getLsbD (i.toNat % 64) <;> simp [h]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_and]
  change (a.toBitVec.getLsbD j && (BitVec.allOnes 64).getLsbD j) = _
  have bits : ∀ k : Fin 64, (BitVec.allOnes 64).getLsbD k.val = true := by decide
  rw [bits ⟨j, hj⟩]
  exact Bool.and_true _

theorem nativeReduce_correct (p : BitVec 128) :
    nativeReduce (UInt64.ofBitVec (p.setWidth 64))
      (UInt64.ofBitVec ((p >>> 64).setWidth 64)) = reduce p := by
  apply UInt64.toBitVec_inj.mp
  simp [nativeReduce, reduce, UInt64.toBitVec_shiftRight, UInt64.toBitVec_shiftLeft]

theorem nativeClmulLo_correct (a b : K) :
    (nativeClmulLo a b).toBitVec = (clmul a b).setWidth 64 := by
  have resize (p : Bool) (x : BitVec 128) :
      (if p then x else 0).setWidth 64 = if p then x.setWidth 64 else 0 := by
    cases p <;> rfl
  have shift (p : Bool) (x : BitVec 64) (n : Nat) :
      (if p then x else 0) <<< n = if p then x <<< n else 0 := by
    cases p <;> simp
  have shiftCond (p : Bool) (x : BitVec 64) (n : Nat) :
      (bif p then x else 0) <<< n = bif p then x <<< n else 0 := by
    cases p <;> simp
  simp only [nativeClmulLo, nativeClmulByte, clmul, clmulSteps.succ, clmulSteps.zero,
    UInt64.toBitVec_xor, nativeSelect_toBitVec, UInt64.toBitVec_shiftLeft,
    UInt64.toBitVec_shiftRight, UInt64.toBitVec_ofNat, UInt64.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.getLsbD_ushiftRight,
    BitVec.setWidth_xor, BitVec.shiftLeft_xor_distrib,
    BitVec.setWidth_shiftLeft_of_le (by decide : 64 ≤ 128),
    BitVec.setWidth_setWidth_of_le a.toBitVec (by decide : 64 ≤ 128),
     resize, shift, ← BitVec.shiftLeft_add]
  simp only [Nat.reduceMod, Nat.reduceAdd, BitVec.reduceUMod, BitVec.toNat_ofNat,
    UInt64.reduceToNat, Nat.zero_add, Nat.add_zero, BitVec.shiftLeft_zero,
    BitVec.zero_xor, BitVec.setWidth_zero, BitVec.setWidth_eq]
  simp only [Nat.reducePow, Nat.reduceMod, BitVec.reduceUMod, BitVec.toNat_ofNat]
  simp only [BitVec.getLsbD_ushiftRight, BitVec.shiftLeft_xor_distrib,
    shift, shiftCond, BitVec.shiftLeft_eq',
    ← BitVec.shiftLeft_add, BitVec.zero_xor, BitVec.shiftLeft_zero,
    Nat.reducePow, Nat.reduceMod, Nat.reduceAdd, BitVec.toNat_ofNat,
    BitVec.xor_assoc]
  dsimp
  simp only [BitVec.getLsbD_ushiftRight, BitVec.shiftLeft_xor_distrib,
    shift, ← BitVec.shiftLeft_add, BitVec.xor_assoc, BitVec.zero_xor]

theorem nativeClmulHi_correct (a b : K) :
    (nativeClmulHi a b).toBitVec = ((clmul a b >>> 64).setWidth 64) := by
  have shift (p : Bool) (x : BitVec 64) (n : Nat) :
      (if p then x else 0) <<< n = if p then x <<< n else 0 := by
    cases p <;> simp
  have right (p : Bool) (x : BitVec 128) :
      ((if p then x else 0) >>> 64).setWidth 64 =
        if p then (x >>> 64).setWidth 64 else 0 := by
    cases p
    · exact (show ((0 : BitVec 128) >>> 64).setWidth 64 = 0 by decide)
    · rfl
  have high (s : Nat) (hs : s < 64) :
      ((a.toBitVec.setWidth 128 <<< s) >>> 64).setWidth 64 =
        if s = 0 then 0 else a.toBitVec >>> (64 - s) :=
    nativeHighShift a.toBitVec ⟨s, hs⟩
  simp only [nativeClmulHi,
    clmul, clmulSteps.succ, clmulSteps.zero, UInt64.toBitVec_xor,
    nativeSelect_toBitVec, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
    UInt64.toBitVec_ofNat, UInt64.toNat_ofNat,
    BitVec.ushiftRight_xor_distrib, BitVec.setWidth_xor, right]
  simp (disch := decide) only [high]
  simp only [Nat.reducePow, Nat.reduceMod, BitVec.reduceUMod, BitVec.toNat_ofNat,
    UInt64.reduceToNat, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq']
  dsimp
  have z : ((0 : BitVec 128) >>> 64).setWidth 64 = 0 := by decide
  simp only [z, BitVec.zero_xor, BitVec.ushiftRight_eq']
  have iz (p : Bool) : (if p then (0 : BitVec 64) else 0) = 0 := by
    cases p <;> rfl
  simp only [ite_self, BitVec.zero_xor]

theorem nativeMul_correct (a b : K) : nativeMul a b = mul a b := by
  have lo : nativeClmulLo a b = UInt64.ofBitVec ((clmul a b).setWidth 64) := by
    apply UInt64.toBitVec_inj.mp
    exact nativeClmulLo_correct a b
  have hi : nativeClmulHi a b = UInt64.ofBitVec ((clmul a b >>> 64).setWidth 64) := by
    apply UInt64.toBitVec_inj.mp
    exact nativeClmulHi_correct a b
  rw [nativeMul, lo, hi]
  exact nativeReduce_correct (clmul a b)

theorem nativeSquare_correct (a : K) : nativeSquare a = square a := by
  rw [nativeSquare, nativeMul_correct, square_refines_mul]

theorem nativeKaratsuba_correct (a b : E) : nativeKaratsuba a b = karatsubaMul a b := by
  simp only [nativeKaratsuba, nativeKaratsuba0, nativeKaratsuba1, nativeKaratsuba2,
    nativeMul_correct, karatsubaMul]

theorem nativeInv_correct (a : K) : nativeInv a = inv a := by
  simp only [nativeInv, nativeInv63, nativeInv60, nativeInv48, nativeInv24,
    nativeInv12, nativeInv6, nativeInv3, nativeSquare24, nativeSquare12,
    nativeSquare6, nativeSquare3, nativeSquare_correct, nativeMul_correct]
  rfl

theorem nativeEinv_correct (a : E) : nativeEinv a = einv a := by
  simp only [nativeEinv, nativeKaratsuba_correct, nativeKaratsuba0,
    nativeMul_correct, nativeInv_correct, einv, norm, mulBase, frobenius2, karatsubaMul]

end LeanVmXmss.Proofs.Field
