import Proofs.Field.Windows
import Model.Field.NativeKernel

namespace LeanVmXmss.Proofs.Field

open Model.Field
open Spec.Field (K)

theorem nativeSelect_word (a b i : K) :
    (nativeSelect a b i).toBitVec =
      if b.toBitVec.getLsbD (i.toNat % 64) then a.toBitVec else 0 := by
  simp only [nativeSelect, UInt64.toBitVec_and, UInt64.toBitVec_sub,
    UInt64.toBitVec_shiftRight, UInt64.toBitVec_ofNat]
  rw [BitVec.and_one_eq_setWidth_ofBool_getLsbD]
  cases h : b.toBitVec.getLsbD (i.toNat % 64) <;> simp [h]
  exact BitVec.and_allOnes

theorem nativeClmulByte_correct (a b : K) :
    (nativeClmulByte a b).toBitVec =
      (clmulSteps a.toBitVec b.toBitVec 8).setWidth 64 := by
  have resize (p : Bool) (x : BitVec 128) :
      (if p then x else 0).setWidth 64 = if p then x.setWidth 64 else 0 := by
    cases p <;> rfl
  simp only [nativeClmulByte, clmulSteps.succ, clmulSteps.zero,
    UInt64.toBitVec_xor, nativeSelect_word, UInt64.toBitVec_shiftLeft,
    UInt64.toBitVec_ofNat, UInt64.toNat_ofNat,
    BitVec.setWidth_xor,
    BitVec.setWidth_shiftLeft_of_le (by decide : 64 ≤ 128),
    resize]
  simp only [BitVec.setWidth_setWidth_of_le a.toBitVec (by decide : 64 ≤ 128),
    BitVec.setWidth_eq]
  have z : (0 : BitVec 128).setWidth 64 = 0 := rfl
  simp only [z, BitVec.shiftLeft_zero]
  dsimp
  simp only [BitVec.zero_xor]

end LeanVmXmss.Proofs.Field
