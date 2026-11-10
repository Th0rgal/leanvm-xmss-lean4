import Model.Field.NativeKernel

open LeanVmXmss.Model.Field

theorem nativeSelect_mask_correct (a b i : UInt64) :
    (nativeSelect a b i).toBitVec =
      if b.toBitVec.getLsbD (i.toNat % 64) then a.toBitVec else 0 := by
  simp only [nativeSelect, UInt64.toBitVec_and, UInt64.toBitVec_sub,
    UInt64.toBitVec_shiftRight, UInt64.toBitVec_ofNat]
  rw [BitVec.and_one_eq_setWidth_ofBool_getLsbD]
  cases h : b.toBitVec.getLsbD (i.toNat % 64) <;> simp [h]
  exact BitVec.and_allOnes
