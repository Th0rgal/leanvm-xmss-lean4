import Model.Vm.Kernel

namespace LeanVmXmss.Proofs.Vm

theorem xor_kernel (x y : UInt64) : Model.Vm.xorKernel x y = x ^^^ y := by
  unfold Model.Vm.xorKernel
  exact Eq.refl _

theorem theta_kernel (x y : UInt64) :
    Model.Vm.thetaKernel x y = x ^^^ ((y <<< 1) ||| (y >>> 63)) := by
  unfold Model.Vm.thetaKernel
  exact Eq.refl _

theorem chi_kernel (x y z : UInt64) : Model.Vm.chiKernel x y z = x ^^^ ((~~~y) &&& z) := by
  unfold Model.Vm.chiKernel
  exact Eq.refl _

theorem rotate_left_kernel (x n : UInt64) : Model.Vm.rotateLeftKernel x n = x <<< n := by
  unfold Model.Vm.rotateLeftKernel
  exact Eq.refl _

theorem rotate_right_kernel (x n : UInt64) : Model.Vm.rotateRightKernel x n = x >>> n := by
  unfold Model.Vm.rotateRightKernel
  exact Eq.refl _

theorem scalar_step_msb (x : UInt64) :
    ((0 : UInt64) - (x >>> 63)) = if x.toNat / 2 ^ 63 == 0 then 0 else 0xffffffffffffffff := by
  have hshift : (x >>> 63).toNat = x.toNat / 2 ^ 63 := by
    rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    rfl
  by_cases h : x.toNat / 2 ^ 63 = 0
  · have hx : x >>> 63 = 0 := UInt64.toNat_inj.mp (by simpa [h] using hshift)
    have hb : (x.toNat / 2 ^ 63 == 0) = true := beq_iff_eq.mpr h
    have hc : (0 : UInt64) - 0 = 0 := by decide
    rw [hx, hb, hc]
    rfl
  · have hlt : x.toNat < 2 ^ 64 := x.toNat_lt
    have h1 : x.toNat / 2 ^ 63 = 1 := by omega
    have hx : x >>> 63 = 1 := UInt64.toNat_inj.mp (by simpa [h1] using hshift)
    have hb : (x.toNat / 2 ^ 63 == 0) = false := beq_false_of_ne h
    have hc : (0 : UInt64) - 1 = 0xffffffffffffffff := by decide
    rw [hx, hb, hc]
    rfl

theorem scalarGeneratorStep_spec (x : UInt64) :
    Model.Vm.scalarGeneratorStep x =
      (x <<< 1) ^^^ (if x.toNat / 2 ^ 63 == 0 then 0 else 0x1b) := by
  unfold Model.Vm.scalarGeneratorStep
  rw [scalar_step_msb]
  cases x.toNat / 2 ^ 63 == 0
  · have hc : (0xffffffffffffffff : UInt64) &&& 0x1b = 0x1b := by decide
    rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, hc]
  · have hc : (0 : UInt64) &&& 0x1b = 0 := by decide
    rw [if_pos rfl, if_pos rfl, hc]

end LeanVmXmss.Proofs.Vm
