import Proofs.Field.Windows
import Model.Field.NativeKernel

namespace LeanVmXmss.Proofs.Field

open Model.Field
open Spec.Field (K)

set_option maxRecDepth 20000
set_option maxHeartbeats 800000

theorem nativeHighShift (a : BitVec 64) (s : Fin 64) :
    (((a.setWidth 128) <<< s.val) >>> 64).setWidth 64 =
      if s.val = 0 then 0 else a >>> (64 - s.val) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_shiftLeft, hj, decide_true, Bool.true_and]
  split
  next h =>
    simp only [h, Nat.sub_zero, BitVec.getLsbD_of_ge a (64 + j) (by omega),
      Bool.and_false]
    exact BitVec.getLsbD_zero.symm
  next h =>
    have hs := s.isLt
    have hle : ¬64 + j < s.val := by omega
    have h128 : 64 + j < 128 := by omega
    have hd : 64 + j - s.val < 128 := by omega
    have heq : 64 + j - s.val = 64 - s.val + j := by omega
    simp only [hle, h128, hd, decide_true, decide_false, Bool.not_false,
      Bool.true_and, heq,
      BitVec.getLsbD_ushiftRight]
    simp only [show 64 - s.val + j < 128 by omega, decide_true, Bool.true_and]

end LeanVmXmss.Proofs.Field
