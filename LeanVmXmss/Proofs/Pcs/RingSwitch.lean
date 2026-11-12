import Model.Pcs.RingSwitch
import Proofs.Field.NativeKernel
import Proofs.Field.Operations
import Proofs.Field.Frobenius

namespace LeanVmXmss.Proofs.Pcs.RingSwitch

open Spec.Field (K E)

theorem nativeKaratsuba_refines (a b : E) :
    Model.Field.nativeKaratsuba a b = Spec.Field.emul a b :=
  (Proofs.Field.nativeKaratsuba_correct a b).trans (Proofs.Field.karatsuba_refines_spec a b)

theorem nativeKaratsuba_eq_emul :
    Model.Field.nativeKaratsuba = Spec.Field.emul := by
  funext a b
  exact nativeKaratsuba_refines a b

theorem nativeMulBase_refines (a : E) (b : K) :
    Model.Pcs.RingSwitch.nativeMulBase a b = Spec.Field.mulBase a b := by
  have hm : Model.Pcs.RingSwitch.nativeMulBase a b = Model.Field.mulBase a b := by
    simp only [Model.Pcs.RingSwitch.nativeMulBase, Model.Field.mulBase,
      Proofs.Field.nativeMul_correct]
  exact hm.trans (Proofs.Field.mulBase_refines_spec a b)

theorem nativeMulBase_eq_mulBase :
    Model.Pcs.RingSwitch.nativeMulBase = Spec.Field.mulBase := by
  funext a b
  exact nativeMulBase_refines a b

theorem nativeEpow_refines (x : E) (n : Nat) :
    Model.Pcs.RingSwitch.nativeEpow x n = Spec.Field.epow x n := by
  simp only [Model.Pcs.RingSwitch.nativeEpow, Spec.Field.epow, nativeKaratsuba_eq_emul]

theorem nativeEpow_eq_epow :
    Model.Pcs.RingSwitch.nativeEpow = Spec.Field.epow := by
  funext x n
  exact nativeEpow_refines x n

theorem nativeSquareN_refines (a : E) (n : Nat) :
    Model.Pcs.RingSwitch.nativeSquareN a n = Spec.Field.epow a (1 <<< n) := by
  have hsq : (fun x => Model.Field.nativeKaratsuba x x) = Model.Field.esquare := by
    funext x
    rw [Proofs.Field.nativeKaratsuba_correct]
    exact (Proofs.Field.karatsuba_refines_polynomial x x).trans
      (Proofs.Field.esquare_refines_polynomial x).symm
  have hpow : Model.Field.epow a (1 * 2 ^ n) = Spec.Field.epow a (1 <<< n) := by
    have hk : Model.Field.karatsubaMul = Spec.Field.emul := by
      funext x y
      exact Proofs.Field.karatsuba_refines_spec x y
    simp only [Model.Field.epow, Spec.Field.epow, hk, Nat.one_mul, Nat.shiftLeft_eq]
  calc Model.Pcs.RingSwitch.nativeSquareN a n
      = Spec.Field.squareNWith Model.Field.esquare a n := by
          rw [Model.Pcs.RingSwitch.nativeSquareN, hsq]
    _ = Spec.Field.squareNWith Model.Field.esquare (Model.Field.epow a 1) n := by
          rw [Proofs.Field.epow_one a]
    _ = Model.Field.epow a (1 * 2 ^ n) := Proofs.Field.esquareN_pow a 1 n
    _ = Spec.Field.epow a (1 <<< n) := hpow

theorem nativeSquareN_eq_epow_shift :
    Model.Pcs.RingSwitch.nativeSquareN = (fun a n => Spec.Field.epow a (1 <<< n)) := by
  funext a n
  exact nativeSquareN_refines a n

theorem nativeSquareN_eq_esquareN :
    Model.Pcs.RingSwitch.nativeSquareN = Spec.Pcs.RingSwitch.esquareN := by
  funext a n
  have hsq : (fun x => Model.Field.nativeKaratsuba x x) = Spec.Field.esquare := by
    funext x
    exact nativeKaratsuba_refines x x
  simp only [Model.Pcs.RingSwitch.nativeSquareN, Spec.Pcs.RingSwitch.esquareN, hsq]

theorem applyComposed_refines (value : E) (challenges : Array E) :
    Model.Pcs.RingSwitch.applyComposed value challenges =
      Spec.Pcs.RingSwitch.applyComposed value challenges := by
  simp only [Model.Pcs.RingSwitch.applyComposed, Spec.Pcs.RingSwitch.applyComposed,
    Model.Pcs.RingSwitch.compositionShifts, nativeKaratsuba_eq_emul, nativeSquareN_eq_esquareN]

theorem applyComposed_eq_spec :
    Model.Pcs.RingSwitch.applyComposed = Spec.Pcs.RingSwitch.applyComposed := by
  funext value challenges
  exact applyComposed_refines value challenges

theorem coordinateWeights_refines (challenges : Array E) :
    Model.Pcs.RingSwitch.coordinateWeights challenges =
      Spec.Pcs.RingSwitch.coordinateWeights challenges := by
  simp only [Model.Pcs.RingSwitch.coordinateWeights, Spec.Pcs.RingSwitch.coordinateWeights,
    Model.Pcs.RingSwitch.degreeE, Model.Pcs.RingSwitch.coordinateBasis, applyComposed_eq_spec]

theorem frobeniusCoefficient_refines (challenges : Array E) (k : Nat) :
    Model.Pcs.RingSwitch.frobeniusCoefficient challenges k =
      Spec.Pcs.RingSwitch.frobeniusCoefficient challenges k := by
  simp only [Model.Pcs.RingSwitch.frobeniusCoefficient, Spec.Pcs.RingSwitch.frobeniusCoefficient,
    Model.Pcs.RingSwitch.compositionShifts, nativeKaratsuba_eq_emul, nativeSquareN_eq_esquareN]

theorem frobeniusCoefficient_eq_spec :
    Model.Pcs.RingSwitch.frobeniusCoefficient = Spec.Pcs.RingSwitch.frobeniusCoefficient := by
  funext challenges k
  exact frobeniusCoefficient_refines challenges k

theorem frobeniusCoefficients_refines (challenges : Array E) :
    Model.Pcs.RingSwitch.frobeniusCoefficients challenges =
      Spec.Pcs.RingSwitch.frobeniusCoefficients challenges := by
  simp only [Model.Pcs.RingSwitch.frobeniusCoefficients, Spec.Pcs.RingSwitch.frobeniusCoefficients,
    Model.Pcs.RingSwitch.packingWidth, frobeniusCoefficient_eq_spec]

theorem ringWeightAt_refines (point rPrime coefficients : Array E) :
    Model.Pcs.RingSwitch.ringWeightAt point rPrime coefficients =
      Spec.Pcs.RingSwitch.ringWeightAt point rPrime coefficients := by
  simp only [Model.Pcs.RingSwitch.ringWeightAt, Spec.Pcs.RingSwitch.ringWeightAt,
    Spec.Field.esquare, nativeKaratsuba_eq_emul]

theorem ringWeightAt_eq_spec :
    Model.Pcs.RingSwitch.ringWeightAt = Spec.Pcs.RingSwitch.ringWeightAt := by
  funext point rPrime coefficients
  exact ringWeightAt_refines point rPrime coefficients

theorem fold1b_refines (words : Array K) (weights : Array E) :
    Model.Pcs.RingSwitch.fold1b words weights =
      Spec.Pcs.RingSwitch.fold1b words weights := rfl

theorem transposeSlices_refines :
    Model.Pcs.RingSwitch.transposeSlices = Spec.Pcs.RingSwitch.transposeSlices := rfl

theorem batchedTarget_refines (slices challenges : Array E) :
    Model.Pcs.RingSwitch.batchedTarget slices challenges =
      Spec.Pcs.RingSwitch.batchedTarget slices challenges := by
  simp only [Model.Pcs.RingSwitch.batchedTarget, Spec.Pcs.RingSwitch.batchedTarget,
    Model.Pcs.RingSwitch.packingWidth, Spec.Pcs.RingSwitch.ringMap,
    applyComposed_eq_spec, nativeMulBase_eq_mulBase]

end LeanVmXmss.Proofs.Pcs.RingSwitch
