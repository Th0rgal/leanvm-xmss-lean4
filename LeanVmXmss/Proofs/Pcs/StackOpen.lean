import Model.Pcs.StackOpen
import Proofs.Pcs.RingSwitch

namespace LeanVmXmss.Proofs.Pcs.StackOpen

open Spec.Field (E)

theorem value_refines :
    Model.Pcs.StackOpen.StackClaim.value = Spec.Pcs.StackOpen.StackClaim.value := rfl

theorem span_refines :
    Model.Pcs.StackOpen.StackClaim.span = Spec.Pcs.StackOpen.StackClaim.span := rfl

theorem aligned_refines :
    Model.Pcs.StackOpen.aligned = Spec.Pcs.StackOpen.aligned := rfl

theorem within_refines :
    Model.Pcs.StackOpen.within = Spec.Pcs.StackOpen.within := rfl

theorem eqEval_refines (left right : Array E) :
    Model.Pcs.StackOpen.eqEval left right = Spec.Pcs.StackOpen.eqEval left right := by
  simp only [Model.Pcs.StackOpen.eqEval, Spec.Pcs.StackOpen.eqEval,
    RingSwitch.nativeKaratsuba_eq_emul]

theorem eqEval_eq_spec :
    Model.Pcs.StackOpen.eqEval = Spec.Pcs.StackOpen.eqEval := by
  funext left right
  exact eqEval_refines left right

theorem indexBits_refines :
    Model.Pcs.StackOpen.indexBits = Spec.Pcs.StackOpen.indexBits := rfl

theorem eqAbove_refines (p : Spec.Pcs.StackOpen.Placement) (full : Array E) :
    Model.Pcs.StackOpen.eqAbove p full = Spec.Pcs.StackOpen.eqAbove p full := by
  simp only [Model.Pcs.StackOpen.eqAbove, Spec.Pcs.StackOpen.eqAbove, eqEval_eq_spec, indexBits_refines]
  split
  · have hsize : (full.extract p.variables full.size).size = full.size - p.variables := by
      simp [Array.size_extract]
    rw [hsize]
  · rfl

theorem place_refines (p : Spec.Pcs.StackOpen.Placement) (low full : Array E) :
    Model.Pcs.StackOpen.place p low full = Spec.Pcs.StackOpen.place p low full := by
  simp only [Model.Pcs.StackOpen.place, Spec.Pcs.StackOpen.place, eqEval_eq_spec,
    eqAbove_refines, RingSwitch.nativeKaratsuba_eq_emul]

theorem ringWeight_refines (point challenges full : Array E) :
    Model.Pcs.StackOpen.ringWeight point challenges full =
      Spec.Pcs.StackOpen.ringWeight point challenges full := by
  simp only [Model.Pcs.StackOpen.ringWeight, Spec.Pcs.StackOpen.ringWeight,
    RingSwitch.frobeniusCoefficients_refines, RingSwitch.ringWeightAt_eq_spec]

theorem batch_refines (lambda : E) (weights values : Array E) :
    Model.Pcs.StackOpen.batch lambda weights values =
      Spec.Pcs.StackOpen.batch lambda weights values := by
  simp only [Model.Pcs.StackOpen.batch, Spec.Pcs.StackOpen.batch,
    RingSwitch.nativeKaratsuba_eq_emul]

theorem openingTarget_refines (lambda : E) (values : Array E) :
    Model.Pcs.StackOpen.openingTarget lambda values =
      Spec.Pcs.StackOpen.openingTarget lambda values := by
  simp only [Model.Pcs.StackOpen.openingTarget, Spec.Pcs.StackOpen.openingTarget, batch_refines]

theorem prepareRing_refines :
    Model.Pcs.StackOpen.prepareRing = Spec.Pcs.StackOpen.prepareRing := rfl

theorem finishRing_refines :
    Model.Pcs.StackOpen.finishRing = Spec.Pcs.StackOpen.finishRing := rfl

theorem stackedTarget_refines :
    Model.Pcs.StackOpen.stackedTarget = Spec.Pcs.StackOpen.stackedTarget := rfl

end LeanVmXmss.Proofs.Pcs.StackOpen
