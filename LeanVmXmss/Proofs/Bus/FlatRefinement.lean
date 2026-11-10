import Model.Bus.Flat
import Proofs.Bus.Refinement

namespace LeanVmXmss.Proofs.Bus

open Spec.Field (K E zero one)
open LeanVmXmss.Model.Bus
open LeanVmXmss.Model.Field

theorem planarEadd_refines (a b : E) : planarEadd a b = Model.Field.eadd a b := by
  simp only [planarEadd, planarEadd0, planarEadd1, planarEadd2, Model.Field.eadd]

theorem planarEmul_refines (a b : E) : planarEmul a b = nativeKaratsuba a b := by
  simp only [planarEmul, planarEmul0, planarEmul1, planarEmul2, nativeKaratsuba]

theorem planarMulBase_refines (a : E) (k : K) :
    planarMulBase a k = nativeMulBase a k := by
  simp only [planarMulBase, planarMulBase0, planarMulBase1, planarMulBase2, nativeMulBase]

theorem decode_encode_planar_empty :
    decodePlanarE (encodePlanarE (#[] : Array E)) = #[] := by
  simp [decodePlanarE, encodePlanarE, planarEEmpty, Model.Pcs.Ntt.foldRange,
    Model.Pcs.Ntt.foldRangeLoop]

theorem eqTable_flat_refines_empty :
    decodePlanarE (eqTableFlat (#[] : Array E)) = eqTable #[] := rfl

theorem foldTable_flat_refines (state : Array (Array E)) (r : E) (half : Nat) :
    foldTableFlat state r half = foldTableState state r half := rfl

theorem proveBalance_flat_refines (gpows : Array K) (lay : Model.Layout.PublicLayout)
    (cols bcCols : Array (Array K)) (ps : ProverState) :
    proveBalanceFlat gpows lay cols bcCols ps = proveBalance gpows lay cols bcCols ps := rfl

theorem proveConstraints_flat_refines (airs : Array AirTable) (cols : Array (Array K))
    (zeta : Array E) (ps : ProverState) :
    proveConstraintsFlat airs cols zeta ps = proveConstraints airs cols zeta ps := rfl

theorem proveBus_flat_refines (program : Array Spec.Vm.Op) (iv : ByteArray)
    (publicInput : Array E) (bundle : Spec.Witness.WitnessBundle) :
    proveBusAndConstraintsFlat program iv publicInput bundle =
      proveBusAndConstraints program iv publicInput bundle := by
  simp only [proveBusAndConstraintsFlat]

end LeanVmXmss.Proofs.Bus
