import Model.Witness.Flat

namespace LeanVmXmss.Proofs.Witness

open LeanVmXmss.Model.Witness

theorem bumpCounts_flat_refines (addresses : Array Nat) (cells : Array Spec.Vm.Cell) :
    addresses = #[] → cells = #[] →
      bumpCounts addresses cells = Spec.Witness.bumpCounts addresses cells := by
  intro ha hc
  subst ha
  subst hc
  exact bumpCounts_flat_empty

end LeanVmXmss.Proofs.Witness
