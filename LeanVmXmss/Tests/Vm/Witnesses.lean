import Proofs.Vm.Basic
import Proofs.Xmss.Basic
import Proofs.Xmss.Encoding
import Proofs.Vm.GPow
import Proofs.Vm.RuntimePowers
import Proofs.Vm.Kernel
import Proofs.Vm.Linear

namespace LeanVmXmss.Tests.Vm

open Spec.Vm
open scoped Spec.Vm

def writtenMemory : Memory := {cells := #[{word := Spec.Field.one, written := true}], used := 1}

def posWitness : Bool :=
  match writtenMemory.store 0 Spec.Field.one with
  | .ok m => (m.get 0).word == Spec.Field.one
  | .error _ => false

def negWitness : Bool :=
  match writtenMemory.store 0 Spec.Field.zero with
  | .error (.conflict ..) => true
  | _ => false

theorem positive_write_once : posWitness = true := by decide

theorem negative_conflict_mutant : negWitness = true := by decide

theorem negative_lane_mutant : Spec.Vm.KeccakInternal.cellLanes true 0 ≠ (some 0, some 1) := by decide

end LeanVmXmss.Tests.Vm
