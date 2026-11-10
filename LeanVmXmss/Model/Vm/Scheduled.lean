import Model.Vm.Interpreter
import Spec.Vm.Hints

namespace LeanVmXmss.Model.Vm

open Spec.Vm

def scheduledRun (fuel : Nat) (program : Array Op) (hints : Array (Array RHint)) (r : Runtime) : Except Fault Runtime :=
  Nat.rec (motive := fun _ => Runtime → Except Fault Runtime) (fun _ => .error .stepLimit)
    (fun _ previous r =>
    if r.state.pc+1 == program.size && r.state.fp == 0 then .ok r
    else match program[r.state.pc]? with
      | none => .error .badProgram
      | some op => match applyHints (hints[r.state.pc]?.getD #[]) r with
        | .error fault => .error fault
        | .ok ⟨ready, streams⟩ => match step op ready with
          | .error fault => .error fault
          | .ok state => previous ⟨state, streams⟩) fuel r

end LeanVmXmss.Model.Vm
