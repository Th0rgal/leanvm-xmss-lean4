import Lean
import Spec.Field.Basic

open Lean Elab Command

def fieldName (name : Name) : Bool :=
  match name with
  | .anonymous => false
  | .str parent part => part == "LeanVmXmss" || fieldName parent
  | .num parent _ => fieldName parent

run_cmd do
  let env ← getEnv
  for (name, _) in env.constants.toList do
    if fieldName name then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless #[`propext, `Quot.sound].contains ax do
          throwError "Forbidden transitive dependency in {name}: {ax}"
      logInfo m!"INSTANCE_AUDIT {name}: {axioms}"
