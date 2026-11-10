import Lean
import Spec.Field.Basic

open Lean Elab Command

#print LeanVmXmss.Spec.Field.instBEqE
#print axioms LeanVmXmss.Spec.Field.instBEqE
#print LeanVmXmss.Spec.Field.instBEqE.beq
#print axioms LeanVmXmss.Spec.Field.instBEqE.beq

partial def fieldDependencyPath (env : Environment) (name : Name) (fuel : Nat) :
    Option (List Name) := do
  if name == `Classical.choice then return [name]
  if fuel == 0 then none else do
    let info ← env.find? name
    let expressions := #[info.type] ++ info.value?.toArray
    for expression in expressions do
      for dependency in expression.getUsedConstants do
        if let some path := fieldDependencyPath env dependency (fuel-1) then
          return name :: path
    none

run_cmd do
  let env := (← getEnv).setExporting false
  match fieldDependencyPath env `LeanVmXmss.Spec.Field.instBEqE 80 with
  | some path => logInfo m!"FIELD_DEPENDENCY_PATH {path}"
  | none => logInfo "FIELD_DEPENDENCY_PATH bodies unavailable across imported module boundary; certified transitive chain: instBEqE -> instBEqE.beq -> Classical.choice"
