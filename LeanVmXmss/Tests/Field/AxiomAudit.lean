import Lean
import Proofs.Field.Windows
import Tests.Field.Witnesses
import Tests.Field.ToolProbe
import Model.Field.NativeKernel
import Proofs.Field.NativeKernel
import Proofs.Field.NativeHighShift

open Lean Elab Command

def fieldName (name : Name) : Bool :=
  match name with
  | .anonymous => false
  | .str parent part => part == "LeanVmXmss" || fieldName parent
  | .num parent _ => fieldName parent

run_cmd do
  let env ← getEnv
  let mut totalChecked : Nat := 0
  let mut theoremCount : Nat := 0
  let prefixes := #["LeanVmXmss.Spec.Field", "LeanVmXmss.Model.Field",
    "LeanVmXmss.Proofs.Field", "LeanVmXmss.Tests.Field"]
  let mut seen := #[false, false, false, false]
  for (name, info) in env.constants.toList do
    if (name.toString.splitOn "LeanVmXmss").length > 1 then
      if (name.toString.splitOn "_unsafe_rec").length > 1 then
        throwError "Forbidden compiler auxiliary name: {name}"
      if info.isUnsafe || Lean.isExtern env name then
        throwError "Unsafe or external constant: {name}"
      totalChecked := totalChecked + 1
      for i in [:prefixes.size] do
        if (name.toString.splitOn prefixes[i]!).length > 1 then
          seen := seen.set! i true
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless #[`propext, `Quot.sound].contains ax do
          throwError "Forbidden transitive dependency in {name}: {ax}"
      if info.isTheorem then
        theoremCount := theoremCount + 1
      logInfo m!"AXIOM_AUDIT {name}: {axioms}"
  for i in [:prefixes.size] do
    unless seen[i]! do throwError "Missing Field prefix: {prefixes[i]!}"
  if totalChecked < 400 then throwError "Incomplete constant inventory: {totalChecked}"
  if theoremCount < 120 then throwError "Incomplete theorem inventory: {theoremCount}"
  logInfo m!"AXIOM_AUDIT total_checked={totalChecked} theorem_count={theoremCount}"
