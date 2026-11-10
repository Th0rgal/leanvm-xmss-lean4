import Lean
import Proofs.Field.NativeKernel
import Proofs.Field.NativeHighShift

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let some info := env.find? `LeanVmXmss.Proofs.Field.nativeClmulHi_correct
    | throwError "Missing refinement"
  let some value := info.value? true | throwError "Missing proof"
  for name in value.getUsedConstants do
    let deps ← Lean.collectAxioms name
    if deps.contains `Classical.choice then
      logInfo m!"CHOICE_DEP {name}"
  let deps ← Lean.collectAxioms `LeanVmXmss.Proofs.Field.nativeHighShift
  for dep in deps do
    unless #[`propext, `Quot.sound].contains dep do
      throwError "Forbidden high-shift dependency: {dep}"
  logInfo m!"HIGH_SHIFT_DEPS {deps}"
