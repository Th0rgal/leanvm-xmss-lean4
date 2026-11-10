import Lean
import Spec.Witness.Basic
import Model.Witness.Scalar
import Proofs.Witness.Refinement

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  let mut rejected : Nat := 0
  for (name, info) in env.constants.toList do
    let text := name.toString
    if (text.splitOn "LeanVmXmss").length > 1 && (text.splitOn "Witness").length > 1 then
      if (text.splitOn "._unsafe_rec").length > 1 then
        logError m!"Forbidden generated name: {name}"
        rejected := rejected + 1
      if info.isUnsafe then
        logError m!"Unsafe declaration: {name}"
        rejected := rejected + 1
      if Lean.isExtern env name then
        logError m!"External declaration: {name}"
        rejected := rejected + 1
      let dependencies ← Lean.collectAxioms name
      for dependency in dependencies do
        unless #[`propext, `Quot.sound].contains dependency do
          logError m!"Forbidden transitive dependency in {name}: {dependency}"
          rejected := rejected + 1
      count := count + 1
  if count == 0 then throwError "Empty Witness declaration inventory"
  if rejected > 0 then throwError "Strict Witness audit rejected {rejected} declarations"
  logInfo m!"WITNESS_STRICT_AUDIT_COUNT {count}"
  logInfo m!"WITNESS_STRICT_AUDIT_REJECTIONS {rejected}"
