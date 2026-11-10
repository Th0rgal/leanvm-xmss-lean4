import Lean
import Spec.Pcs.Ntt
import Spec.Pcs.Commit
import Model.Pcs.Ntt
import Model.Pcs.Commit
import Proofs.Pcs.Refinement
import Proofs.Pcs.CommitMerkle
import Proofs.Pcs.CosetNtt

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  let mut rejected : Nat := 0
  for (name, info) in env.constants.toList do
    let text := name.toString
    if (text.splitOn "LeanVmXmss").length > 1 && (text.splitOn "Pcs").length > 1 then
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
  if count == 0 then throwError "Empty Pcs declaration inventory"
  if rejected > 0 then throwError "Strict Pcs audit rejected {rejected} declarations"
  logInfo m!"PCS_STRICT_AUDIT_COUNT {count}"
  logInfo m!"PCS_STRICT_AUDIT_REJECTIONS {rejected}"
