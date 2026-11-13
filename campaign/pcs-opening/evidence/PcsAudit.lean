import Lean
import Spec.Pcs.RingSwitch
import Spec.Pcs.StackOpen
import Spec.Pcs.Whir
import Spec.Aggregate.Wire
import Model.Pcs.RingSwitch
import Model.Pcs.StackOpen
import Model.Pcs.Whir
import Model.Aggregate.Wire

import Model.Pcs.FlatWhir
import Native.Kernels.Ntt
import Native.Kernels.Keccak8x

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  let mut rejected : Nat := 0
  let owned (text : String) : Bool :=
    text.startsWith "LeanVmXmss.Model.Pcs.FlatWhir." ||
    text.startsWith "LeanVmXmss.Model.Pcs.Ntt." ||
    text.startsWith "LeanVmXmss.Model.Pcs.Commit." ||
    text.startsWith "LeanVmXmss.Native.Kernels.Ntt." ||
    text.startsWith "LeanVmXmss.Native.Kernels.Keccak8x."
  for (name, info) in env.constants.toList do
    let text := name.toString
    if owned text then
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
  if count == 0 then throwError "Empty Whir declaration inventory"
  if rejected > 0 then throwError "Strict Whir audit rejected {rejected} declarations"
  logInfo m!"WHIR_STRICT_AUDIT_COUNT {count}"
  logInfo m!"WHIR_STRICT_AUDIT_REJECTIONS {rejected}"
