import Lean
import Proofs.Field.Windows
import Tests.Field.Witnesses
import Tests.Field.ToolProbe
import Model.Field.NativeKernel
import Proofs.Field.NativeKernel
import Proofs.Field.NativeHighShift

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut total : Nat := 0
  let mut unsafeCount : Nat := 0
  let mut externCount : Nat := 0
  let mut theoremCount : Nat := 0
  let mut auxiliaryCount : Nat := 0
  for (name, info) in env.constants.toList do
    if (name.toString.splitOn "LeanVmXmss").length > 1 then
      total := total + 1
      if info.isTheorem then theoremCount := theoremCount + 1
      if info.isUnsafe then unsafeCount := unsafeCount + 1
      if Lean.isExtern env name then externCount := externCount + 1
       if (name.toString.splitOn "_unsafe_rec").length > 1 then
        auxiliaryCount := auxiliaryCount + 1
        logInfo m!"COMPILER_AUX {name} unsafe={info.isUnsafe} extern={Lean.isExtern env name}"
      let deps ← Lean.collectAxioms name
      for dep in deps do
        unless #[`propext, `Quot.sound].contains dep do
          throwError "Forbidden dependency in {name}: {dep}"
  logInfo m!"COMPILER_INVENTORY total={total} theorems={theoremCount} unsafe={unsafeCount} extern={externCount} unsafe_rec={auxiliaryCount}"
