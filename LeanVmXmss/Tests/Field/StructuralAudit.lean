import Lean
import Spec.Field.Basic

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if (name.toString.splitOn "LeanVmXmss").length > 1 then
      if info.isUnsafe || Lean.isExtern env name then
        throwError "Unsafe or external constant: {name}"
      let deps ← Lean.collectAxioms name
      for dep in deps do
        unless #[`propext, `Quot.sound].contains dep do
          throwError "Forbidden transitive dependency in {name}: {dep}"
      count := count + 1
  logInfo m!"STRUCTURAL_AUDIT checked={count} unsafe=0 extern=0"
