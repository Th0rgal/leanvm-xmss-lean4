import Lean
import Tests.Transcript.Witnesses
import Proofs.Keccak.Registers
import Proofs.Transcript.Registers
import Proofs.Transcript.Minimality
import Model.Merkle.Heap
import Spec.Merkle.Pruned
import Spec.Transcript.Replay
import Tests.Keccak.Witnesses
import Tests.Merkle.Witnesses
import Tests.Transcript.Differential
import Proofs.Transcript.Replay
import Proofs.Merkle.Contracts
import Tests.Merkle.Pruned
import Tests.Transcript.Mutants
import Tests.Keccak.ImportedNative
import Tests.Keccak.NativeRefinement

open Lean Elab Command

def hasLeanVmXmss : Name → Bool
  | .str p s => s == "LeanVmXmss" || hasLeanVmXmss p
  | .num p _ => hasLeanVmXmss p
  | .anonymous => false

def isShardBName : Name → Bool
  | .str p s =>
    ((s == "Keccak" || s == "Transcript" || s == "Merkle") &&
      match p with
      | .str q top => (top == "Spec" || top == "Model" || top == "Proofs" || top == "Tests") &&
          hasLeanVmXmss q
      | _ => false) || isShardBName p
  | .num p _ => isShardBName p
  | .anonymous => false

run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  let mut fieldFailureCount : Nat := 0
  let mut shardCount : Nat := 0
  let mut passedCount : Nat := 0
  let mut unsafeCount : Nat := 0
  let mut externalRuntimeCount : Nat := 0
  let mut failures : Array Name := #[]
  for (name, info) in env.constants.toList do
    if hasLeanVmXmss name then
      if isShardBName name then shardCount := shardCount + 1
      let axioms ← Lean.collectAxioms name
      let mut permitted := true
      if let .str _ "_unsafe_rec" := name then
        externalRuntimeCount := externalRuntimeCount + 1
        permitted := false
        failures := failures.push name
        logInfo m!"FORBIDDEN_GENERATED_RUNTIME {name}: unsafe={info.isUnsafe} extern={Lean.isExtern env name}"
      if Lean.isExtern env name || info.isUnsafe then
        permitted := false
        unsafeCount := unsafeCount + 1
        failures := failures.push name
        logInfo m!"FORBIDDEN_DECLARATION_FLAGS {name}: unsafe={info.isUnsafe} extern={Lean.isExtern env name}"
      for ax in axioms do
        unless #[`propext, `Quot.sound].contains ax do
          permitted := false
          failures := failures.push name
          logInfo m!"FORBIDDEN_TRANSITIVE {name}: {ax}"
          if (`LeanVmXmss.Spec.Field).isPrefixOf name then
            fieldFailureCount := fieldFailureCount + 1
            logInfo m!"EXTERNAL_FIELD_DIAGNOSTIC {name}: {ax}"
      if permitted then passedCount := passedCount + 1
      count := count + 1
  if count < 100 then throwError "Incomplete declaration inventory: {count}"
  logInfo m!"AXIOM_AUDIT_COUNT {count}"
  logInfo m!"SHARD_B_AUDIT_COUNT {shardCount}"
  logInfo m!"STRICT_WHITELIST_COVERAGE {passedCount}/{count}"
  logInfo m!"EXTERNAL_FIELD_FAILURE_COUNT {fieldFailureCount}"
  logInfo m!"UNSAFE_REC_COUNT {unsafeCount}"
  logInfo m!"EXTERNAL_GENERATED_RUNTIME_COUNT {externalRuntimeCount}"
  if !failures.isEmpty then throwError "Forbidden transitive dependencies: {failures.size}"
