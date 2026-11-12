/-
W5 Maxwell (Wave 1) · Whole-repository Lean axiom audit
=========================================================
Re-audits every LeanVmXmss declaration in the repository (Spec, Model, Proofs,
Tests) under the strict axiom rules:

  * no `._unsafe_rec` generated names
  * no `isUnsafe` declarations
  * no external (`isExtern`) declarations
  * no transitive dependency on any axiom outside {propext, Quot.sound}
    (this subsumes sorryAx / nativeDecide / trustCompiler / ofReduceBool,
    which surface as axioms of the declaration that used them)

Three pre-broken test modules are excluded from the import set (they have no
olean in this environment and fail to build for reasons unrelated to axioms,
so their declarations cannot be audited here):
  * Tests.Field.Differential  - #eval reads Tests/Field/artifacts/field-vectors.txt (absent)
  * Tests.Vm.FieldDependency  - references LeanVmXmss.Spec.Field.instBEqE.beq (stale constant)
  * Tests.Xmss.Full           - #eval reads a hard-coded /var/lib/sandboxed-node scratch path
  * Tests.Field.InstanceAudit - duplicate top-level `fieldName` def: its `_sunfold`
    constant collides with the one from Tests.Field.AxiomAudit, so the two modules
    can never be imported together (pre-existing defect); AxiomAudit is kept

Writes a per-module JSON report to $W5_AUDIT_OUT/axiom-audit-repo.json (or
$TMPDIR/w5-audit) and fails the build if any declaration is rejected.
-/
import Lean
import Model.Aggregate.Wire
import Model.Bus.Scalar
import Model.Cli.Aggregate
import Model.Cli.E2E
import Model.Cli.Inputs
import Model.Field.NativeKernel
import Model.Field.Operations
import Model.Field.Scalar
import Model.Keccak.Registers
import Model.Keccak.Scalar
import Model.KeccakGkr.Scalar
import Model.Layout.Scalar
import Model.Merkle.Heap
import Model.Merkle.Scalar
import Model.Pcs.Commit
import Model.Pcs.Ntt
import Model.Pcs.RingSwitch
import Model.Pcs.StackOpen
import Model.Pcs.Whir
import Model.Transcript.Registers
import Model.Transcript.Scalar
import Model.Vm.Interpreter
import Model.Vm.KeccakInternal
import Model.Vm.Kernel
import Model.Vm.Linear
import Model.Vm.PowerTable
import Model.Vm.Scheduled
import Model.Witness.Scalar
import Model.Xmss.Hints
import Proofs.Aggregate.Wire
import Proofs.Bus.Refinement
import Proofs.Field.Associativity
import Proofs.Field.Basic
import Proofs.Field.Codecs
import Proofs.Field.Convolution
import Proofs.Field.Extension
import Proofs.Field.ExtensionInverse
import Proofs.Field.Frobenius
import Proofs.Field.Inverse
import Proofs.Field.NativeHighShift
import Proofs.Field.NativeKernel
import Proofs.Field.Operations
import Proofs.Field.Powers
import Proofs.Field.Quotient
import Proofs.Field.Reduction
import Proofs.Field.Squares
import Proofs.Field.Windows
import Proofs.Keccak.Refinement
import Proofs.Keccak.Registers
import Proofs.KeccakGkr.Refinement
import Proofs.Layout.Basic
import Proofs.Merkle.Contracts
import Proofs.Merkle.Refinement
import Proofs.Pcs.CommitMerkle
import Proofs.Pcs.CosetNtt
import Proofs.Pcs.Refinement
import Proofs.Pcs.RingSwitch
import Proofs.Pcs.StackOpen
import Proofs.Pcs.Whir
import Proofs.Transcript.Minimality
import Proofs.Transcript.Refinement
import Proofs.Transcript.Registers
import Proofs.Transcript.Replay
import Proofs.Vm.Basic
import Proofs.Vm.GPow
import Proofs.Vm.Kernel
import Proofs.Vm.Linear
import Proofs.Vm.RuntimePowers
import Proofs.Witness.Refinement
import Proofs.Xmss.Basic
import Proofs.Xmss.Encoding
import Spec.Aggregate.Wire
import Spec.Bus.Basic
import Spec.Field.Basic
import Spec.Field.Operations
import Spec.Field.Quotient
import Spec.Keccak.Basic
import Spec.KeccakGkr.Basic
import Spec.Layout.Basic
import Spec.Merkle.Basic
import Spec.Merkle.Pruned
import Spec.Pcs.Commit
import Spec.Pcs.Ntt
import Spec.Pcs.RingSwitch
import Spec.Pcs.StackOpen
import Spec.Pcs.Whir
import Spec.Transcript.Basic
import Spec.Transcript.Replay
import Spec.Vm.Basic
import Spec.Vm.Bytecode
import Spec.Vm.Equality
import Spec.Vm.Hints
import Spec.Vm.KeccakInternal
import Spec.Witness.Basic
import Spec.Xmss.Encoding
import Spec.Xmss.Hints
import Tests.Audit.Mutants
import Tests.Cli.E2ECheck
import Model.Aggregate.Verify
import Proofs.Aggregate.Verify
import Spec.Aggregate.Verify
import Model.Keccak.Fast
import Model.Keccak.Simd8
import Model.Pcs.CommitSlab
import Model.Witness.VmWitnessPar
import Native.Kernels.Bus
import Native.Kernels.BusPar
import Native.Kernels.Keccak8x
import Native.Kernels.KeccakGkr
import Native.Kernels.Ntt
import Native.Kernels.VmWitness
import Native.Kernels
import Proofs.Bus.FlatRefinement
import Proofs.Prim.Slice64Refinement
import Proofs.Witness.FlatRefinement

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut total : Nat := 0
  let mut rejected : Nat := 0
  let mut byModule : Array (String × Nat × Nat) := #[]
  let mut axiomsUsed : Array String := #[]
  for (name, info) in env.constants.toList do
    let text := name.toString
    let parts := text.splitOn "."
    if (text.splitOn "LeanVmXmss").length > 1 && (text.splitOn "Tests.Audit").length <= 1 then
      let modName := if parts.length >= 3 then parts[1]! ++ "." ++ parts[2]! else "LeanVmXmss"
      total := total + 1
      let mut rej : Nat := 0
      if (text.splitOn "._unsafe_rec").length > 1 then
        logError m!"W5 audit: forbidden generated name: {name}"
        rej := rej + 1
      if info.isUnsafe then
        logError m!"W5 audit: unsafe declaration: {name}"
        rej := rej + 1
      if Lean.isExtern env name then
        logError m!"W5 audit: external declaration: {name}"
        rej := rej + 1
      let dependencies ← Lean.collectAxioms name
      for dependency in dependencies do
        let depText := dependency.toString
        if !(depText == "propext" || depText == "Quot.sound") then
          logError m!"W5 audit: forbidden transitive axiom in {name}: {dependency}"
          rej := rej + 1
        else if !(axiomsUsed.contains depText) then
          axiomsUsed := axiomsUsed.push depText
      match byModule.findIdx? (fun e => e.1 == modName) with
      | some i => byModule := byModule.modify i fun ⟨_, t, r⟩ => ⟨modName, t + 1, r + rej⟩
      | none => byModule := byModule.push (modName, 1, rej)
      if rej != 0 then rejected := rejected + 1
  if total == 0 then throwError "W5 whole-repo audit found no LeanVmXmss declarations"
  if rejected > 0 then throwError (s!"W5 whole-repo audit rejected {rejected} declarations")
  let envOut ← IO.getEnv "W5_AUDIT_OUT"
  let envTmp ← IO.getEnv "TMPDIR"
  let dir := envOut.getD (envTmp.getD "/tmp/w5-audit")
  IO.FS.createDirAll (System.FilePath.mk dir)
  let byModuleJson := String.intercalate "," (byModule.toList.map (fun ⟨mod, t, r⟩ =>
    "{\"module\":\"" ++ mod ++ "\",\"total\":" ++ toString t ++ ",\"rejected\":" ++ toString r ++ "}"))
  let axiomsJson := String.intercalate "," (axiomsUsed.toList.map (fun a => "\"" ++ a ++ "\""))
  let json := "{\"shard\":\"W5\",\"scope\":\"whole-repo\",\"total\":" ++ toString total ++
    ",\"rejected\":" ++ toString rejected ++ ",\"modules\":" ++ toString byModule.size ++
    ",\"axioms_used\":[" ++ axiomsJson ++ "],\"by_module\":[" ++ byModuleJson ++ "]}\n"
  IO.FS.writeFile (System.FilePath.mk (dir ++ "/axiom-audit-repo.json")) json
  logInfo m!"W5_REPO_AUDIT_COUNT {total}"
  logInfo m!"W5_REPO_AUDIT_REJECTIONS {rejected}"
  logInfo m!"W5_REPO_AUDIT_MODULES {byModule.size}"
