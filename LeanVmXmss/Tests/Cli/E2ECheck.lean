import Model.Cli.Aggregate
import Model.Witness.Scalar

namespace LeanVmXmss.Tests.Cli.E2ECheck

open LeanVmXmss.Model.Cli
open Spec.Field (E)
open Spec.Vm

def setK (offset value : Nat) : Op := .set offset ⟨UInt64.ofNat value, 0, 0⟩

def padPow2 (ops : Array Op) : Array Op :=
  let target := max 2 (1 <<< Spec.Layout.log2Ceil (ops.size + 1))
  let padded := Model.Pcs.Ntt.foldRange (target - 1 - ops.size)
    (fun acc _ => acc.push (setK 0 0)) ops
  padded.push (.xor 0 0 0)

def syntheticCase (name : String) : IO (Array Op × Nat) :=
  match name with
  | "syn_tiny" =>
    pure (padPow2 #[setK 2 5, setK 3 9, .xor 2 3 4, setK 5 7, .mul 4 5 6,
      setK 8 1, setK 9 0, setK 10 0], 16)
  | "syn_jump" =>
    pure (padPow2 #[setK 2 1, setK 3 32, setK 4 1, .jump 2 3 4, setK 5 9,
      setK 6 0, setK 7 1, .jump 6 7 4], 16)
  | "syn_deref" =>
    pure (padPow2 #[setK 2 64, setK 3 11, .deref 2 0 3 .cell, .deref 2 1 0 .pc,
      .deref 2 2 0 .fp, setK 12 0, setK 13 0, setK 14 0], 16)
  | "syn_keccak" =>
    pure (padPow2 #[setK 2 0x1111, setK 3 0x2222, setK 4 0, setK 5 0, setK 6 0,
      setK 7 0, setK 8 0, setK 9 0, setK 10 0, setK 11 0, setK 12 0,
      setK 13 0, setK 14 0, .keccak #[2, 3, 4, 5] 6 10 11 16 false true,
      .keccak #[16, 17, 18, 19] 20 24 25 30 true false], 64)
  | other => throw (IO.userError s!"unknown synthetic case: {other}")

def proveSynMode (name outPath : String) (logInvRate : Nat := 1) : IO Unit := do
  let (program, frame) ← syntheticCase name
  let schedule := Array.replicate program.size #[]
  let publicInput := #[Spec.Field.zero, Spec.Field.zero]
  let t0 ← IO.monoMsNow
  let run ← proveVmRun 100 program frame schedule publicInput #[] logInvRate
  let ms := (← IO.monoMsNow) - t0
  let bytes := Spec.Aggregate.Wire.putProof ByteArray.empty run.proof
  IO.FS.writeBinFile (⟨outPath⟩ : System.FilePath) bytes
  IO.println (s!"E2E_VM_PROOF|case={name}|path={outPath}|bytes={bytes.size}" ++
    s!"|stream={run.proof.stream.size}|merkle={run.proof.merkle.size}" ++
    s!"|mu={run.mu}|cycles={run.cycles}|ms={ms}")

def natEq (a b : Nat) : Bool := decide (a = b)

def u64ArrayEq (xs ys : Array UInt64) : Bool :=
  natEq xs.size ys.size &&
    Model.Pcs.Ntt.foldRange xs.size
      (fun ok i => ok && natEq (xs[i]?.getD 0).toNat (ys[i]?.getD 0).toNat) true

def wordArrayEq (xs ys : Array E) : Bool :=
  natEq xs.size ys.size &&
    Model.Pcs.Ntt.foldRange xs.size
      (fun ok i =>
        ok && Spec.Vm.wordBEq (xs[i]?.getD Spec.Field.zero) (ys[i]?.getD Spec.Field.zero)) true

def bytesEq (xs ys : ByteArray) : Bool :=
  natEq xs.size ys.size &&
    Model.Pcs.Ntt.foldRange xs.size
      (fun ok i => ok && natEq (xs[i]?.getD 0).toNat (ys[i]?.getD 0).toNat) true

def bytesArrayEq (xs ys : Array ByteArray) : Bool :=
  natEq xs.size ys.size &&
    Model.Pcs.Ntt.foldRange xs.size
      (fun ok i =>
        ok && bytesEq (xs[i]?.getD ByteArray.empty) (ys[i]?.getD ByteArray.empty)) true

def checkPrepcsMode (name prepcsPath : String) : IO Unit := do
  let (program, frame) ← syntheticCase name
  let schedule := Array.replicate program.size #[]
  let publicInput := #[Spec.Field.zero, Spec.Field.zero]
  let state ← liftFault (Model.Vm.initial frame publicInput program.size)
  let iv := ivOf program
  let trace ← liftFault (Model.Witness.executeTrace 100 program schedule ⟨state, #[]⟩)
  let initInput := #[Spec.Witness.cellWord state.memory 0, Spec.Witness.cellWord state.memory 1]
  let bundle := Model.Witness.bundleOf program iv initInput trace
  let stage := Model.KeccakGkr.proveKeccakGkr program iv initInput bundle
  let ps0 := specStateOf stage.ps
  let raw ← IO.FS.readBinFile (⟨prepcsPath⟩ : System.FilePath)
  let c0 : Spec.Aggregate.Wire.Cursor := ⟨raw, 0⟩
  let some (ivB, c1) := Spec.Aggregate.Wire.Cursor.take c0 32
    | throw (IO.userError "prepcs iv")
  let some (piB, c2) := Spec.Aggregate.Wire.Cursor.take c1 32
    | throw (IO.userError "prepcs pi")
  let some (nOps, c3) := Spec.Aggregate.Wire.Cursor.usize c2
    | throw (IO.userError "prepcs ops len")
  let some (opsB, c4) := Spec.Aggregate.Wire.Cursor.take c3 nOps
    | throw (IO.userError "prepcs ops")
  let some (nStream, c5) := Spec.Aggregate.Wire.Cursor.usize c4
    | throw (IO.userError "prepcs stream len")
  let some (stream, _) :=
    Spec.Aggregate.Wire.Cursor.repeat nStream Spec.Aggregate.Wire.Cursor.elem c5
    | throw (IO.userError "prepcs stream")
  let replay := opsB.data.foldl (fun (ps, idx) op =>
    if natEq op.toNat 0 then
      (Spec.Transcript.addScalar ps (stream.getD idx Spec.Field.zero), idx + 1)
    else
      ((Spec.Transcript.sample ps).2, idx)) (Spec.Transcript.proverNew ivB piB, 0)
  unless natEq replay.2 stream.size do
    throw (IO.userError "prepcs replay stream cursor mismatch")
  let replayed := replay.1
  unless u64ArrayEq ps0.sponge.state replayed.sponge.state do
    throw (IO.userError "ps0 sponge state mismatch against prepcs replay")
  unless natEq ps0.sponge.pending replayed.sponge.pending do
    throw (IO.userError "ps0 sponge pending mismatch against prepcs replay")
  unless wordArrayEq ps0.stream replayed.stream do
    throw (IO.userError "ps0 stream mismatch against prepcs replay")
  unless bytesArrayEq ps0.merkle replayed.merkle do
    throw (IO.userError "ps0 merkle mismatch against prepcs replay")
  IO.println (s!"E2E_PREPCS_BRIDGE|PASS|case={name}|stream={ps0.stream.size}" ++
    s!"|pending={ps0.sponge.pending}|ops={opsB.size}")

def permuteInputsMode (srcDir dstDir : String) : IO Unit := do
  let src : System.FilePath := ⟨srcDir⟩
  let dst : System.FilePath := ⟨dstDir⟩
  IO.FS.createDirAll dst
  let raw ← loadRawInputs (childPath src "xmss-inputs.bin")
  let permuted := (raw.drop 1 |>.append (raw.take 1)).reverse
  let encoded := permuted.foldl
    (fun acc r => acc ++ r.publicKey ++ r.message ++ r.signature)
    (ByteArray.emptyWithCapacity (permuted.size * Spec.Xmss.recordSize))
  IO.FS.writeBinFile (childPath dst "xmss-inputs.bin") encoded
  for name in ["seed.bin", "bytecode-value.bin", "bytecode.bin", "schedule.bin"] do
    let bytes ← IO.FS.readBinFile (childPath src name)
    IO.FS.writeBinFile (childPath dst name) bytes
  IO.println s!"E2E_PERMUTE_INPUTS|PASS|src={srcDir}|dst={dstDir}|records={permuted.size}"

def runMain (args : List String) : IO Unit := do
  let mode := args.head?.getD "usage"
  match mode with
  | "prove-syn" =>
    match args[1]?, args[2]? with
    | some name, some outPath => proveSynMode name outPath
    | _, _ => throw (IO.userError "usage: e2e-check prove-syn <case> <out-proof>")
  | "check-prepcs" =>
    match args[1]?, args[2]? with
    | some name, some prepcsPath => checkPrepcsMode name prepcsPath
    | _, _ => throw (IO.userError "usage: e2e-check check-prepcs <case> <prepcs-path>")
  | "permute-inputs" =>
    match args[1]?, args[2]? with
    | some srcDir, some dstDir => permuteInputsMode srcDir dstDir
    | _, _ => throw (IO.userError "usage: e2e-check permute-inputs <src-dir> <dst-dir>")
  | "aggregate" => aggregateMain args.tail
  | other => throw (IO.userError s!"unknown mode: {other}")

end LeanVmXmss.Tests.Cli.E2ECheck

def main (args : List String) : IO Unit :=
  LeanVmXmss.Tests.Cli.E2ECheck.runMain args
