import Model.Cli.Inputs
import Model.Witness.Scalar
import Model.KeccakGkr.Scalar
import Model.Pcs.Whir
import Model.Aggregate.Wire

namespace LeanVmXmss.Model.Cli

open Spec.Field (E)
open Spec.Vm

def bytecodePointWidth : Nat := 23

def ivOf (program : Array Op) : ByteArray :=
  let columns := Model.Layout.bytecodeColumnsFast program
  let logBytecode := Spec.Witness.log2FloorPow2 program.size
  Model.Layout.fiatShamirIvFast (Model.Layout.stackBytecodeColumnsFast logBytecode columns)

def specStateOf (ps : Model.Bus.ProverState) : Spec.Transcript.ProverState :=
  ⟨Model.Transcript.Registers.toSpec ps.sponge, ps.stream, #[]⟩

def stackPointsOf (stage : Model.KeccakGkr.KeccakGkrStageOutput) :
    Array Spec.Pcs.StackOpen.StackClaim :=
  stage.slotClaims.map fun sc => .point sc.offset sc.lowPoint sc.value

def phaseOf (phaseBytes : ByteArray) : IO Spec.Merkle.PrunedMerklePaths := do
  match Spec.Aggregate.Wire.Cursor.phase ⟨phaseBytes, 0⟩ with
  | some (phase, cursor) =>
    if cursor.pos == phaseBytes.size then return phase
    else throw (IO.userError "merkle phase has trailing bytes")
  | none => throw (IO.userError "merkle phase did not decode")

def decodePhases (merkle : Array ByteArray) : IO (Array Spec.Merkle.PrunedMerklePaths) :=
  Model.Pcs.Ntt.foldRange merkle.size
    (fun acc idx => do
      let list ← acc
      let phase ← phaseOf (merkle[idx]?.getD ByteArray.empty)
      pure (list.push phase))
    (pure (Array.emptyWithCapacity merkle.size))

def pushWordLE (bytes : ByteArray) (value : UInt64) : ByteArray :=
  bytes.push value.toUInt8
    |>.push (value >>> 8).toUInt8
    |>.push (value >>> 16).toUInt8
    |>.push (value >>> 24).toUInt8
    |>.push (value >>> 32).toUInt8
    |>.push (value >>> 40).toUInt8
    |>.push (value >>> 48).toUInt8
    |>.push (value >>> 56).toUInt8

def serializeUsedMemory (cells : Array Cell) (used : Nat) : ByteArray :=
  Model.Pcs.Ntt.foldRange used
    (fun bytes idx =>
      let word := (Model.Vm.cellAt cells idx).word
      pushWordLE (pushWordLE (pushWordLE bytes word.c0) word.c1) word.c2)
    (ByteArray.emptyWithCapacity (used * 24))

structure VmProvedRun where
  proof : Spec.Aggregate.Wire.VmProof
  cycles : Nat
  memUsed : Nat
  memoryKeccak : ByteArray
  stage : Model.KeccakGkr.KeccakGkrStageOutput
  mu : Nat
  deriving Inhabited

def proveVmRun (fuel : Nat) (program : Array Op) (frame : Nat)
    (schedule : Array (Array RHint)) (publicInput : Array E)
    (streams : Array Stream) (logInvRate : Nat) : IO VmProvedRun := do
  let state ← liftFault (Model.Vm.initial frame publicInput program.size)
  let iv := ivOf program
  let trace ← liftFault
    (Model.Witness.executeTrace fuel program schedule ⟨state, streams⟩)
  unless trace.unconstrained == 0 do throw (IO.userError "unconstrained reads")
  let initInput := #[Spec.Witness.cellWord state.memory 0, Spec.Witness.cellWord state.memory 1]
  let bundle := Model.Witness.bundleOf program iv initInput trace
  let stage := Model.KeccakGkr.proveKeccakGkr program iv initInput bundle
  let ps0 := specStateOf stage.ps
  let points := stackPointsOf stage
  let ring : Spec.Pcs.StackOpen.RingSwitchOpen :=
    ⟨stage.ringClaim.offset, #[⟨stage.ringClaim.suffixPoint, stage.ringClaim.slices⟩]⟩
  let mu := bundle.sized.layout.shape.mu
  let ps1 ← match Model.Pcs.Whir.provePcsOpen ps0 mu logInvRate bundle.message points ring with
    | some ps => pure ps
    | none => throw (IO.userError "provePcsOpen failed")
  let phases ← decodePhases ps1.merkle
  let memBytes := serializeUsedMemory trace.memory.cells trace.memUsed
  return {
    proof := ⟨ps1.stream, phases⟩
    cycles := trace.cycles
    memUsed := trace.memUsed
    memoryKeccak := Spec.Vm.KeccakInternal.hash memBytes
    stage := stage
    mu := mu }

def signatureClaimsOf (raw : Array Spec.Xmss.RawSignature) :
    Array Spec.Aggregate.Wire.SignaturePair :=
  (Spec.Xmss.sortedUnique raw).map fun record => ⟨record.publicKey, record.message⟩

def ethereumProofOf (claims : Array Spec.Aggregate.Wire.SignaturePair)
    (bytecodeValue : E) (proof : Spec.Aggregate.Wire.VmProof) :
    Spec.Aggregate.Wire.EthereumProof :=
  { claims := ⟨claims, #[]⟩
    daRoot := none
    defer := ⟨Array.replicate bytecodePointWidth Spec.Field.zero, bytecodeValue⟩
    proof := proof }

def verifyAllSignatures (raw : Array Spec.Xmss.RawSignature) : IO Unit :=
  Model.Pcs.Ntt.foldRange raw.size
    (fun acc idx => do
      acc
      match raw[idx]? with
      | some record =>
        unless Spec.Xmss.verifySignature record do
          throw (IO.userError "Lean signature verification failed")
      | none => pure ())
    (pure ())

def scalarPairBytes (pair : E × E) : ByteArray :=
  Spec.Xmss.writeLE pair.1.c0 8 ++ Spec.Xmss.writeLE pair.1.c1 8 ++
    Spec.Xmss.writeLE pair.2.c0 8 ++ Spec.Xmss.writeLE pair.2.c1 8

def proveLeafEthereum (program : Array Op) (frame : Nat) (schedule : Array (Array RHint))
    (seed : ByteArray) (bytecodeValue : E) (records : Array Spec.Xmss.RawSignature)
    (logInvRate : Nat) (statement : ByteArray) (hints : Array Spec.Xmss.HintEntry)
    (fuel : Nat := 10000000) : IO (ByteArray × VmProvedRun) := do
  verifyAllSignatures records
  let streams := streamsOfHints hints
  let publicInput := #[Spec.Xmss.packCell statement, Spec.Xmss.packCell statement 16]
  let run ← proveVmRun fuel program frame schedule publicInput streams logInvRate
  let claims := signatureClaimsOf records
  unless Model.Aggregate.Wire.signerSetOk ⟨claims, #[]⟩ do
    throw (IO.userError "signer set failed strict order check")
  let eth := ethereumProofOf claims bytecodeValue run.proof
  let seedPair : E × E := (Spec.Xmss.packCell seed, Spec.Xmss.packCell seed 16)
  let wireStatement := scalarPairBytes (Model.Aggregate.Wire.EthereumProof.statement seedPair eth)
  unless wireStatement == statement do
    throw (IO.userError "EthereumProof statement mismatch against workload statement")
  let wire := Model.Aggregate.Wire.EthereumProof.toBytesWithoutPubkeys eth
  return (wire, run)

end LeanVmXmss.Model.Cli
