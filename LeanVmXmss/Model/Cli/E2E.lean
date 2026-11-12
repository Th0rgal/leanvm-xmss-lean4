import Model.Cli.Inputs
import Model.Bus.Flat
import Model.Witness.Flat
import Model.KeccakGkr.Flat
import Model.Pcs.FlatWhir
import Model.Aggregate.Wire

namespace LeanVmXmss.Model.Cli

open Spec.Field (E)
open Spec.Vm

def bytecodePointWidth : Nat := 23

def ivOfCols (program : Array Op) (bytecodeCols : Array (Array Spec.Field.K)) : ByteArray :=
  let logBytecode := Spec.Witness.log2FloorPow2 program.size
  Model.Layout.fiatShamirIvFast (Model.Layout.stackBytecodeColumnsFast logBytecode bytecodeCols)

def ivOf (program : Array Op) : ByteArray :=
  ivOfCols program (Model.Layout.bytecodeColumnsFast program)

def specStateOf (ps : Model.Bus.ProverState) : Spec.Transcript.ProverState :=
  ⟨Model.Transcript.Registers.toSpec ps.sponge, ps.stream, #[]⟩

def stackPointsOf (stage : Model.KeccakGkr.KeccakGkrStageOutput) :
    Array Spec.Pcs.StackOpen.StackClaim :=
  stage.slotClaims.map fun sc => .point sc.offset sc.lowPoint sc.value

def phaseOf (phaseBytes : ByteArray) : IO Spec.Merkle.PrunedMerklePaths := do
  match Spec.Aggregate.Wire.Cursor.phase ⟨phaseBytes, 0⟩ with
  | some (phase, cursor) =>
    if decide (cursor.pos = phaseBytes.size) then return phase
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

def proveBusAndConstraintsFlatWithBcCols (program : Array Op) (iv : ByteArray)
    (publicInput : Array E) (bundle : Spec.Witness.WitnessBundle)
    (bcCols : Array (Array Spec.Field.K)) : Model.Bus.BusStageOutput :=
  let ps0 := Model.Bus.startTranscript iv publicInput bundle.sized bundle.root
  let cols := Model.Bus.buildColumnsFlat program bundle.sized bundle.message
  let gpows := Model.Layout.gpowTable (Model.Bus.maxBusGpowIndex program bundle.sized)
  let (bus, ps1) := Model.Bus.proveBalanceFlat gpows bundle.sized.layout cols bcCols ps0
  let (xi, ps2) := Model.Bus.sampleChallenge ps1
  let airs := Model.Bus.buildAirs bundle.sized.layout.taus bus xi
  let (tableClaims, ps3) := Model.Bus.proveConstraintsFlat airs cols bus.point ps2
  let (rPi, ps4) := Model.Bus.sampleChallenge ps3
  let slots := Model.Bus.finishClaims bundle.sized.layout publicInput bus.claims tableClaims rPi
  let outClaim := Model.Bus.keccakOutputClaim tableClaims
  ⟨ps4, slots, outClaim⟩

def proveBusAndConstraintsWqWithBcCols (program : Array Op) (iv : ByteArray)
    (publicInput : Array E) (sized : Spec.Witness.SizedRun) (root : ByteArray)
    (wq : ByteArray) (wins : Array (Array Spec.Field.K))
    (bcCols : Array (Array Spec.Field.K)) : Model.Bus.BusStageOutput :=
  let ps0 := Model.Bus.startTranscript iv publicInput sized root
  let cols := Model.Bus.buildColumnsFlatWq program sized wq wins
  let gpows := Model.Layout.gpowTable (Model.Bus.maxBusGpowIndex program sized)
  let (bus, ps1) := Model.Bus.proveBalanceFlat gpows sized.layout cols bcCols ps0
  let (xi, ps2) := Model.Bus.sampleChallenge ps1
  let airs := Model.Bus.buildAirs sized.layout.taus bus xi
  let (tableClaims, ps3) := Model.Bus.proveConstraintsFlat airs cols bus.point ps2
  let (rPi, ps4) := Model.Bus.sampleChallenge ps3
  let slots := Model.Bus.finishClaims sized.layout publicInput bus.claims tableClaims rPi
  let outClaim := Model.Bus.keccakOutputClaim tableClaims
  ⟨ps4, slots, outClaim⟩

def proveKeccakGkrOnlyFlat (bus : Model.Bus.BusStageOutput)
    (bundle : Spec.Witness.WitnessBundle) (wq : ByteArray) :
    IO Model.KeccakGkr.KeccakGkrStageOutput := do
  let executed := bundle.sized.rows[Spec.Layout.opKeccak]?.getD 0
  let qBase := (bundle.sized.layout.placements[Spec.Layout.qKeccak]?.join).map
    Spec.Layout.Placement.index |>.getD 0
  let reduced ← Model.KeccakGkr.proveReductionFlat bus.ps wq executed bus.keccakOutput qBase
  let extra :=
    match reduced.1.outputs with
    | none => #[]
    | some opening => #[⟨qBase, opening.point, opening.value⟩]
  pure ⟨reduced.2, bus.slotClaims ++ extra,
    ⟨qBase, reduced.1.inputs.point, reduced.1.inputs.slices⟩, reduced.1⟩

def proveKeccakGkrOnlyWq (bus : Model.Bus.BusStageOutput) (executed qBase : Nat)
    (wq : ByteArray) : IO Model.KeccakGkr.KeccakGkrStageOutput := do
  let reduced ← Model.KeccakGkr.proveReductionFlat bus.ps wq executed bus.keccakOutput qBase
  let extra :=
    match reduced.1.outputs with
    | none => #[]
    | some opening => #[⟨qBase, opening.point, opening.value⟩]
  pure ⟨reduced.2, bus.slotClaims ++ extra,
    ⟨qBase, reduced.1.inputs.point, reduced.1.inputs.slices⟩, reduced.1⟩

def proveKeccakGkrStageFlat (program : Array Op) (iv : ByteArray) (publicInput : Array E)
    (bundle : Spec.Witness.WitnessBundle) (wq : ByteArray) :
    IO Model.KeccakGkr.KeccakGkrStageOutput := do
  let bus := Model.Bus.proveBusAndConstraintsFlat program iv publicInput bundle
  proveKeccakGkrOnlyFlat bus bundle wq

def assembleWqK4 (program : Array Op) (trace : Spec.Witness.ExecutionTrace) :
    IO (Spec.Witness.SizedRun × ByteArray × Array (Array Spec.Field.K)) := do
  let sized := Spec.Witness.sizeRun program trace
  let maxC := max (Spec.Witness.maxNatArray trace.bytecodeCount)
    (Spec.Witness.maxCellAccesses trace.memory)
  let g := Model.Vm.growLinear trace.g (max trace.memUsed (max program.size maxC))
  let kr := trace.tables[5]?.getD #[]
  let kh := (sized.layout.taus.map Spec.Witness.pow2)[5]?.getD 1
  let gTasks ← (Array.range 7).mapM fun grp =>
    IO.asTask (prio := .dedicated) <| IO.lazyPure fun () =>
      Model.Witness.fillTablesGroup grp program sized g
  let qTasks ← (Array.range 16).mapM fun p =>
    IO.asTask (prio := .dedicated) <| IO.lazyPure fun () =>
      Model.Witness.fillQKeccakChunk program kr trace.memory
        (p * kr.size / 16) ((p + 1) * kr.size / 16)
  let lTasks ← (Array.range 3).mapM fun l =>
    IO.asTask (prio := .dedicated) <| IO.lazyPure fun () =>
      Model.Witness.memLimbBytes trace.memory.cells
        (min sized.cells trace.memory.used) l
  let mut qChunks := #[]
  for t in qTasks do
    match ← IO.wait t with
    | .ok c => qChunks := qChunks.push c
    | .error e => throw e
  let mut wins := (Array.replicate Spec.Layout.nColumns #[]).setIfInBounds Spec.Layout.qKeccak
    (Model.Witness.assembleQKeccak kr.size kh qChunks)
  for t in gTasks do
    let part ← match ← IO.wait t with
    | .ok w => pure w
    | .error e => throw e
    wins := Model.Pcs.Ntt.foldRange Spec.Layout.nColumns (fun a i =>
      let c := part[i]?.getD #[]
      if c.isEmpty then a else a.set! i c) wins
  let mut limbs := #[]
  for t in lTasks do
    match ← IO.wait t with
    | .ok c => limbs := limbs.push c
    | .error e => throw e
  let wq := Model.Witness.stackWqK4 sized wins
    (limbs[0]?.getD ByteArray.empty) (limbs[1]?.getD ByteArray.empty)
    (limbs[2]?.getD ByteArray.empty)
  return (sized, wq, wins)

def commitWitnessSplit (iv : ByteArray) (publicInput : Array E)
    (sized : Spec.Witness.SizedRun) (message : Array Spec.Field.K) (wq : ByteArray) :
    IO Spec.Witness.WitnessBundle := do
  let sh := sized.layout.shape
  let root ← Model.Witness.commitRootWqPar wq sh.nLanes
    (sh.mu - Spec.Layout.logBatch) Spec.Witness.logInvRateDefault
  let pair := Spec.Witness.challengePair iv publicInput sized root
  return ⟨sized, message, root, Spec.Witness.announceDigest sized, pair.1, pair.2⟩

def proveVmRunCore (computeMemoryKeccak : Bool) (fuel : Nat) (program : Array Op) (frame : Nat)
    (schedule : Array (Array RHint)) (publicInput : Array E)
    (streams : Array Stream) (logInvRate : Nat) : IO VmProvedRun := do
  let state ← liftFault (Model.Vm.initial frame publicInput program.size)
  let iv := ivOf program
  let trace ← liftFault
    (Model.Witness.executeTraceFlat fuel program schedule ⟨state, streams⟩)
  unless decide (trace.unconstrained = 0) do throw (IO.userError "unconstrained reads")
  let initInput := #[Spec.Witness.cellWord state.memory 0, Spec.Witness.cellWord state.memory 1]
  let (bundle, wq) ← Model.Witness.bundleFlatParallel program iv initInput trace
  let stage ← proveKeccakGkrStageFlat program iv initInput bundle wq
  let ps0 := specStateOf stage.ps
  let points := stackPointsOf stage
  let ring : Spec.Pcs.StackOpen.RingSwitchOpen :=
    ⟨stage.ringClaim.offset, #[⟨stage.ringClaim.suffixPoint, stage.ringClaim.slices⟩]⟩
  let mu := bundle.sized.layout.shape.mu
  let ps1 ← match Model.Pcs.FlatWhir.provePcsOpenFlat ps0 mu logInvRate wq points ring with
    | some ps => pure ps
    | none => throw (IO.userError "provePcsOpenFlat failed")
  let phases ← decodePhases ps1.merkle
  let memHash :=
    if computeMemoryKeccak then
      Model.Xmss.hashFast (serializeUsedMemory trace.memory.cells trace.memUsed)
    else
      ByteArray.empty
  return {
    proof := ⟨ps1.stream, phases⟩
    cycles := trace.cycles
    memUsed := trace.memUsed
    memoryKeccak := memHash
    stage := stage
    mu := mu }

def proveVmRun (fuel : Nat) (program : Array Op) (frame : Nat)
    (schedule : Array (Array RHint)) (publicInput : Array E)
    (streams : Array Stream) (logInvRate : Nat) : IO VmProvedRun :=
  proveVmRunCore true fuel program frame schedule publicInput streams logInvRate

def signatureClaimsOf (raw : Array Spec.Xmss.RawSignature) :
    Array Spec.Aggregate.Wire.SignaturePair :=
  (signersOf raw).map fun record => ⟨record.publicKey, record.message⟩

def ethereumProofOf (claims : Array Spec.Aggregate.Wire.SignaturePair)
    (bytecodeValue : E) (proof : Spec.Aggregate.Wire.VmProof) :
    Spec.Aggregate.Wire.EthereumProof :=
  { claims := ⟨claims, #[]⟩
    daRoot := none
    defer := ⟨Array.replicate bytecodePointWidth Spec.Field.zero, bytecodeValue⟩
    proof := proof }

def verifySignatureFast (raw : Spec.Xmss.RawSignature) : Bool :=
  Model.Xmss.verifySignatureFast raw

def verifyAllSignatures (raw : Array Spec.Xmss.RawSignature) : IO Unit := do
  let n := raw.size
  if decide (n = 0) then return ()
  let tasks ← (Array.range 16).mapM fun p =>
    IO.asTask (prio := .dedicated) <| IO.lazyPure fun () =>
      let lo := p * n / 16
      let hi := (p + 1) * n / 16
      Model.Pcs.Ntt.foldRange (hi - lo)
        (fun ok j =>
          ok &&
            match raw[lo + j]? with
            | some record => verifySignatureFast record
            | none => true)
        true
  for task in tasks do
    match ← IO.wait task with
    | .ok true => pure ()
    | .ok false => throw (IO.userError "Lean signature verification failed")
    | .error e => throw e

def scalarPairBytes (pair : E × E) : ByteArray :=
  Spec.Xmss.writeLE pair.1.c0 8 ++ Spec.Xmss.writeLE pair.1.c1 8 ++
    Spec.Xmss.writeLE pair.2.c0 8 ++ Spec.Xmss.writeLE pair.2.c1 8

def matchPrefixAt (raw pat : ByteArray) (pos : Nat) : Bool :=
  decide (pos + pat.size <= raw.size) &&
    Model.Pcs.Ntt.foldRange pat.size
      (fun ok j =>
        ok && decide ((raw[pos + j]?.getD 0).toNat = (pat[j]?.getD 0).toNat))
      true

def parseDigitsAt (raw : ByteArray) (start : Nat) : Nat :=
  let skipped := Model.Pcs.Ntt.foldRange (raw.size - start)
    (fun idx _ =>
      let b := (raw[idx]?.getD 0).toNat
      if decide (b = 32) || decide (b = 9) then idx + 1 else idx)
    start
  let (_, val) := Model.Pcs.Ntt.foldRange (raw.size - skipped)
    (fun (done, acc) off =>
      if done then (true, acc)
      else
        let b := (raw[skipped + off]?.getD 0).toNat
        if decide (b >= 48) && decide (b <= 57) then (false, acc * 10 + (b - 48))
        else (true, acc))
    (false, 0)
  val

def extractProcKbBytes (raw : ByteArray) (key : String) : Nat :=
  let pat := key.toUTF8
  let found := Model.Pcs.Ntt.foldRange raw.size
    (fun acc i =>
      match acc with
      | some _ => acc
      | none =>
        if (decide (i = 0) || decide ((raw[i - 1]?.getD 0).toNat = 10)) &&
            matchPrefixAt raw pat i then
          some (parseDigitsAt raw (i + pat.size) * 1024)
        else none)
    none
  found.getD 0

def readProcMemBytes : IO (Nat × Nat) := do
  let raw ← IO.FS.readBinFile ⟨"/proc/self/status"⟩
  return (extractProcKbBytes raw "VmRSS:", extractProcKbBytes raw "VmHWM:")

structure PhaseTimings where
  statementHints : Nat := 0
  executeWitness : Nat := 0
  commitNttMerkle : Nat := 0
  busConstraints : Nat := 0
  keccakGkr : Nat := 0
  pcsOpen : Nat := 0
  wireEncode : Nat := 0
  total : Nat := 0
  vmRssBytes : Nat := 0
  vmHwmBytes : Nat := 0
  rssStatementHints : Nat := 0
  rssExecuteWitness : Nat := 0
  rssCommitNttMerkle : Nat := 0
  rssBusConstraints : Nat := 0
  rssKeccakGkr : Nat := 0
  rssPcsOpen : Nat := 0
  rssWireEncode : Nat := 0
  deriving Inhabited

def phaseTimingsJson (passIdx : Nat) (t : PhaseTimings) : String :=
  "{\"pass\":" ++ toString passIdx ++ "," ++
    "\"phases_nanos\":{" ++
    "\"0b_statement_hints\":" ++ toString t.statementHints ++ "," ++
    "\"1_execute_witness\":" ++ toString t.executeWitness ++ "," ++
    "\"2_commit_ntt_merkle\":" ++ toString t.commitNttMerkle ++ "," ++
    "\"3_bus_constraints\":" ++ toString t.busConstraints ++ "," ++
    "\"4_keccak_gkr\":" ++ toString t.keccakGkr ++ "," ++
    "\"5_pcs_open\":" ++ toString t.pcsOpen ++ "," ++
    "\"6_wire_encode\":" ++ toString t.wireEncode ++ "}," ++
    "\"total_nanos\":" ++ toString t.total ++ "," ++
    "\"vm_rss_bytes\":" ++ toString t.vmRssBytes ++ "," ++
    "\"vm_hwm_bytes\":" ++ toString t.vmHwmBytes ++ "," ++
    "\"phase_rss_bytes\":{" ++
    "\"0b_statement_hints\":" ++ toString t.rssStatementHints ++ "," ++
    "\"1_execute_witness\":" ++ toString t.rssExecuteWitness ++ "," ++
    "\"2_commit_ntt_merkle\":" ++ toString t.rssCommitNttMerkle ++ "," ++
    "\"3_bus_constraints\":" ++ toString t.rssBusConstraints ++ "," ++
    "\"4_keccak_gkr\":" ++ toString t.rssKeccakGkr ++ "," ++
    "\"5_pcs_open\":" ++ toString t.rssPcsOpen ++ "," ++
    "\"6_wire_encode\":" ++ toString t.rssWireEncode ++ "}}"

def encodeScalarsLE (xs : Array E) : ByteArray :=
  Model.Pcs.Ntt.foldRange xs.size
    (fun acc i =>
      let w := xs[i]?.getD Spec.Field.zero
      pushWordLE (pushWordLE (pushWordLE acc w.c0) w.c1) w.c2)
    (ByteArray.emptyWithCapacity (24 * xs.size))

def encodeNatArrayLE (xs : Array Nat) : ByteArray :=
  Model.Pcs.Ntt.foldRange xs.size
    (fun acc i => pushWordLE acc (UInt64.ofNat (xs[i]?.getD 0)))
    (ByteArray.emptyWithCapacity (8 * xs.size))

def exportShardFixtures (dir : System.FilePath) (iv : ByteArray) (publicInput : Array E)
    (hints : Array Spec.Xmss.HintEntry) (sized : Spec.Witness.SizedRun) (root : ByteArray)
    (wq : ByteArray) (bus : Model.Bus.BusStageOutput) (stage : Model.KeccakGkr.KeccakGkrStageOutput)
    (proof : Spec.Aggregate.Wire.VmProof) (wire : ByteArray) : IO Unit := do
  let k1 := childPath dir "K1"
  let k2 := childPath dir "K2"
  let k3 := childPath dir "K3"
  let k4 := childPath dir "K4"
  IO.FS.createDirAll k1
  IO.FS.createDirAll k2
  IO.FS.createDirAll k3
  IO.FS.createDirAll k4
  let piBytes := encodeScalarsLE publicInput
  let tausBytes := encodeNatArrayLE sized.layout.taus
  let rowsBytes := encodeNatArrayLE sized.rows
  IO.FS.writeBinFile (childPath k4 "iv.bin") iv
  IO.FS.writeBinFile (childPath k4 "public-input.bin") piBytes
  IO.FS.writeBinFile (childPath k4 "hints.bin") (encodeHints hints)
  IO.FS.writeBinFile (childPath k4 "expected-root.bin") root
  let wqHash := Model.Xmss.hashFast wq
  IO.FS.writeBinFile (childPath k4 "expected-wq-keccak256.bin") wqHash
  IO.FS.writeBinFile (childPath k1 "iv.bin") iv
  IO.FS.writeBinFile (childPath k1 "public-input.bin") piBytes
  IO.FS.writeBinFile (childPath k1 "root.bin") root
  IO.FS.writeBinFile (childPath k1 "taus.bin") tausBytes
  IO.FS.writeBinFile (childPath k1 "rows.bin") rowsBytes
  let busStream := encodeScalarsLE bus.ps.stream
  let busHash := Model.Xmss.hashFast busStream
  IO.FS.writeBinFile (childPath k1 "expected-bus-stream.bin") busStream
  IO.FS.writeBinFile (childPath k1 "expected-bus-keccak256.bin") busHash
  let qWin := Model.Witness.qKeccakWindowWq sized wq
  let outClaimPt := encodeScalarsLE
    (bus.keccakOutput.instancePoint ++ bus.keccakOutput.lanes)
  let gkrStream := encodeScalarsLE stage.ps.stream
  let gkrHash := Model.Xmss.hashFast gkrStream
  IO.FS.writeBinFile (childPath k2 "q-keccak-window.bin") qWin
  IO.FS.writeBinFile (childPath k2 "keccak-output-claim.bin") outClaimPt
  IO.FS.writeBinFile (childPath k2 "expected-stage-stream.bin") gkrStream
  IO.FS.writeBinFile (childPath k2 "expected-stage-keccak256.bin") gkrHash
  IO.FS.writeBinFile (childPath k3 "wq.bin") wq
  IO.FS.writeBinFile (childPath k3 "expected-root.bin") root
  let vmProofBytes := Spec.Aggregate.Wire.putProof ByteArray.empty proof
  let vmProofHash := Model.Xmss.hashFast vmProofBytes
  let wireHash := Model.Xmss.hashFast wire
  IO.FS.writeBinFile (childPath k3 "expected-vm-proof.bin") vmProofBytes
  IO.FS.writeBinFile (childPath k3 "expected-vm-proof-keccak256.bin") vmProofHash
  let manifest :=
    "{\"committed_words\":" ++ toString (wq.size / 8) ++ "," ++
    "\"wq_bytes\":" ++ toString wq.size ++ "," ++
    "\"mu\":" ++ toString sized.layout.shape.mu ++ "," ++
    "\"n_lanes\":" ++ toString sized.layout.shape.nLanes ++ "," ++
    "\"keccak_rows\":" ++ toString (sized.rows[Spec.Layout.opKeccak]?.getD 0) ++ "," ++
    "\"root_hex\":\"" ++ hex root ++ "\"," ++
    "\"wq_keccak256\":\"" ++ hex wqHash ++ "\"," ++
    "\"bus_stream_keccak256\":\"" ++ hex busHash ++ "\"," ++
    "\"gkr_stream_keccak256\":\"" ++ hex gkrHash ++ "\"," ++
    "\"vm_proof_keccak256\":\"" ++ hex vmProofHash ++ "\"," ++
    "\"eth_wire_keccak256\":\"" ++ hex wireHash ++ "\"}\n"
  IO.FS.writeFile (childPath dir "manifest.json") manifest

def proveLeafEthereumFast (program : Array Op) (frame : Nat)
    (schedule : Array (Array RHint)) (seed : ByteArray) (bytecodeValue : E)
    (signers : Array Spec.Xmss.RawSignature) (logInvRate : Nat) (statement : ByteArray)
    (hints : Array Spec.Xmss.HintEntry) (iv : ByteArray)
    (bcCols : Array (Array Spec.Field.K)) (fuel : Nat := 10000000) :
    IO (Spec.Aggregate.Wire.EthereumProof × VmProvedRun) := do
  let streams := streamsOfHints hints
  let publicInput := #[Spec.Xmss.packCell statement, Spec.Xmss.packCell statement 16]
  let state ← liftFault (Model.Vm.initial frame publicInput program.size)
  let trace ← liftFault
    (Model.Witness.executeTraceFlat fuel program schedule ⟨state, streams⟩)
  unless decide (trace.unconstrained = 0) do throw (IO.userError "unconstrained reads")
  let traceCycles := trace.cycles
  let traceMemUsed := trace.memUsed
  let initInput := #[Spec.Witness.cellWord state.memory 0, Spec.Witness.cellWord state.memory 1]
  let (sized, wq, wins) ← assembleWqK4 program trace
  let sh := sized.layout.shape
  let root ← Model.Witness.commitRootWqPar wq sh.nLanes (sh.mu - Spec.Layout.logBatch)
    Spec.Witness.logInvRateDefault
  let executed := sized.rows[Spec.Layout.opKeccak]?.getD 0
  let qBase := (sized.layout.placements[Spec.Layout.qKeccak]?.join).map
    Spec.Layout.Placement.index |>.getD 0
  let mu := sh.mu
  let bus := proveBusAndConstraintsWqWithBcCols program iv initInput sized root wq wins bcCols
  let stage ← proveKeccakGkrOnlyWq bus executed qBase wq
  let ps0 := specStateOf stage.ps
  let points := stackPointsOf stage
  let ring : Spec.Pcs.StackOpen.RingSwitchOpen :=
    ⟨stage.ringClaim.offset, #[⟨stage.ringClaim.suffixPoint, stage.ringClaim.slices⟩]⟩
  let ps1 ← match Model.Pcs.FlatWhir.provePcsOpenFlat ps0 mu logInvRate wq points ring with
    | some ps => pure ps
    | none => throw (IO.userError "provePcsOpenFlat failed")
  let phases ← decodePhases ps1.merkle
  let claims := signers.map fun record => ⟨record.publicKey, record.message⟩
  unless Model.Aggregate.Wire.signerSetOk ⟨claims, #[]⟩ do
    throw (IO.userError "signer set failed strict order check")
  let eth := ethereumProofOf claims bytecodeValue ⟨ps1.stream, phases⟩
  let seedPair : E × E := (Spec.Xmss.packCell seed, Spec.Xmss.packCell seed 16)
  let wireStatement := scalarPairBytes (Model.Aggregate.Wire.EthereumProof.statement seedPair eth)
  unless bytesEqFast wireStatement statement do
    throw (IO.userError "EthereumProof statement mismatch against workload statement")
  let run : VmProvedRun := {
    proof := ⟨ps1.stream, phases⟩
    cycles := traceCycles
    memUsed := traceMemUsed
    memoryKeccak := ByteArray.empty
    stage := stage
    mu := mu }
  return (eth, run)

def proveLeafEthereumTimedPass (program : Array Op) (frame : Nat)
    (schedule : Array (Array RHint)) (seed : ByteArray) (bytecodeValue : E)
    (records : Array Spec.Xmss.RawSignature) (logInvRate : Nat) (iv : ByteArray)
    (bcCols : Array (Array Spec.Field.K)) (exportDir : Option System.FilePath := none)
    (fuel : Nat := 10000000) :
    IO (Spec.Aggregate.Wire.EthereumProof × ByteArray × Nat × VmProvedRun ×
      ByteArray × PhaseTimings) := do
  let t0 ← IO.monoNanosNow
  let (signers, hints) ← verifyAndHintsParallel seed records bytecodeValue
  let statement := Model.Xmss.statementDigest seed signers bytecodeValue
  let streams := streamsOfHints hints
  let t0b ← IO.monoNanosNow
  let (rss0b, _) ← readProcMemBytes
  let publicInput := #[Spec.Xmss.packCell statement, Spec.Xmss.packCell statement 16]
  let state ← liftFault (Model.Vm.initial frame publicInput program.size)
  let trace ← liftFault
    (Model.Witness.executeTraceFlat fuel program schedule ⟨state, streams⟩)
  unless decide (trace.unconstrained = 0) do throw (IO.userError "unconstrained reads")
  let traceCycles := trace.cycles
  let traceMemUsed := trace.memUsed
  let initInput := #[Spec.Witness.cellWord state.memory 0, Spec.Witness.cellWord state.memory 1]
  let (sized, wq, wins) ← assembleWqK4 program trace
  let t1 ← IO.monoNanosNow
  let (rss1, _) ← readProcMemBytes
  let sh := sized.layout.shape
  let root ← Model.Witness.commitRootWqPar wq sh.nLanes (sh.mu - Spec.Layout.logBatch)
    Spec.Witness.logInvRateDefault
  let t2 ← IO.monoNanosNow
  let (rss2, _) ← readProcMemBytes
  let executed := sized.rows[Spec.Layout.opKeccak]?.getD 0
  let qBase := (sized.layout.placements[Spec.Layout.qKeccak]?.join).map
    Spec.Layout.Placement.index |>.getD 0
  let mu := sh.mu
  let bus := proveBusAndConstraintsWqWithBcCols program iv initInput sized root wq wins bcCols
  let t3 ← IO.monoNanosNow
  let (rss3, _) ← readProcMemBytes
  let stage ← proveKeccakGkrOnlyWq bus executed qBase wq
  let t4 ← IO.monoNanosNow
  let (rss4, _) ← readProcMemBytes
  let ps0 := specStateOf stage.ps
  let points := stackPointsOf stage
  let ring : Spec.Pcs.StackOpen.RingSwitchOpen :=
    ⟨stage.ringClaim.offset, #[⟨stage.ringClaim.suffixPoint, stage.ringClaim.slices⟩]⟩
  let ps1 ← match Model.Pcs.FlatWhir.provePcsOpenFlat ps0 mu logInvRate wq points ring with
    | some ps => pure ps
    | none => throw (IO.userError "provePcsOpenFlat failed")
  let phases ← decodePhases ps1.merkle
  let claims := signers.map fun record => ⟨record.publicKey, record.message⟩
  unless Model.Aggregate.Wire.signerSetOk ⟨claims, #[]⟩ do
    throw (IO.userError "signer set failed strict order check")
  let eth := ethereumProofOf claims bytecodeValue ⟨ps1.stream, phases⟩
  let seedPair : E × E := (Spec.Xmss.packCell seed, Spec.Xmss.packCell seed 16)
  let wireStatement := scalarPairBytes (Model.Aggregate.Wire.EthereumProof.statement seedPair eth)
  unless bytesEqFast wireStatement statement do
    throw (IO.userError "EthereumProof statement mismatch against workload statement")
  let t5 ← IO.monoNanosNow
  let (rss5, _) ← readProcMemBytes
  let wire := Model.Aggregate.Wire.EthereumProof.toBytesWithoutPubkeys eth
  let t6 ← IO.monoNanosNow
  let (rss6, hwm6) ← readProcMemBytes
  if let some dir := exportDir then
    exportShardFixtures dir iv initInput hints sized root wq bus stage ⟨ps1.stream, phases⟩ wire
  let timings : PhaseTimings := {
    statementHints := t0b - t0
    executeWitness := t1 - t0b
    commitNttMerkle := t2 - t1
    busConstraints := t3 - t2
    keccakGkr := t4 - t3
    pcsOpen := t5 - t4
    wireEncode := t6 - t5
    total := t5 - t0
    vmRssBytes := rss6
    vmHwmBytes := hwm6
    rssStatementHints := rss0b
    rssExecuteWitness := rss1
    rssCommitNttMerkle := rss2
    rssBusConstraints := rss3
    rssKeccakGkr := rss4
    rssPcsOpen := rss5
    rssWireEncode := rss6 }
  let run : VmProvedRun := {
    proof := ⟨ps1.stream, phases⟩
    cycles := traceCycles
    memUsed := traceMemUsed
    memoryKeccak := ByteArray.empty
    stage := stage
    mu := mu }
  return (eth, statement, hints.size, run, wire, timings)

def proveLeafEthereumCore (alreadyVerified : Bool) (program : Array Op) (frame : Nat)
    (schedule : Array (Array RHint)) (seed : ByteArray) (bytecodeValue : E)
    (records : Array Spec.Xmss.RawSignature) (logInvRate : Nat) (statement : ByteArray)
    (hints : Array Spec.Xmss.HintEntry) (fuel : Nat := 10000000) :
    IO (ByteArray × Nat × VmProvedRun) := do
  unless alreadyVerified do
    verifyAllSignatures records
  let bcCols := Model.Layout.bytecodeColumnsFast program
  let iv := ivOfCols program bcCols
  let signers := signersOf records
  let (eth, run) ← proveLeafEthereumFast program frame schedule seed bytecodeValue signers
    logInvRate statement hints iv bcCols fuel
  let wire := Model.Aggregate.Wire.EthereumProof.toBytesWithoutPubkeys eth
  let proofBytes := Model.Aggregate.Wire.EthereumProof.proofSize eth
  return (wire, proofBytes, run)

def proveLeafEthereum (program : Array Op) (frame : Nat) (schedule : Array (Array RHint))
    (seed : ByteArray) (bytecodeValue : E) (records : Array Spec.Xmss.RawSignature)
    (logInvRate : Nat) (statement : ByteArray) (hints : Array Spec.Xmss.HintEntry)
    (fuel : Nat := 10000000) : IO (ByteArray × Nat × VmProvedRun) :=
  proveLeafEthereumCore false program frame schedule seed bytecodeValue records logInvRate
    statement hints fuel

end LeanVmXmss.Model.Cli
