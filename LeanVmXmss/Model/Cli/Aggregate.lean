import Model.Cli.Inputs
import Model.Cli.E2E
import Model.Vm.Flat

namespace LeanVmXmss.Model.Cli

open Spec.Xmss Spec.Vm

structure AggregateContext where
  program : Array Op
  frame : Nat
  schedule : Array (Array RHint)
  seed : ByteArray
  bytecodeValue : Spec.Field.E
  records : Array RawSignature
  logInvRate : Nat
  bytecodeCols : Array (Array Spec.Field.K)
  iv : ByteArray

structure ProofArtifact where
  prover : String
  logInvRate : Nat
  records : Nat
  signers : Nat
  hintEntries : Nat
  statement : ByteArray
  hintsKeccak : ByteArray
  cycles : Option Nat
  memoryCells : Option Nat
  memoryKeccak : ByteArray
  wireBytes : ByteArray := ByteArray.empty
  proofSize : Option Nat := none
  ethProof : Option Spec.Aggregate.Wire.EthereumProof := none
  deriving Inhabited

abbrev AggregateProverFn :=
  AggregateContext → Array RawSignature → ByteArray → Array HintEntry → IO ProofArtifact

def pushWord (bytes : ByteArray) (value : UInt64) : ByteArray :=
  bytes.push value.toUInt8
    |>.push (value >>> 8).toUInt8
    |>.push (value >>> 16).toUInt8
    |>.push (value >>> 24).toUInt8
    |>.push (value >>> 32).toUInt8
    |>.push (value >>> 40).toUInt8
    |>.push (value >>> 48).toUInt8
    |>.push (value >>> 56).toUInt8

def serializeMemory (cells : Array Cell) (used : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.emptyWithCapacity (used * 24)
  for i in [:used] do
    let x := (Model.Vm.cellAt cells i).word
    bytes := pushWord bytes x.c0
    bytes := pushWord bytes x.c1
    bytes := pushWord bytes x.c2
  return bytes

def vmProverMaxRecords : Nat := 16384

def vmWitnessProver (fuel : Nat := 100000000) : AggregateProverFn :=
    fun ctx signers statement hints => do
  if ctx.records.size > vmProverMaxRecords then
    throw (IO.userError s!"vm prover is for fixtures of at most {vmProverMaxRecords} records")
  let encoded := encodeHints hints
  let streams := streamsOfHints hints
  let state ← liftFault (Model.Vm.initial ctx.frame #[packCell statement, packCell statement 16]
    ctx.program.size)
  let fs0 : Model.Vm.Flat.FlatState :=
    ⟨Model.Vm.Flat.flatOf state.memory, state.pc, state.fp, state.nextFree, state.g,
      state.cycles, state.opcodeCounts⟩
  let (fs, _) ← liftFault
    (Model.Vm.Flat.scheduledRunFlat fuel ctx.program ctx.schedule fs0 streams)
  let mem := Model.Vm.Flat.toMemory fs.m
  unless mem.unconstrainedReads.isEmpty do throw (IO.userError "unconstrained reads")
  let memory := serializeMemory mem.cells mem.used
  return {
    prover := "vm-witness", logInvRate := ctx.logInvRate,
    records := ctx.records.size, signers := signers.size,
    hintEntries := hints.size, statement, hintsKeccak := Model.Xmss.hashFast encoded,
    cycles := some fs.cycles, memoryCells := some mem.used,
    memoryKeccak := Model.Xmss.hashFast memory }

def stubProver : AggregateProverFn := fun ctx signers statement hints => do
  return {
    prover := "stub", logInvRate := ctx.logInvRate,
    records := ctx.records.size, signers := signers.size,
    hintEntries := hints.size, statement,
    hintsKeccak := hashEncodedHints hints,
    cycles := none, memoryCells := none,
    memoryKeccak := ByteArray.empty }

def runStubPass (ctx : AggregateContext) : IO (ProofArtifact × Nat) := do
  let t0 ← IO.monoNanosNow
  let signers := signersOf ctx.records
  let statement := Model.Xmss.statementDigest ctx.seed signers ctx.bytecodeValue
  let seedCells := #[packCell ctx.seed, packCell ctx.seed 16]
  let (hintEntries, hintsKeccak) ← liftText (do
    let r ← hashWorkloadHintsFromSignersDirect seedCells signers ctx.bytecodeValue
    if signers.size == ctx.records.size then
      .ok r
    else
      let allOk := Fin.foldl ctx.records.size (fun ok i =>
        if !ok then false
        else if hi : i.val < ctx.records.size then Model.Xmss.verifySignatureFast ctx.records[i.val]
        else true) true
      if allOk then .ok r else .error "Lean signature verification failed")
  let artifact : ProofArtifact := {
    prover := "stub", logInvRate := ctx.logInvRate,
    records := ctx.records.size, signers := signers.size,
    hintEntries, statement, hintsKeccak,
    cycles := none, memoryCells := none,
    memoryKeccak := ByteArray.empty }
  let t1 ← IO.monoNanosNow
  return (artifact, t1 - t0)

def e2eProver (fuel : Nat := 10000000) : AggregateProverFn :=
    fun ctx signers statement hints => do
  if ctx.records.size > vmProverMaxRecords then
    throw (IO.userError s!"e2e prover is for fixtures of at most {vmProverMaxRecords} records")
  let (eth, run) ← proveLeafEthereumFast ctx.program ctx.frame ctx.schedule ctx.seed
    ctx.bytecodeValue signers ctx.logInvRate statement hints ctx.iv ctx.bytecodeCols fuel
  return {
    prover := "e2e", logInvRate := ctx.logInvRate,
    records := ctx.records.size, signers := signers.size,
    hintEntries := hints.size, statement,
    hintsKeccak := ByteArray.empty,
    cycles := some run.cycles, memoryCells := some run.memUsed,
    memoryKeccak := ByteArray.empty,
    wireBytes := ByteArray.empty,
    proofSize := some (Model.Aggregate.Wire.EthereumProof.proofSize eth),
    ethProof := some eth }

def proverOf (name : String) : IO AggregateProverFn :=
  match name with
  | "vm" => pure vmWitnessProver
  | "stub" => pure stubProver
  | "e2e" => pure e2eProver
  | other => throw (IO.userError s!"unknown prover: {other}")

def runAggregatePass (prover : AggregateProverFn) (ctx : AggregateContext)
    : IO (ProofArtifact × Nat) := do
  let t0 ← IO.monoNanosNow
  let (signers, hints) ← verifyAndHintsParallel ctx.seed ctx.records ctx.bytecodeValue
  let statement := Model.Xmss.statementDigest ctx.seed signers ctx.bytecodeValue
  let artifact ← prover ctx signers statement hints
  let t1 ← IO.monoNanosNow
  return (artifact, t1 - t0)

def runPhasedE2EPass (ctx : AggregateContext) (exportDir : Option System.FilePath := none)
    (fuel : Nat := 10000000) : IO (ProofArtifact × Nat × PhaseTimings) := do
  if ctx.records.size > vmProverMaxRecords then
    throw (IO.userError s!"e2e prover is for fixtures of at most {vmProverMaxRecords} records")
  let (eth, statement, hintCount, run, wire, timings) ← proveLeafEthereumTimedPass ctx.program
    ctx.frame ctx.schedule ctx.seed ctx.bytecodeValue ctx.records ctx.logInvRate ctx.iv
    ctx.bytecodeCols exportDir fuel
  let artifact : ProofArtifact := {
    prover := "e2e", logInvRate := ctx.logInvRate,
    records := ctx.records.size, signers := eth.claims.xmss.size,
    hintEntries := hintCount, statement,
    hintsKeccak := ByteArray.empty,
    cycles := some run.cycles, memoryCells := some run.memUsed,
    memoryKeccak := ByteArray.empty, wireBytes := wire,
    proofSize := some (Model.Aggregate.Wire.EthereumProof.proofSize eth),
    ethProof := some eth }
  return (artifact, timings.total, timings)

def artifactLines (a : ProofArtifact) : String :=
  "prover=" ++ a.prover ++ "\n" ++
  "log_inv_rate=" ++ toString a.logInvRate ++ "\n" ++
  "records=" ++ toString a.records ++ "\n" ++
  "signers=" ++ toString a.signers ++ "\n" ++
  "hint_entries=" ++ toString a.hintEntries ++ "\n" ++
  "statement_digest=" ++ hex a.statement ++ "\n" ++
  "hints_keccak256=" ++ hex a.hintsKeccak ++ "\n" ++
  "cycles=" ++ (a.cycles.map toString |>.getD "none") ++ "\n" ++
  "memory_cells_used=" ++ (a.memoryCells.map toString |>.getD "none") ++ "\n" ++
  "memory_keccak256=" ++ (if a.memoryKeccak.isEmpty then "none" else hex a.memoryKeccak) ++ "\n"

def flagValue (args : List String) (name : String) : Option String :=
  (List.range (args.length + 1)).foldl (fun acc i =>
    match acc with
    | some _ => acc
    | none => if (args[i]?.getD "") == name then args[i + 1]? else none) none

def parseNat (text : String) : Option Nat :=
  let bytes := text.toUTF8
  if bytes.isEmpty then none
  else Model.Pcs.Ntt.foldRange bytes.size
    (fun acc i =>
      match acc with
      | none => none
      | some n =>
        let d := (bytes[i]?.getD 0).toNat
        if d >= 48 && d <= 57 then some (n * 10 + d - 48) else none)
    (some 0)

def natFlag (args : List String) (name : String) (fallback : Nat) : IO Nat := do
  match flagValue args name with
  | some v => match parseNat v with
    | some n => pure n
    | none => throw (IO.userError s!"flag {name} expects a number, got {v}")
  | none => pure fallback

def stringFlag (args : List String) (name : String) : IO String := do
  match flagValue args name with
  | some v => pure v
  | none => throw (IO.userError s!"missing required flag {name}")

def writePhaseReportJson (path : System.FilePath) (xmss records signers logInvRate : Nat)
    (warmup : PhaseTimings) (passes : Array PhaseTimings) : IO Unit := do
  let n := max passes.size 1
  let meanOf (proj : PhaseTimings → Nat) : Nat :=
    (passes.foldl (fun acc p => acc + proj p) 0) / n
  let maxHwm := passes.foldl (fun m p => max m p.vmHwmBytes) warmup.vmHwmBytes
  let maxRss := passes.foldl (fun m p => max m p.vmRssBytes) warmup.vmRssBytes
  let mut passItems := ""
  for idx in [:passes.size] do
    let sep := if idx == 0 then "" else ","
    passItems := passItems ++ sep ++ phaseTimingsJson (idx + 1) (passes[idx]?.getD default)
  let meanTimings : PhaseTimings := {
    statementHints := meanOf PhaseTimings.statementHints
    executeWitness := meanOf PhaseTimings.executeWitness
    commitNttMerkle := meanOf PhaseTimings.commitNttMerkle
    busConstraints := meanOf PhaseTimings.busConstraints
    keccakGkr := meanOf PhaseTimings.keccakGkr
    pcsOpen := meanOf PhaseTimings.pcsOpen
    wireEncode := meanOf PhaseTimings.wireEncode
    total := meanOf PhaseTimings.total
    vmRssBytes := maxRss
    vmHwmBytes := maxHwm
    rssStatementHints := meanOf PhaseTimings.rssStatementHints
    rssExecuteWitness := meanOf PhaseTimings.rssExecuteWitness
    rssCommitNttMerkle := meanOf PhaseTimings.rssCommitNttMerkle
    rssBusConstraints := meanOf PhaseTimings.rssBusConstraints
    rssKeccakGkr := meanOf PhaseTimings.rssKeccakGkr
    rssPcsOpen := meanOf PhaseTimings.rssPcsOpen
    rssWireEncode := meanOf PhaseTimings.rssWireEncode }
  let doc :=
    "{\"xmss\":" ++ toString xmss ++ "," ++
    "\"records\":" ++ toString records ++ "," ++
    "\"signers\":" ++ toString signers ++ "," ++
    "\"log_inv_rate\":" ++ toString logInvRate ++ "," ++
    "\"warmup\":" ++ phaseTimingsJson 0 warmup ++ "," ++
    "\"passes\":[" ++ passItems ++ "]," ++
    "\"mean\":" ++ phaseTimingsJson passes.size meanTimings ++ "}\n"
  IO.FS.writeFile path doc

def aggregateMain (args : List String) : IO Unit := do
  let xmss ← natFlag args "--xmss" 0
  let inputs ← stringFlag args "--inputs"
  let outProof ← stringFlag args "--out-proof"
  let logInvRate ← natFlag args "--log-inv-rate" 1
  let repeatCount ← natFlag args "--repeat" 3
  let cooldownMs ← natFlag args "--cooldown-ms" 2000
  let proverName := (flagValue args "--prover").getD "vm"
  let phaseTimingsOut := flagValue args "--phase-timings"
  let exportFixturesOut := flagValue args "--export-fixtures"
  let prover ← proverOf proverName
  let dir : System.FilePath := ⟨inputs⟩
  let records ← loadRawInputs (childPath dir "xmss-inputs.bin")
  let seed ← loadSeed (childPath dir "seed.bin")
  let bytecodeValue ← loadBytecodeValue (childPath dir "bytecode-value.bin")
  let (program, frame, schedule) ← loadGuest dir
  let bytecodeCols := Model.Layout.bytecodeColumnsFast program
  let iv := ivOfCols program bytecodeCols
  let ctx : AggregateContext :=
    ⟨program, frame, schedule, seed, bytecodeValue, records, logInvRate, bytecodeCols, iv⟩
  let usePhased := proverName == "e2e" && (phaseTimingsOut.isSome || exportFixturesOut.isSome)
  let out ← IO.getStdout
  out.putStrLn (s!"BENCH|impl=lean-cli|prover={proverName}|xmss={xmss}|records={records.size}" ++
    s!"|signers={(signersOf records).size}|log_inv_rate={logInvRate}" ++
    s!"|repeat={repeatCount}|cooldown_ms={cooldownMs}")
  let mut warmupTimings : PhaseTimings := default
  let (warmupArtifact, warmupNanos) ←
    if usePhased then do
      let exp0 := if repeatCount == 0 then exportFixturesOut.map System.FilePath.mk else none
      let (art, ns, tm) ← runPhasedE2EPass ctx exp0
      warmupTimings := tm
      pure (art, ns)
    else if proverName == "stub" then
      runStubPass ctx
    else
      runAggregatePass prover ctx
  out.putStrLn s!"WARMUP|nanos={warmupNanos}"
  let mut last : ProofArtifact :=
    if repeatCount == 0 then warmupArtifact else { warmupArtifact with ethProof := none }
  let mut times : Array Nat := #[]
  let mut passTimings : Array PhaseTimings := #[]
  for i in [1:repeatCount + 1] do
    if cooldownMs > 0 then IO.sleep cooldownMs.toUInt32
    if usePhased then
      let expDir :=
        if i == repeatCount then exportFixturesOut.map System.FilePath.mk else none
      let (artifact, nanos, tm) ← runPhasedE2EPass ctx expDir
      last := artifact
      times := times.push nanos
      passTimings := passTimings.push tm
      out.putStrLn s!"PASS|i={i}|nanos={nanos}"
    else if proverName == "stub" then
      let (artifact, nanos) ← runStubPass ctx
      last := artifact
      times := times.push nanos
      out.putStrLn s!"PASS|i={i}|nanos={nanos}"
    else
      let (artifact, nanos) ← runAggregatePass prover ctx
      last := artifact
      times := times.push nanos
      out.putStrLn s!"PASS|i={i}|nanos={nanos}"
  let finalWire :=
    if !last.wireBytes.isEmpty then last.wireBytes
    else match last.ethProof with
      | some eth => Model.Aggregate.Wire.EthereumProof.toBytesWithoutPubkeys eth
      | none => ByteArray.empty
  let mean := (times.foldl (· + ·) 0) / (max times.size 1)
  let hintsHex := if last.hintsKeccak.isEmpty then "none" else hex last.hintsKeccak
  let memHex := if last.memoryKeccak.isEmpty then "none" else hex last.memoryKeccak
  let wireSizeStr := if finalWire.isEmpty then "none" else toString finalWire.size
  let proofSizeStr := last.proofSize.map toString |>.getD "none"
  let (_, hwmBytes) ← readProcMemBytes
  out.putStrLn (s!"LAST|statement={hex last.statement}|hints_keccak256={hintsHex}" ++
    s!"|proof_bytes={wireSizeStr}|proof_size={proofSizeStr}" ++
    s!"|cycles={(last.cycles.map toString |>.getD "none")}|memory_cells_used=" ++
    s!"{(last.memoryCells.map toString |>.getD "none")}|memory_keccak256=" ++
    s!"{memHex}|vm_hwm_bytes={hwmBytes}")
  out.putStrLn s!"STATS|passes={times.size}|mean_nanos={mean}"
  if let some ptPath := phaseTimingsOut then
    writePhaseReportJson ⟨ptPath⟩ xmss records.size last.signers logInvRate
      warmupTimings passTimings
  if !finalWire.isEmpty then
    IO.FS.writeBinFile (⟨outProof⟩ : System.FilePath) finalWire
    out.putStrLn s!"ARTIFACT|path={outProof}|bytes={finalWire.size}"
  else
    let text := artifactLines last
    IO.FS.writeFile (⟨outProof⟩ : System.FilePath) text
    out.putStrLn s!"ARTIFACT|path={outProof}|bytes={text.toUTF8.size}"

end LeanVmXmss.Model.Cli
