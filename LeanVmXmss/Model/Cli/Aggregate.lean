import Model.Cli.Inputs
import Model.Cli.E2E
import Model.Vm.Linear

/-!
The pluggable aggregate prover and its benchmark CLI.

`AggregateContext` carries everything loaded outside the timer; an
`AggregateProverFn` turns the raw fixture plus the freshly derived statement and
hints into a `ProofArtifact`. The default `vmWitnessProver` runs the linear VM
interpreter over the schedule (`Model.Vm.scheduledRunLinear`) and packages the
execution statistics as the artifact; a stub prover covers statement/hints-only
benchmarking for workloads too large to interpret here.

The timing loop matches the Rust reference (`bins/leanvm/src/benchmark.rs` with
`bench::Plan`): bytecode, schedule and fixture inputs are loaded outside the
timer; one discarded warmup pass precedes `repeat` measured passes; a cooldown
sleep precedes each measured pass outside the timer; every pass recomputes
statement and hints from the raw `(pubkey, message, signature)` records and then
runs the prover. Pass times are reported as unrounded nanoseconds.
-/

namespace LeanVmXmss.Model.Cli

open Spec.Xmss Spec.Vm

/-- Everything the prover needs, loaded once outside the timer. -/
structure AggregateContext where
  program : Array Op
  frame : Nat
  schedule : Array (Array RHint)
  seed : ByteArray
  bytecodeValue : Spec.Field.E
  records : Array RawSignature
  logInvRate : Nat

/-- What one proving pass produced. -/
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
  deriving Inhabited

/-- A pluggable prover entrypoint: context, freshly derived statement, fresh hints. -/
abbrev AggregateProverFn := AggregateContext → ByteArray → Array HintEntry → IO ProofArtifact

/-! ### The default VM-witness prover -/

def pushWord (bytes : ByteArray) (value : UInt64) : ByteArray :=
  bytes.push value.toUInt8
    |>.push (value >>> 8).toUInt8
    |>.push (value >>> 16).toUInt8
    |>.push (value >>> 24).toUInt8
    |>.push (value >>> 32).toUInt8
    |>.push (value >>> 40).toUInt8
    |>.push (value >>> 48).toUInt8
    |>.push (value >>> 56).toUInt8

/-- The used prefix of the write-once memory image, word-serialized. -/
def serializeMemory (cells : Array Cell) (used : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.emptyWithCapacity (used * 24)
  for i in [:used] do
    let x := (Model.Vm.cellAt cells i).word
    bytes := pushWord bytes x.c0
    bytes := pushWord bytes x.c1
    bytes := pushWord bytes x.c2
  return bytes

/-- The largest raw workload the VM-witness prover accepts here: interpreting a
leaf's full witness is for the small fixtures; bigger ones benchmark with the
stub prover (statement + hints only). -/
def vmProverMaxRecords : Nat := 500

/-- The default prover: derive the witness by executing the guest in the linear
interpreter, then package the execution statistics. -/
def vmWitnessProver (fuel : Nat := 100000000) : AggregateProverFn := fun ctx statement hints => do
  if ctx.records.size > vmProverMaxRecords then
    throw (IO.userError s!"vm prover is for fixtures of at most {vmProverMaxRecords} records")
  let encoded := encodeHints hints
  let streams := streamsOfHints hints
  let state ← liftFault (Model.Vm.initial ctx.frame #[packCell statement, packCell statement 16]
    ctx.program.size)
  let mut cur : Runtime := ⟨state, streams⟩
  for _ in [:fuel] do
    if cur.state.pc+1 == ctx.program.size && cur.state.fp == 0 then break
    let op ← liftFault (match ctx.program[cur.state.pc]? with
      | some op => Except.ok op
      | none => Except.error Fault.badProgram)
    let ⟨ready, streams'⟩ ← liftFault (Model.Vm.applyHintsLinear (ctx.schedule[cur.state.pc]?.getD #[]) cur)
    let st ← liftFault (Model.Vm.stepLinear op ready)
    cur := ⟨st, streams'⟩
  let s := cur.state
  unless s.memory.unconstrainedReads.isEmpty do throw (IO.userError "unconstrained reads")
  let memory := serializeMemory s.memory.cells s.memory.used
  return {
    prover := "vm-witness", logInvRate := ctx.logInvRate,
    records := ctx.records.size, signers := (signersOf ctx.records).size,
    hintEntries := hints.size, statement, hintsKeccak := Spec.Vm.KeccakInternal.hash encoded,
    cycles := some s.cycles, memoryCells := some s.memory.used,
    memoryKeccak := Spec.Vm.KeccakInternal.hash memory }

/-- The stub prover: statement and hints only, no VM execution. -/
def stubProver : AggregateProverFn := fun ctx statement hints => do
  return {
    prover := "stub", logInvRate := ctx.logInvRate,
    records := ctx.records.size, signers := (signersOf ctx.records).size,
    hintEntries := hints.size, statement,
    hintsKeccak := Spec.Vm.KeccakInternal.hash (encodeHints hints),
    cycles := none, memoryCells := none,
    memoryKeccak := ByteArray.empty }

def e2eProver (fuel : Nat := 10000000) : AggregateProverFn := fun ctx statement hints => do
  if ctx.records.size > vmProverMaxRecords then
    throw (IO.userError s!"e2e prover is for fixtures of at most {vmProverMaxRecords} records")
  let encoded := encodeHints hints
  let (wire, run) ← proveLeafEthereum ctx.program ctx.frame ctx.schedule ctx.seed
    ctx.bytecodeValue ctx.records ctx.logInvRate statement hints fuel
  return {
    prover := "e2e", logInvRate := ctx.logInvRate,
    records := ctx.records.size, signers := (signersOf ctx.records).size,
    hintEntries := hints.size, statement,
    hintsKeccak := Spec.Vm.KeccakInternal.hash encoded,
    cycles := some run.cycles, memoryCells := some run.memUsed,
    memoryKeccak := run.memoryKeccak, wireBytes := wire }

def proverOf (name : String) : IO AggregateProverFn :=
  match name with
  | "vm" => pure (vmWitnessProver)
  | "stub" => pure stubProver
  | "e2e" => pure (e2eProver)
  | other => throw (IO.userError s!"unknown prover: {other}")

/-! ### One timed pass -/

/-- One full pass: statement and hints recomputed from raw, then the prover.
Returns the artifact and the pass duration in nanoseconds. -/
def runAggregatePass (prover : AggregateProverFn) (ctx : AggregateContext)
    : IO (ProofArtifact × Nat) := do
  let t0 ← IO.monoNanosNow
  let statement := statementOf ctx.seed ctx.records ctx.bytecodeValue
  let hints ← liftText (hintsOf ctx.seed ctx.records ctx.bytecodeValue)
  let artifact ← prover ctx statement hints
  let t1 ← IO.monoNanosNow
  return (artifact, t1 - t0)

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

/-! ### The benchmark CLI -/

def flagValue (args : List String) (name : String) : Option String :=
  (List.range (args.length + 1)).foldl (fun acc i =>
    match acc with
    | some _ => acc
    | none => if (args[i]?.getD "") == name then args[i+1]? else none) none

def parseNat (text : String) : Option Nat :=
  let bytes := text.toUTF8.data
  if bytes.isEmpty then none
  else bytes.foldlM (fun n b =>
    if b.toNat >= 48 && b.toNat <= 57 then some (n*10+b.toNat-48) else none) 0

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

/-- Usage: aggregateMain [--xmss N] --inputs DIR --out-proof PATH
  [--log-inv-rate 1] [--repeat 3] [--cooldown-ms 2000] [--prover vm|stub|e2e] -/
def aggregateMain (args : List String) : IO Unit := do
  let xmss ← natFlag args "--xmss" 0
  let inputs ← stringFlag args "--inputs"
  let outProof ← stringFlag args "--out-proof"
  let logInvRate ← natFlag args "--log-inv-rate" 1
  let repeatCount ← natFlag args "--repeat" 3
  let cooldownMs ← natFlag args "--cooldown-ms" 2000
  let proverName := (flagValue args "--prover").getD "vm"
  let prover ← proverOf proverName
  let dir : System.FilePath := ⟨inputs⟩
  let records ← loadRawInputs (childPath dir "xmss-inputs.bin")
  let seed ← loadSeed (childPath dir "seed.bin")
  let bytecodeValue ← loadBytecodeValue (childPath dir "bytecode-value.bin")
  let (program, frame, schedule) ← loadGuest dir
  let ctx : AggregateContext := ⟨program, frame, schedule, seed, bytecodeValue, records, logInvRate⟩
  let out ← IO.getStdout
  out.putStrLn (s!"BENCH|impl=lean-cli|prover={proverName}|xmss={xmss}|records={records.size}" ++
    s!"|signers={(signersOf records).size}|log_inv_rate={logInvRate}|repeat={repeatCount}|cooldown_ms={cooldownMs}")
  let (warmupArtifact, warmupNanos) ← runAggregatePass prover ctx
  out.putStrLn s!"WARMUP|nanos={warmupNanos}"
  let mut last : ProofArtifact := warmupArtifact
  let mut times : Array Nat := #[]
  for i in [1:repeatCount+1] do
    if cooldownMs > 0 then IO.sleep cooldownMs.toUInt32
    let (artifact, nanos) ← runAggregatePass prover ctx
    last := artifact
    times := times.push nanos
    out.putStrLn s!"PASS|i={i}|nanos={nanos}"
  let mean := (times.foldl (· + ·) 0) / (max times.size 1)
  out.putStrLn (s!"LAST|statement={hex last.statement}|hints_keccak256={hex last.hintsKeccak}" ++
    s!"|cycles={(last.cycles.map toString |>.getD "none")}|memory_cells_used=" ++
    s!"{(last.memoryCells.map toString |>.getD "none")}|memory_keccak256=" ++
    (if last.memoryKeccak.isEmpty then "none" else hex last.memoryKeccak))
  out.putStrLn s!"STATS|passes={times.size}|mean_nanos={mean}"
  if !last.wireBytes.isEmpty then
    IO.FS.writeBinFile (⟨outProof⟩ : System.FilePath) last.wireBytes
    out.putStrLn s!"ARTIFACT|path={outProof}|bytes={last.wireBytes.size}"
  else
    let text := artifactLines last
    IO.FS.writeFile (⟨outProof⟩ : System.FilePath) text
    out.putStrLn s!"ARTIFACT|path={outProof}|bytes={text.toUTF8.size}"

end LeanVmXmss.Model.Cli
