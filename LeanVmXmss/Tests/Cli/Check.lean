import Model.Cli.Aggregate

/-!
The `cli-check` binary: end-to-end validation of the pure Lean aggregate input
and statement/hints pipeline against the Rust-generated oracle fixtures.

Modes:
- `oracle <dir>`     full check of one oracle fixture directory: signature
                     verification, hints, statement, and a full linear-VM
                     execution compared cycle-for-cycle against `execution.json`.
- `parity <dir>`     statement/hints parity only (no VM run), for fixtures whose
                     interpretation is out of scope here (xmss1400).
- `fresh <dir> <guest-dir>` check freshly generated inputs (non-cached mock keys)
                     against their expected statement/hints/execution, plus
                     permutation invariance.
- `bench <flags...>` the benchmark CLI (`Model.Cli.aggregateMain`).
- `gate <oracle-root> <fresh-dir>` all of the above on the standard fixtures.
-/

namespace LeanVmXmss.Tests.Cli

open LeanVmXmss.Model.Cli Spec.Xmss Spec.Vm

/-! Minimal JSON field extraction over the UTF-8 bytes, avoiding the classical
`String` list accessors. -/

def prefixOf (pat text : List UInt8) : Bool :=
  pat.length <= text.length && (pat.zip text).all (fun (p, t) => p.toNat == t.toNat)

def findPattern (pat : List UInt8) (text : List UInt8) : Option (List UInt8) :=
  (List.range (text.length + 1)).foldl (fun acc i =>
    match acc with
    | some _ => acc
    | none =>
      let rest := text.drop i
      if prefixOf pat rest then some rest else none) none

def keyPattern (key : String) : List UInt8 :=
  34 :: (key.toUTF8.data.toList ++ [34, 58])

def jsonInt (text : String) (key : String) : Option Nat := do
  let after ← findPattern (keyPattern key) (text.toUTF8.data.toList)
  let rest := after.drop (keyPattern key).length
  let digits := (rest.dropWhile (fun b => b.toNat == 32)).takeWhile fun b =>
    b.toNat >= 48 && b.toNat <= 57
  return digits.foldl (fun n b => n*10 + b.toNat - 48) 0

def jsonStringBytes (text : String) (key : String) : Option (List UInt8) := do
  let after ← findPattern (keyPattern key) (text.toUTF8.data.toList)
  let rest := after.drop (keyPattern key).length
  let chars := rest.dropWhile (fun b => b.toNat == 32)
  return (chars.drop 1).takeWhile (fun b => b.toNat != 34)

/-- The ASCII hex encoding of a digest, as bytes, to compare against a JSON value. -/
def asciiHexBytes (bytes : ByteArray) : ByteArray := Id.run do
  let digits := "0123456789abcdef".toUTF8
  let mut out := ByteArray.emptyWithCapacity (bytes.size * 2)
  for i in [:bytes.size] do
    let b := bytes[i]!
    out := out.push digits[(b.toNat / 16)]!
    out := out.push digits[(b.toNat % 16)]!
  return out

def jsonHash (report : String) (key : String) : IO ByteArray := do
  match jsonStringBytes report key with
  | some bytes => return ⟨bytes.toArray⟩
  | none => throw (IO.userError s!"json field missing: {key}")

/-- Text file reading over the binary primitive, which keeps the classical
`String` accessors out of the audited declarations. -/
def readAsciiFile (path : System.FilePath) : IO String := do
  let bytes ← IO.FS.readBinFile path
  let list := bytes.data.toList
  if list.any (fun b => b.toNat >= 128) then
    throw (IO.userError s!"{path}: non-ASCII content")
  return String.ofList (list.map fun b =>
    if h : b.toNat.isValidChar then Char.ofNatAux b.toNat h else '?')

/-- The expected cycle count of the standard oracle fixtures, when known. -/
def expectedCycles (records : Nat) : Option Nat :=
  match records with
  | 4 => some 21465
  | 16 => some 31140
  | 1400 => some 1146537
  | _ => none

/-- Run the guest over the derived witness and return the execution statistics. -/
def vmExecution (dir : System.FilePath) (raw : Array RawSignature) (statement : ByteArray)
    : IO (Nat × Nat × ByteArray × Array Nat) := do
  let (program, frame, schedule) ← loadGuest dir
  let hints ← liftText (hintsOf (← loadSeed (childPath dir "seed.bin")) raw
    (← loadBytecodeValue (childPath dir "bytecode-value.bin")))
  let streams := streamsOfHints hints
  let state ← liftFault (Model.Vm.initial frame #[packCell statement, packCell statement 16]
    program.size)
  let mut cur : Runtime := ⟨state, streams⟩
  for _ in [:100000000] do
    if cur.state.pc+1 == program.size && cur.state.fp == 0 then break
    let op ← liftFault (match program[cur.state.pc]? with
      | some op => Except.ok op
      | none => Except.error Fault.badProgram)
    let ⟨ready, streams'⟩ ← liftFault (Model.Vm.applyHintsLinear (schedule[cur.state.pc]?.getD #[]) cur)
    let st ← liftFault (Model.Vm.stepLinear op ready)
    cur := ⟨st, streams'⟩
  let s := cur.state
  unless s.memory.unconstrainedReads.isEmpty do throw (IO.userError "unconstrained reads")
  let memory := serializeMemory s.memory.cells s.memory.used
  return (s.cycles, s.memory.used, Spec.Vm.KeccakInternal.hash memory, s.opcodeCounts)

/-- Statement and hints parity against an oracle fixture directory. -/
def parityCheck (dir : System.FilePath) : IO (Nat × ByteArray) := do
  let raw ← loadRawInputs (childPath dir "xmss-inputs.bin")
  let seed ← loadSeed (childPath dir "seed.bin")
  let bytecodeValue ← loadBytecodeValue (childPath dir "bytecode-value.bin")
  for x in raw do
    unless verifySignature x do throw (IO.userError "Lean signature verification failed")
  let hints ← liftText (hintsOf seed raw bytecodeValue)
  let encoded := encodeHints hints
  let expectedHints ← IO.FS.readBinFile (childPath dir "hints.bin")
  unless encoded == expectedHints do throw (IO.userError "Lean/Rust hint byte mismatch")
  let statement := statementOf seed raw bytecodeValue
  let expectedStatement ← IO.FS.readBinFile (childPath dir "statement.bin")
  unless statement == expectedStatement do throw (IO.userError "Lean/Rust statement mismatch")
  return (raw.size, statement)

def oracleMode (dir : System.FilePath) : IO Unit := do
  let (records, statement) ← parityCheck dir
  let raw ← loadRawInputs (childPath dir "xmss-inputs.bin")
  let (cycles, cells, memoryHash, _) ← vmExecution dir raw statement
  let report ← readAsciiFile (childPath dir "execution.json")
  let oracleCycles ← match jsonInt report "cycles" with
    | some n => pure n
    | none => throw (IO.userError "execution.json: missing cycles")
  unless cycles == oracleCycles do
    throw (IO.userError s!"cycle mismatch: Lean {cycles} vs oracle {oracleCycles}")
  if let some known := expectedCycles records then
    unless cycles == known do
      throw (IO.userError s!"cycle mismatch: Lean {cycles} vs constant {known}")
  let expectedCells ← match jsonInt report "memory_cells_used" with
    | some n => pure n
    | none => throw (IO.userError "execution.json: missing memory_cells_used")
  unless cells == expectedCells do
    throw (IO.userError s!"memory cell mismatch: Lean {cells} vs oracle {expectedCells}")
  let expectedHash ← jsonHash report "memory_keccak256"
  unless asciiHexBytes memoryHash == expectedHash do
    throw (IO.userError s!"memory hash mismatch: Lean {hex memoryHash} vs oracle {expectedHash}")
  IO.println (s!"CLI_CHECK_ORACLE|PASS|dir={dir}|records={records}|cycles={cycles}" ++
    s!"|memory_cells_used={cells}|memory_keccak256={hex memoryHash}")

def parityMode (dir : System.FilePath) : IO Unit := do
  let (records, statement) ← parityCheck dir
  IO.println s!"CLI_CHECK_PARITY|PASS|dir={dir}|records={records}|statement_digest={hex statement}"

/-- Deterministically permute a record list: rotate by one, then reverse. -/
def permuteRecords (raw : Array RawSignature) : Array RawSignature :=
  let rotated := raw.drop 1 |>.append (raw.take 1)
  rotated.reverse

def freshMode (dir guestDir : System.FilePath) : IO Unit := do
  let raw ← loadRawInputs (childPath dir "xmss-inputs.bin")
  let seed ← loadSeed (childPath dir "seed.bin")
  let bytecodeValue ← loadBytecodeValue (childPath dir "bytecode-value.bin")
  for x in raw do
    unless verifySignature x do throw (IO.userError "fresh input failed Lean signature check")
  let hints ← liftText (hintsOf seed raw bytecodeValue)
  let encoded := encodeHints hints
  let expectedHints ← IO.FS.readBinFile (childPath dir "expected-hints.bin")
  unless encoded == expectedHints do throw (IO.userError "fresh hints mismatch")
  let statement := statementOf seed raw bytecodeValue
  let expectedStatement ← IO.FS.readBinFile (childPath dir "expected-statement.bin")
  unless statement == expectedStatement do throw (IO.userError "fresh statement mismatch")
  let permuted := permuteRecords raw
  unless statementOf seed permuted bytecodeValue == statement do
    throw (IO.userError "statement is not permutation invariant")
  let permutedHints ← liftText (hintsOf seed permuted bytecodeValue)
  unless encodeHints permutedHints == encoded do
    throw (IO.userError "hints are not permutation invariant")
  let (cycles, cells, memoryHash, _) ← vmExecution guestDir raw statement
  let report ← readAsciiFile (childPath dir "expected-execution.json")
  let expectedCycles ← match jsonInt report "cycles" with
    | some n => pure n
    | none => throw (IO.userError "expected-execution.json: missing cycles")
  unless cycles == expectedCycles do
    throw (IO.userError s!"fresh cycle mismatch: Lean {cycles} vs Rust {expectedCycles}")
  let expectedHash ← jsonHash report "memory_keccak256"
  unless asciiHexBytes memoryHash == expectedHash do
    throw (IO.userError s!"fresh memory hash mismatch: Lean {hex memoryHash} vs Rust {expectedHash}")
  let expectedCells ← match jsonInt report "memory_cells_used" with
    | some n => pure n
    | none => throw (IO.userError "expected-execution.json: missing memory_cells_used")
  unless cells == expectedCells do
    throw (IO.userError s!"fresh memory cells mismatch: Lean {cells} vs Rust {expectedCells}")
  IO.println (s!"CLI_CHECK_FRESH|PASS|dir={dir}|records={raw.size}|cycles={cycles}" ++
    s!"|memory_cells_used={cells}|memory_keccak256={hex memoryHash}")

def gateMode (root freshDir : System.FilePath) : IO Unit := do
  oracleMode (childPath root "xmss4")
  oracleMode (childPath root "xmss16")
  parityMode (childPath root "xmss1400")
  freshMode freshDir (childPath root "xmss4")
  IO.println s!"CLI_CHECK_GATE|PASS"

def main (args : List String) : IO Unit := do
  let mode := args.head?.getD "usage"
  match mode with
  | "oracle" =>
    match args[1]? with
    | some dir => oracleMode ⟨dir⟩
    | none => throw (IO.userError "usage: cli-check oracle <dir>")
  | "parity" =>
    match args[1]? with
    | some dir => parityMode ⟨dir⟩
    | none => throw (IO.userError "usage: cli-check parity <dir>")
  | "fresh" =>
    match args[1]?, args[2]? with
    | some dir, some guest => freshMode ⟨dir⟩ ⟨guest⟩
    | _, _ => throw (IO.userError "usage: cli-check fresh <fresh-dir> <guest-dir>")
  | "bench" => aggregateMain args.tail
  | "gate" =>
    match args[1]?, args[2]? with
    | some root, some fresh => gateMode ⟨root⟩ ⟨fresh⟩
    | _, _ => throw (IO.userError "usage: cli-check gate <oracle-root> <fresh-dir>")
  | other => throw (IO.userError s!"unknown mode: {other}")

end LeanVmXmss.Tests.Cli

def main (args : List String) : IO Unit := LeanVmXmss.Tests.Cli.main args
