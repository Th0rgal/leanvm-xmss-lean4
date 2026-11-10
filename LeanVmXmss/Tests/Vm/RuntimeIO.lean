import Model.Vm.Linear
import Tests.Xmss.Differential

namespace LeanVmXmss.Tests.Vm

open Spec.Vm Spec.Xmss

abbrev Reader := StateT Nat (Except String)

def takeWord (bytes : ByteArray) : Reader UInt64 := do
  let offset ← get
  if offset+8 > bytes.size then throw "truncated schedule"
  set (offset+8)
  return readLE bytes offset 8

def takeNat (bytes : ByteArray) : Reader Nat := return (← takeWord bytes).toNat

def takeString (bytes : ByteArray) : Reader String := do
  let len ← takeNat bytes
  let offset ← get
  if offset+len > bytes.size then throw "truncated name"
  set (offset+len)
  let data := (bytes.extract offset (offset+len)).data.toList
  if data.any (fun b => b.toNat >= 128) then throw "non-ASCII name"
  return String.ofList (data.map fun b =>
    if h : b.toNat.isValidChar then Char.ofNatAux b.toNat h else '?')

def asciiNat (text : String) : Option Nat := do
  let bytes := text.toUTF8.data
  if bytes.isEmpty then none
  else bytes.foldlM (fun n b =>
    if b.toNat >= 48 && b.toNat <= 57 then some (n*10+b.toNat-48) else none) 0

def takeDest (bytes : ByteArray) : Reader BitsDest := do
  let tag ← takeNat bytes
  let base ← takeNat bytes
  if tag == 0 then return .stack base
  else if tag == 1 then return .heap base
  else throw "invalid bit destination"

def takeHint (b : ByteArray) : Reader RHint := do
  let tag ← takeNat b
  match tag with
  | 0 => return .frameAddress (← takeNat b)
  | 1 => return .allocFrames (← takeNat b) (← takeNat b) (← takeNat b) (← takeWord b) (← takeNat b)
  | 2 => return .alloc (← takeNat b) (← takeNat b)
  | 3 => return .allocDyn (← takeNat b) (← takeNat b)
  | 4 => return .witnessStack (← takeString b) (← takeNat b) (← takeNat b)
  | 5 => return .witnessHeap (← takeString b) (← takeNat b) (← takeNat b) (← takeNat b)
  | 6 => return .log2Ceil (← takeDest b) (← takeNat b) (← takeNat b) (← takeNat b)
  | 7 => return .bitDecompose (← takeNat b) (← takeDest b) (← takeNat b) (← takeNat b)
  | 8 => return .bitDecomposeExp (← takeNat b) (← takeDest b) (← takeNat b)
  | 9 =>
    let value ← takeNat b
    let dest ← takeDest b
    let nbits ← takeNat b
    let ndigits ← takeNat b
    let digitBits ← takeNat b
    let start ← takeNat b
    let cell ← takeWord b
    return .digitDecomposeExp value dest nbits ndigits digitBits start
      (if cell.toNat == 18446744073709551615 then none else some cell.toNat)
  | 10 => return .windowsExp (← takeNat b) (← takeDest b) (← takeNat b) (← takeNat b) (← takeNat b) (← takeNat b)
  | 11 => return .fieldLimbs (← takeNat b) (← takeNat b) (← takeNat b)
  | 12 => return .inverse (← takeNat b) (← takeNat b)
  | 13 => return .print (← takeString b) (← takeNat b)
  | _ => throw "unknown hint"

def readSchedule (bytes : ByteArray) (programSize : Nat) : Except String (Nat × Array (Array RHint)) := do
  let ((frame, hints), endOffset) ← (do
    let frame ← takeNat bytes
    let size ← takeNat bytes
    let mut hints := Array.replicate programSize #[]
    for _ in [:size] do
      let pc ← takeNat bytes
      if pc >= programSize then throw "schedule PC out of bounds"
      let count ← takeNat bytes
      let mut list := #[]
      for _ in [:count] do list := list.push (← takeHint bytes)
      hints := hints.set! pc list
    pure (frame,hints) : Reader (Nat × Array (Array RHint))).run 0
  if endOffset != bytes.size then throw "trailing schedule bytes"
  return (frame,hints)

def streamsOf (hints : Array HintEntry) : Array Stream := Id.run do
  let mut streams : Array Stream := #[]
  for hint in hints do
    if let some i := streams.findIdx? (fun s => s.name == hint.name) then
      streams := streams.modify i fun s => {s with entries := s.entries.push hint.values}
    else streams := streams.push ⟨hint.name, #[hint.values], 0⟩
  return streams

def liftError [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

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

def tracedRun (fuel : Nat) (program : Array Op) (hints : Array (Array RHint))
    (r : Runtime) (stopAt : Option Nat := none) : IO Runtime := do
  let mut cur := r
  for _ in [:fuel] do
    if cur.state.pc+1 == program.size && cur.state.fp == 0 then return cur
    if let some limit := stopAt then
      if cur.state.cycles >= limit then return cur
    if cur.state.cycles % 100000 == 0 then
      let diagnostic ← IO.getStderr
      let time ← IO.monoNanosNow
      let msg1 := s!"VM_PROGRESS mono_ns={time} cycles={cur.state.cycles} pc={cur.state.pc} fp={cur.state.fp} "
      let msg2 := s!"nextFree={cur.state.nextFree} used={cur.state.memory.used} "
      let msg3 := s!"links={cur.state.memory.links.size} powers={cur.state.g.powers.size}"
      diagnostic.putStrLn (msg1 ++ msg2 ++ msg3)
      diagnostic.flush
    let op ← liftError (match program[cur.state.pc]? with
      | some op => Except.ok op
      | none => Except.error Fault.badProgram)
    let ready ← liftError (Model.Vm.applyHintsLinear (hints[cur.state.pc]?.getD #[]) cur)
    let ⟨ready, streams⟩ := ready
    let state ← liftError (Model.Vm.stepLinear op ready)
    cur := ⟨state, streams⟩
  throw (IO.userError "VM diagnostic fuel exhausted")

def runFull (input output : System.FilePath) : IO Unit := do
  let diagnostic ← IO.getStderr
  diagnostic.putStrLn "VM_STAGE parsing"
  let raw ← liftError (parseRaw (← IO.FS.readBinFile input))
  let seed ← IO.FS.readBinFile (Tests.Xmss.childPath output "seed.bin")
  let valueBytes ← IO.FS.readBinFile (Tests.Xmss.childPath output "bytecode-value.bin")
  let value : Spec.Field.E := ⟨readLE valueBytes 0 8,0,0⟩
  let digest := statementDigest seed (sortedUnique raw) value
  let hints ← liftError (workloadHints #[packCell seed, packCell seed 16] raw value)
  diagnostic.putStrLn s!"VM_STAGE hints_ready entries={hints.size}"
  let program ← liftError (Spec.Vm.load (← IO.FS.readBinFile (Tests.Xmss.childPath output "bytecode.bin")))
  let (frame, schedule) ← liftError (readSchedule (← IO.FS.readBinFile (Tests.Xmss.childPath output "schedule.bin")) program.size)
  let state ← liftError (Model.Vm.initial frame #[packCell digest, packCell digest 16] program.size)
  diagnostic.putStrLn s!"VM_STAGE schedule_ready frame={frame} instructions={program.size}"
  let streams := streamsOf hints
  diagnostic.putStrLn s!"VM_STAGE streams_ready count={streams.size}"
  diagnostic.flush
  let stopAt := (← IO.getEnv "SHARD_C_PROFILE_CYCLES").bind asciiNat
  let result ← tracedRun 100000000 program schedule ⟨state,streams⟩ stopAt
  if stopAt.isSome then
    let time ← IO.monoNanosNow
    let msg := s!"VM_PROFILE_STOP mono_ns={time} cycles={result.state.cycles} " ++
      s!"used={result.state.memory.used} powers={result.state.g.powers.size}"
    diagnostic.putStrLn msg
    diagnostic.flush
    return
  diagnostic.putStrLn s!"VM_STAGE execution_ready cycles={result.state.cycles}"
  diagnostic.flush
  let s := result.state
  unless s.memory.unconstrainedReads.isEmpty do throw (IO.userError "unconstrained reads")
  if raw.size == 1400 then
    unless s.cycles == 1146537 do throw (IO.userError s!"wrong cycle count: {s.cycles}")
  let memory := serializeMemory s.memory.cells s.memory.used
  let hash := Tests.Xmss.hex (Spec.Vm.KeccakInternal.hash memory)
  let report := s!"cycles={s.cycles} memory_cells_used={s.memory.used} " ++
    s!"memory_keccak256={hash} counts={s.opcodeCounts} unconstrained_reads=[]"
  IO.FS.writeFile (Tests.Xmss.childPath output "lean-execution.txt") report
  IO.println report

end LeanVmXmss.Tests.Vm
