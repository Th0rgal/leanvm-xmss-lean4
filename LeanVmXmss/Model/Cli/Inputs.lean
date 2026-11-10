import Model.Xmss.Hints
import Spec.Vm.Bytecode
import Spec.Vm.Hints

/-!
The CLI-facing input pipeline for the leaf aggregate: raw fixture loading, the
prover schedule reader, and the pure Lean statement/hints derivation that mirrors
`rec_aggregation` for a workload of raw leanXMSS records.

Everything here is a thin re-arrangement of the audited `Spec.Xmss` pipeline:
`statementOf` is `Spec.Xmss.statementDigest`, `hintsOf` is
`Spec.Xmss.workloadHints`, `encodeHints` is the `hints.bin` encoding, and
`streamsOfHints` groups hint entries into the named streams the VM consumes.
-/

namespace LeanVmXmss.Model.Cli

open Spec.Xmss Spec.Vm

/-- Path join that avoids `System.FilePath` separator elaboration surprises. -/
def childPath (base : System.FilePath) (name : String) : System.FilePath :=
  ⟨base.toString ++ "/" ++ name⟩

def liftText {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error e => throw (IO.userError e)

def liftFault {α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error e => throw (IO.userError (reprStr e))

/-! ### Raw fixture loading -/

/-- Parse an `xmss-inputs.bin` image into raw records. -/
def loadRawInputs (path : System.FilePath) : IO (Array RawSignature) := do
  liftText (parseRaw (← IO.FS.readBinFile path))

def loadBytecode (path : System.FilePath) : IO (Array Op) := do
  liftText (Spec.Vm.load (← IO.FS.readBinFile path))

/-- The Fiat-Shamir seed, 32 bytes. -/
def loadSeed (path : System.FilePath) : IO ByteArray :=
  IO.FS.readBinFile path

/-- The deferred bytecode value: the stacked bytecode table's first word. -/
def loadBytecodeValue (path : System.FilePath) : IO Spec.Field.E := do
  let bytes ← IO.FS.readBinFile path
  if bytes.size < 8 then throw (IO.userError s!"{path}: truncated bytecode value")
  return ⟨readLE bytes 0 8, 0, 0⟩

def loadStatement (path : System.FilePath) : IO ByteArray :=
  IO.FS.readBinFile path

/-! ### The prover schedule reader (mirror of `Tests.Vm.RuntimeIO`) -/

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

/-- Decode `schedule.bin`: the main frame size and the per-pc prover hints. -/
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

/-- The guest program, main frame, and prover schedule of an oracle directory. -/
def loadGuest (dir : System.FilePath) : IO (Array Op × Nat × Array (Array RHint)) := do
  let program ← loadBytecode (childPath dir "bytecode.bin")
  let (frame, schedule) ← liftText
    (readSchedule (← IO.FS.readBinFile (childPath dir "schedule.bin")) program.size)
  return (program, frame, schedule)

/-! ### The aggregate pipeline -/

/-- The deduplicated, sorted signer set of a raw workload. -/
def signersOf (raw : Array RawSignature) : Array RawSignature := sortedUnique raw

/-- The aggregate statement digest over the sorted, deduplicated raw records. -/
def statementOf (seed : ByteArray) (raw : Array RawSignature) (bytecodeValue : Spec.Field.E) : ByteArray :=
  statementDigest seed (sortedUnique raw) bytecodeValue

/-- The aggregate witness hints over the raw (unsorted) records. -/
def hintsOf (seed : ByteArray) (raw : Array RawSignature)
    (bytecodeValue : Spec.Field.E) : Except String (Array HintEntry) :=
  workloadHints #[packCell seed, packCell seed 16] raw bytecodeValue

/-- The `hints.bin` wire encoding of a hint list. -/
def encodeHints (hints : Array HintEntry) : ByteArray := hints.foldl (fun acc h =>
  let name := h.name.toUTF8
  let header := writeLE name.size.toUInt64 4 ++ name ++ writeLE h.values.size.toUInt64 4
  let words := h.values.foldl (fun bytes x =>
      bytes ++ writeLE x.c0 8 ++ writeLE x.c1 8 ++ writeLE x.c2 8) ByteArray.empty
  acc ++ header ++ words) ByteArray.empty

/-- Group hint entries into the named witness streams the VM pops entries from. -/
def streamsOfHints (hints : Array HintEntry) : Array Stream := Id.run do
  let mut streams : Array Stream := #[]
  for hint in hints do
    if let some i := streams.findIdx? (fun s => s.name == hint.name) then
      streams := streams.modify i fun s => {s with entries := s.entries.push hint.values}
    else streams := streams.push ⟨hint.name, #[hint.values], 0⟩
  return streams

def hex (bytes : ByteArray) : String := String.ofList (bytes.data.toList.flatMap fun b =>
  let digits := #[ '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f' ]
  [digits[b.toNat/16]!, digits[b.toNat%16]!])

end LeanVmXmss.Model.Cli
