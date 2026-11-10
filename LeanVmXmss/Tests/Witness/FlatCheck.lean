import Tests.Vm.RuntimeIO
import Model.Witness.Flat

open LeanVmXmss
open LeanVmXmss.Spec.Vm
open LeanVmXmss.Spec.Field (E)
open LeanVmXmss.Model.Witness

def setK (offset value : Nat) : Op := .set offset ⟨UInt64.ofNat value, 0, 0⟩

def padPow2 (ops : Array Op) : Array Op :=
  let target := max 2 (1 <<< Spec.Layout.log2Ceil (ops.size + 1))
  let padded := Model.Pcs.Ntt.foldRange (target - 1 - ops.size)
    (fun acc _ => acc.push (setK 0 0)) ops
  padded.push (.xor 0 0 0)

def synthetic (name : String) : Array Op × Nat :=
  match name with
  | "syn_tiny" =>
    (padPow2 #[setK 2 5, setK 3 9, .xor 2 3 4, setK 5 7, .mul 4 5 6,
      setK 8 1, setK 9 0, setK 10 0], 16)
  | "syn_jump" =>
    (padPow2 #[setK 2 1, setK 3 32, setK 4 1, .jump 2 3 4, setK 5 9,
      setK 6 0, setK 7 1, .jump 6 7 4], 16)
  | "syn_deref" =>
    (padPow2 #[setK 2 64, setK 3 11, .deref 2 0 3 .cell, .deref 2 1 0 .pc,
      .deref 2 2 0 .fp, setK 12 0, setK 13 0, setK 14 0], 16)
  | _ =>
    (padPow2 #[setK 2 0x1111, setK 3 0x2222, setK 4 0, setK 5 0, setK 6 0,
      setK 7 0, setK 8 0, setK 9 0, setK 10 0, setK 11 0, setK 12 0,
      setK 13 0, setK 14 0, .keccak #[2, 3, 4, 5] 6 10 11 16 false true,
      .keccak #[16, 17, 18, 19] 20 24 25 30 true false], 64)

def hexDigits : Array Char :=
  #['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f']

def hexByte (byte : UInt8) : String :=
  String.ofList [hexDigits[(byte.toNat >>> 4) % 16]?.getD '0', hexDigits[byte.toNat % 16]?.getD '0']

def hexBytes (bytes : ByteArray) : String :=
  bytes.data.foldl (fun acc byte => acc ++ hexByte byte) ""

def hexLimb (value : UInt64) : String :=
  String.ofList <|
    Model.Pcs.Ntt.foldRange 16
      (fun acc step =>
        let shift := 60 - 4 * step
        let digit := (value >>> UInt64.ofNat shift).toNat % 16
        if acc.isEmpty && digit == 0 && step != 15 then acc
        else acc ++ [hexDigits[digit]?.getD '0'])
      []

def limbs (value : E) : String :=
  hexLimb value.c0 ++ "," ++ hexLimb value.c1 ++ "," ++ hexLimb value.c2

def counts (rows : Array Nat) : String :=
  rows.foldl (fun acc n => acc ++ (if acc.isEmpty then "" else ",") ++ toString n) ""

def ivOf (program : Array Op) : ByteArray :=
  let columns := Model.Layout.bytecodeColumnsFast program
  let logBytecode := Spec.Witness.log2FloorPow2 program.size
  Model.Layout.fiatShamirIvFast (Model.Layout.stackBytecodeColumnsFast logBytecode columns)

def emitCase (name : String) (program : Array Op) (frame : Nat) (hints : Array (Array RHint))
    (streams : Array Stream) (publicInput : Array E) (fuel : Nat) : IO String := do
  let state ← Tests.Vm.liftError (Model.Vm.initial frame publicInput program.size)
  let t0 ← IO.monoMsNow
  let iv ← IO.lazyPure (fun () => ivOf program)
  let tIv ← IO.monoMsNow
  let traceRes ← IO.lazyPure (fun () => executeTrace fuel program hints ⟨state, streams⟩)
  let trace ← Tests.Vm.liftError traceRes
  let tExec ← IO.monoMsNow
  let initInput := #[Spec.Witness.cellWord state.memory 0, Spec.Witness.cellWord state.memory 1]
  let bundle ← IO.lazyPure (fun () => bundleOf program iv initInput trace)
  let t1 ← IO.monoMsNow
  let sized := bundle.sized
  let roots := Spec.Merkle.hashToScalars bundle.root
  let lines :=
    "CASE|" ++ name ++ "\n" ++
    "EXEC|" ++ toString sized.trace.cycles ++ "|" ++ toString sized.trace.memUsed ++ "|" ++
      toString sized.logMem ++ "|" ++ counts sized.rows ++ "|" ++ toString sized.trace.unconstrained ++ "\n" ++
    "ANNOUNCE|" ++ hexBytes bundle.announce ++ "\n" ++
    "ROOT|" ++ limbs roots.1 ++ "|" ++ limbs roots.2 ++ "\n" ++
    "CHAL|" ++ limbs bundle.challenge ++ "|" ++ limbs bundle.official ++ "\n"
  IO.eprintln s!"TIMING_MS|{name}|total={t1 - t0}|iv={tIv - t0}|exec={tExec - tIv}|bundle={t1 - tExec}"
  IO.print lines
  return lines

def decodeAscii (bytes : ByteArray) : Except String String := do
  let list := bytes.data.toList
  if list.any (fun b => b.toNat >= 128) then throw "non-ASCII hint name"
  return String.ofList (list.map fun b =>
    if h : b.toNat.isValidChar then Char.ofNatAux b.toNat h else '?')

def readHints (bytes : ByteArray) : Except String (Array Spec.Xmss.HintEntry) := do
  let mut offset := 0
  let mut hints : Array Spec.Xmss.HintEntry := #[]
  while offset < bytes.size do
    if offset + 4 > bytes.size then throw "truncated hint name"
    let nameLen := (Spec.Xmss.readLE bytes offset 4).toNat
    offset := offset + 4
    if offset + nameLen + 4 > bytes.size then throw "truncated hint"
    let name ← decodeAscii (bytes.extract offset (offset + nameLen))
    offset := offset + nameLen
    let count := (Spec.Xmss.readLE bytes offset 4).toNat
    offset := offset + 4
    let mut values : Array E := #[]
    for _ in [:count] do
      if offset + 24 > bytes.size then throw "truncated hint word"
      values := values.push ⟨Spec.Xmss.readLE bytes offset 8,
        Spec.Xmss.readLE bytes (offset + 8) 8,
        Spec.Xmss.readLE bytes (offset + 16) 8⟩
      offset := offset + 24
    hints := hints.push ⟨name, values⟩
  return hints

def main (arguments : List String) : IO Unit := do
  let mode := arguments.head?.getD "synthetic"
  if mode == "synthetic" || mode == "all" then
    let mut rendered := ""
    for name in ["syn_tiny", "syn_jump", "syn_deref", "syn_keccak"] do
      let case := synthetic name
      let out ← emitCase name case.1 case.2 (Array.replicate case.1.size #[]) #[]
        #[Spec.Field.zero, Spec.Field.zero] 100
      rendered := rendered ++ out
    let expected ← IO.FS.readFile "Tests/Witness/evidence/oracle/synthetic.txt"
    if rendered != expected then
      throw (IO.userError "synthetic oracle mismatch")
    IO.eprintln "SYNTHETIC_PARITY|PASS"
  if mode == "xmss" || mode == "all" then
    let directory := arguments[1]?.getD ""
    let caseName := arguments[2]?.getD "xmss1400"
    let program ← Tests.Vm.liftError
      (load (← IO.FS.readBinFile (directory ++ "/bytecode.bin")))
    let schedule ← Tests.Vm.liftError
      (Tests.Vm.readSchedule (← IO.FS.readBinFile (directory ++ "/schedule.bin")) program.size)
    let hints ← Tests.Vm.liftError
      (readHints (← IO.FS.readBinFile (directory ++ "/hints.bin")))
    let streams ← IO.lazyPure (fun () => Tests.Vm.streamsOf hints)
    let statement ← IO.FS.readBinFile (directory ++ "/statement.bin")
    let publicInput : Array E :=
      #[⟨Spec.Xmss.readLE statement 0 8, Spec.Xmss.readLE statement 8 8, 0⟩,
        ⟨Spec.Xmss.readLE statement 16 8, Spec.Xmss.readLE statement 24 8, 0⟩]
    let out ← emitCase caseName program schedule.1 schedule.2 streams publicInput 2000000
    if caseName == "xmss1400" then
      let expected ← IO.FS.readFile "Tests/Witness/evidence/oracle/xmss1400.txt"
      if out != expected then
        throw (IO.userError "xmss1400 oracle mismatch")
      IO.eprintln "XMSS1400_PARITY|PASS"
  if !(mode == "synthetic" || mode == "xmss" || mode == "all") then
    throw (IO.userError "usage: FlatCheck synthetic|xmss|all [oracle-dir] [case-name]")
