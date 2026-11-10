import Tests.Vm.RuntimeIO
import Model.Witness.Scalar
import Model.Bus.Scalar

open LeanVmXmss
open LeanVmXmss.Spec.Vm
open LeanVmXmss.Spec.Field (E)
open LeanVmXmss.Model.Witness
open LeanVmXmss.Model.Bus

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
  String.ofList [hexDigits[(byte.toNat >>> 4) % 16]?.getD '0',
    hexDigits[byte.toNat % 16]?.getD '0']

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

def pushLe64 (ba : ByteArray) (w : UInt64) : ByteArray :=
  Model.Pcs.Ntt.foldRange 8
    (fun acc i => acc.push ((w >>> UInt64.ofNat (8 * i)).toUInt8))
    ba

def hashWords (words : @& Array E) : String :=
  let bytes := Model.Pcs.Ntt.foldRange words.size
    (fun acc idx =>
      let w := words[idx]?.getD Spec.Field.zero
      pushLe64 (pushLe64 (pushLe64 acc w.c0) w.c1) w.c2)
    (ByteArray.emptyWithCapacity (words.size * 24))
  hexBytes (Model.Layout.keccak256Stream bytes)

def hashSlotClaims (slots : @& Array SlotClaim) : String :=
  let words := Model.Pcs.Ntt.foldRange slots.size
    (fun acc idx =>
      let sc := slots[idx]?.getD default
      let hdr : E := ⟨UInt64.ofNat sc.offset, UInt64.ofNat sc.lowPoint.size, 0⟩
      ((acc.push hdr) ++ sc.lowPoint).push sc.value)
    #[]
  hashWords words

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
  let tBundle ← IO.monoMsNow
  let stage ← IO.lazyPure (fun () =>
    proveBusAndConstraints program iv initInput bundle)
  let tBus ← IO.monoMsNow
  let (probe, _) := sampleChallenge stage.ps
  let lines :=
    "CASE|" ++ name ++ "\n" ++
    "STREAM|" ++ toString stage.ps.stream.size ++ "|" ++ hashWords stage.ps.stream ++ "\n" ++
    "PROBE|" ++ limbs probe ++ "\n" ++
    "KECCAK_OUT|" ++ toString stage.keccakOutput.instancePoint.size ++ "|" ++
      hashWords stage.keccakOutput.instancePoint ++ "|" ++
      hashWords stage.keccakOutput.lanes ++ "\n" ++
    "SLOTS|" ++ toString stage.slotClaims.size ++ "|" ++
      hashSlotClaims stage.slotClaims ++ "\n"
  IO.eprintln
    s!"TIMING_MS|{name}|total={tBus - t0}|iv={tIv - t0}|exec={tExec - tIv}|bundle={tBundle - tExec}|bus={tBus - tBundle}"
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
    let expected ← IO.FS.readFile "Tests/Bus/evidence/oracle/synthetic.txt"
    if rendered != expected then
      throw (IO.userError "synthetic bus oracle mismatch")
    IO.eprintln "SYNTHETIC_PARITY|PASS"
  if mode == "xmss" || mode == "all" then
    let directory := arguments[1]?.getD ""
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
    let out ← emitCase "xmss1400" program schedule.1 schedule.2 streams
      publicInput 2000000
    let expected ← IO.FS.readFile "Tests/Bus/evidence/oracle/xmss1400.txt"
    if out != expected then
      throw (IO.userError "xmss1400 bus oracle mismatch")
    IO.eprintln "XMSS1400_PARITY|PASS"
  if !(mode == "synthetic" || mode == "xmss" || mode == "all") then
    throw (IO.userError "usage: Check synthetic|xmss|all [oracle-dir]")
