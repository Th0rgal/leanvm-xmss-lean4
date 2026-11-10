import Tests.Vm.RuntimeIO
import Model.Witness.Scalar
import Model.KeccakGkr.Scalar

open LeanVmXmss
open LeanVmXmss.Spec.Vm
open LeanVmXmss.Spec.Field (E)
open LeanVmXmss.Spec.Bus (SlotClaim)
open LeanVmXmss.Model.Witness
open LeanVmXmss.Model.Bus (sampleChallenge)
open LeanVmXmss.Model.KeccakGkr

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

def keccakScalarCount (executed : Nat) : Nat :=
  let logSteps := Spec.KeccakGkr.stepsLog executed
  let yVars := logSteps - Spec.KeccakGkr.packBits + Spec.KeccakGkr.segLog
  let perLayer := Spec.KeccakGkr.productBits + 2 * yVars + 3 * Spec.KeccakGkr.localBits + 3
  let outScalars :=
    if Spec.KeccakGkr.segments > 1 then 1 + 2 * Spec.KeccakGkr.slotBits + 1 else 0
  let inScalars :=
    2 * Spec.KeccakGkr.packBits + 2 * Spec.KeccakGkr.slotBits + Spec.KeccakGkr.wordBits
  outScalars + Spec.Layout.keccakDepth * perLayer + inScalars

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
  let stage ← IO.lazyPure (fun () => proveKeccakGkr program iv initInput bundle)
  let tGkr ← IO.monoMsNow
  let executed := bundle.sized.rows[Spec.Layout.opKeccak]?.getD 0
  let kLen := keccakScalarCount executed
  let kStart := stage.ps.stream.size - kLen
  let kSlice := stage.ps.stream.extract kStart stage.ps.stream.size
  let (probe, _) := sampleChallenge stage.ps
  let dumpScalars := (← IO.getEnv "KECCAK_GKR_DUMP_SCALARS").isSome
  let scalarLines :=
    if dumpScalars then
      Model.Pcs.Ntt.foldRange kSlice.size
        (fun acc idx =>
          acc ++ "SCALAR|" ++ toString idx ++ "|" ++
            limbs (kSlice[idx]?.getD Spec.Field.zero) ++ "\n")
        ""
    else ""
  let outLine :=
    match stage.openings.outputs with
    | some wo =>
      "OUT_OPEN|1|" ++ toString stage.ringClaim.offset ++ "|" ++
        toString wo.point.size ++ "|" ++ hashWords wo.point ++ "|" ++ limbs wo.value ++ "\n"
    | none =>
      "OUT_OPEN|0|0|0||0,0,0\n"
  let ringLine :=
    "RING_OPEN|" ++ toString stage.ringClaim.offset ++ "|" ++
      toString stage.ringClaim.suffixPoint.size ++ "|" ++
      hashWords stage.ringClaim.suffixPoint ++ "|" ++
      toString stage.ringClaim.slices.size ++ "|" ++
      hashWords stage.ringClaim.slices ++ "\n"
  let lines :=
    "CASE|" ++ name ++ "\n" ++
    "STREAM|" ++ toString stage.ps.stream.size ++ "|" ++ hashWords stage.ps.stream ++ "\n" ++
    "KECCAK_SCALARS|" ++ toString kStart ++ "|" ++ toString kSlice.size ++ "|" ++
      hashWords kSlice ++ "\n" ++
    scalarLines ++
    "PROBE|" ++ limbs probe ++ "\n" ++
    outLine ++
    ringLine ++
    "SLOTS|" ++ toString stage.slotClaims.size ++ "|" ++ hashSlotClaims stage.slotClaims ++ "\n"
  IO.eprintln
    s!"TIMING_MS|{name}|total={tGkr - t0}|iv={tIv - t0}|exec={tExec - tIv}|bundle={tBundle - tExec}|bus_and_gkr={tGkr - tBundle}"
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

def runXmssCase (label directory : String) : IO String := do
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
  emitCase label program schedule.1 schedule.2 streams publicInput 2000000

def main (arguments : List String) : IO Unit := do
  let mode := arguments.head?.getD "synthetic"
  if mode == "synthetic" then
    let mut rendered := ""
    for name in ["syn_tiny", "syn_jump", "syn_deref", "syn_keccak"] do
      let case := synthetic name
      let out ← emitCase name case.1 case.2 (Array.replicate case.1.size #[]) #[]
        #[Spec.Field.zero, Spec.Field.zero] 100
      rendered := rendered ++ out
    let expected ← IO.FS.readFile "Tests/KeccakGkr/evidence/oracle/synthetic.txt"
    if rendered != expected then
      throw (IO.userError "synthetic keccak-gkr oracle mismatch")
    IO.eprintln "SYNTHETIC_PARITY|PASS"
  else if mode == "xmss" then
    let label := arguments[1]?.getD "xmss4"
    let directory := arguments[2]?.getD ""
    let _ ← runXmssCase label directory
  else if mode == "all" then
    let dir4 := arguments[1]?.getD ""
    let dir16 := arguments[2]?.getD ""
    let mut rendered := ""
    for name in ["syn_tiny", "syn_jump", "syn_deref", "syn_keccak"] do
      let case := synthetic name
      let out ← emitCase name case.1 case.2 (Array.replicate case.1.size #[]) #[]
        #[Spec.Field.zero, Spec.Field.zero] 100
      rendered := rendered ++ out
    let out4 ← runXmssCase "xmss4" dir4
    let out16 ← runXmssCase "xmss16" dir16
    rendered := rendered ++ out4 ++ out16
    let expected ← IO.FS.readFile "Tests/KeccakGkr/evidence/oracle/all.txt"
    if rendered != expected then
      throw (IO.userError "all keccak-gkr oracle mismatch")
    IO.eprintln "ALL_KECCAK_GKR_PARITY|PASS"
  else
    throw (IO.userError "usage: Check synthetic | xmss <label> <dir> | all <xmss4-dir> <xmss16-dir>")
