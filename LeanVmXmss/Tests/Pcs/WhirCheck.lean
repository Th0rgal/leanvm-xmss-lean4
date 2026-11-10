import Model.Pcs.Ntt
import Model.Pcs.RingSwitch
import Model.Pcs.StackOpen
import Model.Pcs.Whir
import Model.Aggregate.Wire
import Model.Bus.Scalar
import Model.Witness.Scalar
import Tests.Vm.RuntimeIO

open LeanVmXmss
open LeanVmXmss.Spec.Field (E K)

def setK (offset value : Nat) : Spec.Vm.Op := .set offset ⟨UInt64.ofNat value, 0, 0⟩

def padPow2 (ops : Array Spec.Vm.Op) : Array Spec.Vm.Op :=
  let target := max 2 (1 <<< Spec.Layout.log2Ceil (ops.size + 1))
  let padded := Model.Pcs.Ntt.foldRange (target - 1 - ops.size)
    (fun acc _ => acc.push (setK 0 0)) ops
  padded.push (.xor 0 0 0)

def ivOf (program : Array Spec.Vm.Op) : ByteArray :=
  let columns := Model.Layout.bytecodeColumnsFast program
  let logBytecode := Spec.Witness.log2FloorPow2 program.size
  Model.Layout.fiatShamirIvFast (Model.Layout.stackBytecodeColumnsFast logBytecode columns)

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

def hexDigits : Array Char :=
  #['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f']

def hexByte (byte : UInt8) : String :=
  String.ofList [hexDigits[(byte.toNat >>> 4) % 16]?.getD '0', hexDigits[byte.toNat % 16]?.getD '0']

def hexBytes (bytes : ByteArray) : String :=
  bytes.data.foldl (fun acc byte => acc ++ hexByte byte) ""

def hexLimb (value : UInt64) : String :=
  String.ofList <|
    LeanVmXmss.Model.Pcs.Ntt.foldRange 16
      (fun acc step =>
        let digit := (value >>> UInt64.ofNat (60 - 4 * step)).toNat % 16
        if acc.isEmpty && digit == 0 && step != 15 then acc
        else acc ++ [hexDigits[digit]?.getD '0'])
      []

def limbs (value : E) : String :=
  hexLimb value.c0 ++ "," ++ hexLimb value.c1 ++ "," ++ hexLimb value.c2

def elem (seed tag : UInt64) : E :=
  ⟨seed * 0x9e3779b97f4a7c15 + tag,
   seed * 0xbf58476d1ce4e5b9 + (tag <<< (1 : UInt64)),
   seed * 0x94d049bb133111eb + (tag <<< (2 : UInt64))⟩

def nums (values : Array Nat) : String :=
  values.foldl (fun acc value => if acc.isEmpty then toString value else acc ++ "," ++ toString value) ""

def main (args : List String) : IO Unit := do
  let mode := args.head?.getD "synthetic"
  let challenges := LeanVmXmss.Model.Pcs.Ntt.foldRange 6 (fun acc index => acc.push (elem 0x111 (UInt64.ofNat index))) #[]
  let point := LeanVmXmss.Model.Pcs.Ntt.foldRange 4 (fun acc index => acc.push (elem 0x222 (UInt64.ofNat index))) #[]
  let prime := LeanVmXmss.Model.Pcs.Ntt.foldRange 4 (fun acc index => acc.push (elem 0x333 (UInt64.ofNat index))) #[]
  let slices := LeanVmXmss.Model.Pcs.Ntt.foldRange 64 (fun acc index => acc.push (elem 0x444 (UInt64.ofNat index))) #[]
  let coefficients := LeanVmXmss.Model.Pcs.RingSwitch.frobeniusCoefficients challenges
  let images := slices.map fun slice => LeanVmXmss.Model.Pcs.RingSwitch.applyComposed slice challenges
  IO.println <|
    "RING|mapped=" ++ limbs (LeanVmXmss.Model.Pcs.RingSwitch.applyComposed (slices.getD 3 LeanVmXmss.Spec.Field.zero) challenges) ++
    "|weight=" ++ limbs (LeanVmXmss.Model.Pcs.RingSwitch.ringWeightAt point prime coefficients) ++
    "|target=" ++ limbs (LeanVmXmss.Model.Pcs.Whir.polyEval images ⟨2, 0, 0⟩)
  let mut configs := ""
  for logN in [15, 16, 20, 28] do
    for rate in [1, 2, 3, 4] do
      match LeanVmXmss.Model.Pcs.Whir.deriveConfig logN rate with
      | none => pure ()
      | some config =>
        configs := configs ++ toString logN ++ ":" ++ toString rate ++ ":" ++
          nums config.logInvRates ++ ":" ++ nums config.folds ++ ":" ++ nums config.queries ++ "|"
  IO.println ("WHIR|" ++ configs)
  let sample := elem 0x555 7
  let windows := LeanVmXmss.Model.Pcs.Ntt.foldRange 4
    (fun acc chunk => acc.push (toString (LeanVmXmss.Model.Pcs.Whir.sampleWindow sample 9 chunk))) #[]
  IO.println ("WINDOW|" ++ windows.foldl (fun acc value => if acc.isEmpty then value else acc ++ "," ++ value) "")
  let table : Array K := LeanVmXmss.Model.Pcs.Ntt.foldRange 16 (fun acc index => acc.push (0x1000 + UInt64.ofNat index)) #[]
  let evalPoint := LeanVmXmss.Model.Pcs.Ntt.foldRange 4 (fun acc index => acc.push (elem 0x666 (UInt64.ofNat index))) #[]
  IO.println ("MLE|" ++ limbs (LeanVmXmss.Model.Pcs.Whir.multilinearEval table evalPoint))
  IO.println ("EQ|" ++ limbs (LeanVmXmss.Model.Pcs.StackOpen.eqEval point prime))
  IO.println ("POLY|" ++ limbs (LeanVmXmss.Model.Pcs.Whir.polyEval #[elem 1 0, elem 2 0, elem 3 0, elem 4 0] (elem 9 1)))
  if mode == "synthetic" || mode == "all" then
    IO.println ("DA|syn_tiny|" ++ hexBytes (LeanVmXmss.Model.Aggregate.Wire.daDigest none))
    IO.println ("DA|syn_jump|" ++ hexBytes (LeanVmXmss.Model.Aggregate.Wire.daDigest (some ⟨Array.replicate 32 7⟩)))
    IO.println ("DA|syn_deref|" ++ hexBytes (LeanVmXmss.Model.Aggregate.Wire.daDigest none))
    IO.println ("DA|syn_keccak|" ++ hexBytes (LeanVmXmss.Model.Aggregate.Wire.daDigest (some ⟨Array.replicate 32 9⟩)))
  if mode == "oracle" || mode == "all" then
    for name in ["xmss4", "xmss16"] do
      let bytes ← IO.FS.readBinFile ("/var/lib/orb-node/work/caches/xmss-hub-v3/oracle/" ++ name ++ "/seed.bin")
      IO.println ("DA|" ++ name ++ "|" ++ hexBytes (LeanVmXmss.Model.Aggregate.Wire.daDigest (some (bytes.extract 0 32))))
  IO.println ("PARITY_DONE|" ++ mode)
  if mode == "probe" then
    IO.println "PROBE|start"
    let program := padPow2 #[setK 2 5, setK 3 9, .xor 2 3 4, setK 5 7, .mul 4 5 6, setK 8 1, setK 9 0, setK 10 0]
    IO.println s!"PROBE|ops={program.size}"
    let state ← Tests.Vm.liftError (Model.Vm.initial 16 #[Spec.Field.zero, Spec.Field.zero] program.size)
    IO.println "PROBE|state"
    let trace ← Tests.Vm.liftError (Model.Witness.executeTrace 100 program (Array.replicate program.size #[]) ⟨state, #[]⟩)
    IO.println s!"PROBE|cycles={trace.cycles}"
    let iv := ivOf program
    IO.println "PROBE|iv"
    let bundle := Model.Witness.bundleOf program iv #[Spec.Field.zero, Spec.Field.zero] trace
    IO.println s!"PROBE|mu={bundle.sized.layout.shape.mu}|words={bundle.message.size}"
    return
  if mode == "splice" then
    IO.println "SPLICE|enter"
    (← IO.getStdout).flush
    let name := args.getD 1 "syn_tiny"
    let prepcsPath := args.getD 2 "/tmp/opencode/syn_tiny.prepcs"
    let outPath := args.getD 3 "/tmp/opencode/syn_tiny.proof"
    let dir := args.getD 4 ("/var/lib/orb-node/work/caches/xmss-hub-v3/oracle/" ++ name)
    let bundle ← if name.startsWith "syn_" then do
      let case : Array Spec.Vm.Op × Nat := match name with
        | "syn_tiny" => (padPow2 #[setK 2 5, setK 3 9, .xor 2 3 4, setK 5 7, .mul 4 5 6,
            setK 8 1, setK 9 0, setK 10 0], 16)
        | "syn_jump" => (padPow2 #[setK 2 1, setK 3 32, setK 4 1, .jump 2 3 4, setK 5 9,
            setK 6 0, setK 7 1, .jump 6 7 4], 16)
        | "syn_deref" => (padPow2 #[setK 2 64, setK 3 11, .deref 2 0 3 .cell, .deref 2 1 0 .pc,
            .deref 2 2 0 .fp, setK 12 0, setK 13 0, setK 14 0], 16)
        | _ => (padPow2 #[setK 2 0x1111, setK 3 0x2222, setK 4 0, setK 5 0, setK 6 0,
            setK 7 0, setK 8 0, setK 9 0, setK 10 0, setK 11 0, setK 12 0,
            setK 13 0, setK 14 0, .keccak #[2, 3, 4, 5] 6 10 11 16 false true,
            .keccak #[16, 17, 18, 19] 20 24 25 30 true false], 64)
      let program := case.1
      let state ← Tests.Vm.liftError
        (Model.Vm.initial case.2 #[Spec.Field.zero, Spec.Field.zero] program.size)
      let iv := ivOf program
      let trace ← Tests.Vm.liftError
        (Model.Witness.executeTrace 100 program (Array.replicate program.size #[]) ⟨state, #[]⟩)
      IO.println "SPLICE|trace"
      (← IO.getStdout).flush
      pure (Model.Witness.bundleOf program iv #[Spec.Field.zero, Spec.Field.zero] trace)
    else do
      let program ← Tests.Vm.liftError (Spec.Vm.load (← IO.FS.readBinFile (dir ++ "/bytecode.bin")))
      let schedule ← Tests.Vm.liftError
        (Tests.Vm.readSchedule (← IO.FS.readBinFile (dir ++ "/schedule.bin")) program.size)
      let hints ← Tests.Vm.liftError (readHints (← IO.FS.readBinFile (dir ++ "/hints.bin")))
      let streams := Tests.Vm.streamsOf hints
      let statement ← IO.FS.readBinFile (dir ++ "/statement.bin")
      let publicInput : Array E :=
        #[⟨Spec.Xmss.readLE statement 0 8, Spec.Xmss.readLE statement 8 8, 0⟩,
          ⟨Spec.Xmss.readLE statement 16 8, Spec.Xmss.readLE statement 24 8, 0⟩]
      let state ← Tests.Vm.liftError (Model.Vm.initial schedule.1 publicInput program.size)
      let iv := ivOf program
      let trace ← Tests.Vm.liftError
        (Model.Witness.executeTrace 2000000 program schedule.2 ⟨state, streams⟩)
      let initInput := #[Spec.Witness.cellWord state.memory 0, Spec.Witness.cellWord state.memory 1]
      pure (Model.Witness.bundleOf program iv initInput trace)
    IO.println s!"SPLICE|mu={bundle.sized.layout.shape.mu}"
    (← IO.getStdout).flush
    let raw ← IO.FS.readBinFile prepcsPath
    let c0 : Spec.Aggregate.Wire.Cursor := ⟨raw, 0⟩
    let some (ivB, c1) := Spec.Aggregate.Wire.Cursor.take c0 32 | throw (IO.userError "iv")
    let some (piB, c2) := Spec.Aggregate.Wire.Cursor.take c1 32 | throw (IO.userError "pi")
    let some (nOps, c3) := Spec.Aggregate.Wire.Cursor.usize c2 | throw (IO.userError "ops len")
    let some (opsB, c4) := Spec.Aggregate.Wire.Cursor.take c3 nOps | throw (IO.userError "ops")
    let some (nStream, c5) := Spec.Aggregate.Wire.Cursor.usize c4 | throw (IO.userError "stream len")
    let some (stream, c6) :=
      Spec.Aggregate.Wire.Cursor.repeat nStream Spec.Aggregate.Wire.Cursor.elem c5
      | throw (IO.userError "stream")
    let some (nSlots, c7) := Spec.Aggregate.Wire.Cursor.usize c6 | throw (IO.userError "slots")
    let mut cursor := c7
    let mut points : Array Spec.Pcs.StackOpen.StackClaim := #[]
    for _ in [:nSlots] do
      let some (off, c) := Spec.Aggregate.Wire.Cursor.usize cursor | throw (IO.userError "off")
      let some (nv, c) := Spec.Aggregate.Wire.Cursor.usize c | throw (IO.userError "nv")
      let some (pt, c) := Spec.Aggregate.Wire.Cursor.repeat nv Spec.Aggregate.Wire.Cursor.elem c | throw (IO.userError "pt")
      let some (val, c) := Spec.Aggregate.Wire.Cursor.elem c | throw (IO.userError "val")
      points := points.push (.point off pt val)
      cursor := c
    let some (ringOff, c8) := Spec.Aggregate.Wire.Cursor.usize cursor | throw (IO.userError "ring off")
    let some (ringVars, c9) := Spec.Aggregate.Wire.Cursor.usize c8 | throw (IO.userError "ring vars")
    let some (ringPt, c10) :=
      Spec.Aggregate.Wire.Cursor.repeat ringVars Spec.Aggregate.Wire.Cursor.elem c9
      | throw (IO.userError "ring pt")
    let some (slices, c11) :=
      Spec.Aggregate.Wire.Cursor.repeat 64 Spec.Aggregate.Wire.Cursor.elem c10
      | throw (IO.userError "slices")
    IO.println s!"SPLICE|parsed|slots={points.size}|stream={stream.size}"
    (← IO.getStdout).flush
    if c11.pos != raw.size then throw (IO.userError "trailing")
    if args.getD 5 "" == "witness" then
      let mut bytes := ByteArray.empty
      bytes := Spec.Aggregate.Wire.putU64 bytes (UInt64.ofNat bundle.sized.layout.shape.mu)
      bytes := Spec.Aggregate.Wire.putU64 bytes (UInt64.ofNat bundle.message.size)
      for w in bundle.message do
        bytes := Spec.Aggregate.Wire.putU64 bytes w
      IO.FS.writeBinFile outPath bytes
      IO.println s!"WITNESS|{name}|mu={bundle.sized.layout.shape.mu}|words={bundle.message.size}"
      return
    let replay := opsB.data.foldl (fun (ps, i) op =>
      if op == 0 then
        (Spec.Transcript.addScalar ps (stream.getD i Spec.Field.zero), i + 1)
      else
        ((Spec.Transcript.sample ps).2, i)) (Spec.Transcript.proverNew ivB piB, 0)
    IO.println s!"SPLICE|replayed|i={replay.2}"
    (← IO.getStdout).flush
    if replay.2 != stream.size then throw (IO.userError "op/stream mismatch")
    let ps0 := replay.1
    let ring : Spec.Pcs.StackOpen.RingSwitchOpen := ⟨ringOff, #[⟨ringPt, slices⟩]⟩
    let mu := bundle.sized.layout.shape.mu
    let t0 ← IO.monoMsNow
    let some ps := Model.Pcs.Whir.provePcsOpen ps0 mu 1 bundle.message points ring
      | throw (IO.userError "provePcsOpen failed")
    IO.println s!"SPLICE|proved_ms={(← IO.monoMsNow) - t0}"
    let mut phases : Array Spec.Merkle.PrunedMerklePaths := #[]
    for phaseBytes in ps.merkle do
      let some (phase, pc) := Spec.Aggregate.Wire.Cursor.phase ⟨phaseBytes, 0⟩
        | throw (IO.userError "phase")
      if pc.pos != phaseBytes.size then throw (IO.userError "phase trailing")
      phases := phases.push phase
    let proof : Spec.Aggregate.Wire.VmProof := ⟨ps.stream, phases⟩
    IO.FS.writeBinFile outPath (Spec.Aggregate.Wire.putProof ByteArray.empty proof)
    IO.println s!"SPLICE_LEAN|{name}|stream={ps.stream.size}|merkle={phases.size}"
