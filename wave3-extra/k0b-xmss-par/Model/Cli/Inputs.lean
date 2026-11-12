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
def signersOf (raw : Array RawSignature) : Array RawSignature :=
  Model.Xmss.sortedUniqueFast raw

/-- The aggregate statement digest over the sorted, deduplicated raw records. -/
def statementOf (seed : ByteArray) (raw : Array RawSignature) (bytecodeValue : Spec.Field.E) : ByteArray :=
  Model.Xmss.statementDigest seed (Model.Xmss.sortedUniqueFast raw) bytecodeValue

/-- The aggregate witness hints over the raw (unsorted) records. -/
def hintsOf (seed : ByteArray) (raw : Array RawSignature)
    (bytecodeValue : Spec.Field.E) : Except String (Array HintEntry) :=
  Model.Xmss.workloadHints #[packCell seed, packCell seed 16] raw bytecodeValue

/-- The aggregate witness hints with integrated root-signature verification. -/
def hintsOfVerified (seed : ByteArray) (raw : Array RawSignature)
    (bytecodeValue : Spec.Field.E) : Except String (Array HintEntry) :=
  Model.Xmss.workloadHintsVerified #[packCell seed, packCell seed 16] raw bytecodeValue

@[inline] def pushU32LE (b : ByteArray) (x : UInt64) : ByteArray :=
  b.push x.toUInt8
    |>.push (x >>> 8).toUInt8
    |>.push (x >>> 16).toUInt8
    |>.push (x >>> 24).toUInt8

def utf8Meta : ByteArray := "meta".toUTF8
def utf8FsSeed : ByteArray := "fs_seed".toUTF8
def utf8SignersSplit : ByteArray := "signers_split".toUTF8
def utf8Claims : ByteArray := "claims".toUTF8
def utf8RawIndex : ByteArray := "raw_index".toUTF8
def utf8LxIndex : ByteArray := "lx_index".toUTF8
def utf8LxWindows : ByteArray := "lx_windows".toUTF8
def utf8LxPath : ByteArray := "lx_path".toUTF8
def utf8Randomizer : ByteArray := "randomizer".toUTF8
def utf8LxDigits : ByteArray := "lx_digits".toUTF8
def utf8ChainStarts : ByteArray := "chain_starts".toUTF8
def utf8LeafDefer : ByteArray := "leaf_defer".toUTF8
def utf8DaPick : ByteArray := "da_pick".toUTF8

@[inline] def hintNameUTF8 (name : @& String) : ByteArray :=
  if name == "chain_starts" then utf8ChainStarts
  else if name == "lx_path" then utf8LxPath
  else if name == "randomizer" then utf8Randomizer
  else if name == "lx_digits" then utf8LxDigits
  else if name == "claims" then utf8Claims
  else if name == "raw_index" then utf8RawIndex
  else if name == "lx_index" then utf8LxIndex
  else if name == "lx_windows" then utf8LxWindows
  else if name == "meta" then utf8Meta
  else if name == "fs_seed" then utf8FsSeed
  else if name == "signers_split" then utf8SignersSplit
  else if name == "leaf_defer" then utf8LeafDefer
  else if name == "da_pick" then utf8DaPick
  else name.toUTF8

def hdrRawIndex : ByteArray := pushU32LE (pushU32LE ByteArray.empty 9 ++ "raw_index".toUTF8) 1
def hdrLxIndex : ByteArray := pushU32LE (pushU32LE ByteArray.empty 8 ++ "lx_index".toUTF8) 4
def hdrLxWindows : ByteArray := pushU32LE (pushU32LE ByteArray.empty 10 ++ "lx_windows".toUTF8) 4
def hdrLxPath : ByteArray := pushU32LE (pushU32LE ByteArray.empty 7 ++ "lx_path".toUTF8) 1
def hdrRandomizer : ByteArray := pushU32LE (pushU32LE ByteArray.empty 10 ++ "randomizer".toUTF8) 1
def hdrLxDigits : ByteArray := pushU32LE (pushU32LE ByteArray.empty 9 ++ "lx_digits".toUTF8) 15
def hdrChainStarts : ByteArray := pushU32LE (pushU32LE ByteArray.empty 12 ++ "chain_starts".toUTF8) 1

@[inline] def pushFieldBytes (b : ByteArray) (x : Spec.Field.E) : ByteArray :=
  Model.Keccak.pushU64LE (Model.Keccak.pushU64LE (Model.Keccak.pushU64LE b x.c0) x.c1) x.c2

@[inline] def pushPairBytes (b : ByteArray) (p : Model.Keccak.Pair64) : ByteArray :=
  pushFieldBytes b (Model.Xmss.packPair64 p)

@[inline] def pushHdr (b : ByteArray) (hdr : ByteArray) : ByteArray :=
  Fin.foldl hdr.size (fun acc i => if h : i.val < hdr.size then acc.push hdr[i.val] else acc) b

/-- Encode a slice `[start, start + len)` of hint entries into `init`. -/
def encodeHintsSliceInto (hints : @& Array HintEntry) (start len : Nat) (init : ByteArray) : ByteArray :=
  let chunkBytes := Fin.foldl len (fun sum k =>
    let idx := start + k.val
    if h : idx < hints.size then
      let entry := hints[idx]
      sum + 8 + entry.name.utf8ByteSize + entry.values.size * 24
    else sum) init.size
  let base := if init.size == 0 then ByteArray.emptyWithCapacity chunkBytes else
    let b := ByteArray.emptyWithCapacity chunkBytes
    Fin.foldl init.size (fun acc j =>
      if hj : j.val < init.size then acc.push init[j.val] else acc) b
  Fin.foldl len (fun acc k =>
    let idx := start + k.val
    if h : idx < hints.size then
      let entry := hints[idx]
      let name := hintNameUTF8 entry.name
      let acc := pushU32LE acc name.size.toUInt64
      let acc := Fin.foldl name.size (fun b j =>
        if hj : j.val < name.size then b.push name[j.val] else b) acc
      let acc := pushU32LE acc entry.values.size.toUInt64
      Fin.foldl entry.values.size (fun b j =>
        if hj : j.val < entry.values.size then
          pushFieldBytes b entry.values[j.val]
        else b) acc
    else acc) base

/-- Encode a slice `[start, start + len)` of hint entries. -/
def encodeHintsSlice (hints : @& Array HintEntry) (start len : Nat) : ByteArray :=
  encodeHintsSliceInto hints start len ByteArray.empty

/-- Stream-hash a hint list into its `hints.bin` Keccak-256 digest while encoding slices in parallel. -/
def hashEncodedHints (hints : Array HintEntry) : ByteArray :=
  let n := hints.size
  if n <= 512 then
    Model.Keccak.keccak256CPS (encodeHintsSlice hints 0 n)
  else
    let wCount := 16
    let tasks := Fin.foldl wCount (fun ts w =>
      let start := (w.val * n) / wCount
      let stop := ((w.val + 1) * n) / wCount
      let len := stop - start
      let t : Task ByteArray := Task.spawn fun () => encodeHintsSlice hints start len
      ts.push t) (Array.emptyWithCapacity wCount : Array (Task ByteArray))
    let (st, carry) := Fin.foldl tasks.size (fun (s, rem) w =>
      if h : w.val < tasks.size then
        Model.Keccak.absorbChunkCPS s rem tasks[w.val].get
      else (s, rem)) (Model.Keccak.zeroState25Fast, ByteArray.empty)
    Model.Keccak.finalizeKeccak256CPS st carry 0 carry.size

def signerLayerDirectBytes (pp : Model.Keccak.Pair64) (sig : @& ByteArray) (hsig : sig.size = 2404)
    (index layer : Nat) (hlayer : layer < 2)
    (out : ByteArray) (rootLo rootHi root2 root3 : UInt64) : Except String (ByteArray × Model.Keccak.Pair64) :=
  let offset := 4 + layer * 1200
  let e := index >>> (layer * 16)
  let rand := Model.Xmss.readPair64Proof sig offset (by omega)
  let addrMsg := Model.Xmss.addressLo 12 layer 0 e 0
  let digest : Model.Keccak.Pair64 :=
    if layer == 0 then
      let s0 := Model.Keccak.permuteAbsorb25 Model.Keccak.zeroState25Fast pp.lo pp.hi addrMsg 0
        rootLo rootHi root2 root3 rand.lo rand.hi 0x01 0 0 0 0 0 0x8000000000000000
      ⟨s0.a00, s0.a01⟩
    else
      Model.Keccak.keccak1Block16 pp.lo pp.hi addrMsg 0 rootLo rootHi rand.lo rand.hi 0x01
  match Model.Xmss.codeword58 digest with
  | none => .error "invalid WOTS+C codeword"
  | some digits =>
    let ends := Fin.foldl 58 (fun acc i =>
      let stOff := offset + 16 + i.val * 16
      let startVal := Model.Xmss.readPair64Proof sig stOff (by omega)
      let dig := digits[i.val]?.getD 0
      acc.push (Model.Xmss.chainFast pp layer e i.val dig startVal)) (Array.emptyWithCapacity 58)
    let leafRoot := Model.Xmss.hashLeafEnds pp layer e ends
    let (out, climbedRoot) := Fin.foldl 16 (fun st lv =>
      let level := lv.val
      let sibOff := offset + 944 + level * 16
      let sib := Model.Xmss.readPair64Proof sig sibOff (by omega)
      let b1 := pushPairBytes (pushHdr st.1 hdrLxPath) sib
      let cur := st.2
      let addrTree := Model.Xmss.addressLo 3 layer (level + 1) (e >>> (level + 1)) 0
      let nextRoot :=
        if ((e >>> level) &&& 1) == 0 then
          Model.Keccak.keccak1Block16 pp.lo pp.hi addrTree 0 cur.lo cur.hi sib.lo sib.hi 0x01
        else
          Model.Keccak.keccak1Block16 pp.lo pp.hi addrTree 0 sib.lo sib.hi cur.lo cur.hi 0x01
      (b1, nextRoot)) (out, leafRoot)
    let out := pushPairBytes (pushHdr out hdrRandomizer) rand
    let out := pushHdr out hdrLxDigits
    let out := Fin.foldl 15 (fun b g =>
      let grp := g.val
      let cnt := min 4 (58 - grp * 4)
      let val := Fin.foldl cnt (fun n j =>
        let d := digits[grp * 4 + j.val]?.getD 0
        n + d * (1 <<< (2 * j.val))) 0
      pushFieldBytes b (Model.Xmss.countFast val)) out
    let out := Fin.foldl 58 (fun b i =>
      let stOff := offset + 16 + i.val * 16
      let startCell := Model.Xmss.packCellProof sig stOff (by omega)
      pushFieldBytes (pushHdr b hdrChainStarts) startCell) out
    .ok (out, climbedRoot)

def signerDirectBytes (raw : @& RawSignature) (rawIdxVal : Spec.Field.E) (out : ByteArray) :
    Except String ByteArray :=
  if hpk : raw.publicKey.size = 32 then
    if hmsg : raw.message.size = 32 then
      if hsig : raw.signature.size = 2404 then
        let out := pushFieldBytes (pushHdr out hdrRawIndex) rawIdxVal
        let pkRoot := Model.Xmss.readPair64Proof raw.publicKey 0 (by omega)
        let pp := Model.Xmss.readPair64Proof raw.publicKey 16 (by omega)
        let index : Nat :=
          (raw.signature[0]).toNat |||
          ((raw.signature[1]).toNat <<< 8) |||
          ((raw.signature[2]).toNat <<< 16) |||
          ((raw.signature[3]).toNat <<< 24)
        let s0 := index
        let s1 := index >>> 8
        let s2 := index >>> 16
        let s3 := index >>> 24
        let out := pushHdr out hdrLxIndex
        let out := pushFieldBytes out ⟨s0.toUInt64, 0, 0⟩
        let out := pushFieldBytes out ⟨s1.toUInt64, 0, 0⟩
        let out := pushFieldBytes out ⟨s2.toUInt64, 0, 0⟩
        let out := pushFieldBytes out ⟨s3.toUInt64, 0, 0⟩
        let out := pushHdr out hdrLxWindows
        let out := pushFieldBytes out (Model.Xmss.countFast (s0 &&& 255))
        let out := pushFieldBytes out (Model.Xmss.countFast (s1 &&& 255))
        let out := pushFieldBytes out (Model.Xmss.countFast (s2 &&& 255))
        let out := pushFieldBytes out (Model.Xmss.countFast (s3 &&& 255))
        let m0 := Model.Keccak.readWordLEProof raw.message 0 (by omega)
        let m1 := Model.Keccak.readWordLEProof raw.message 8 (by omega)
        let m2 := Model.Keccak.readWordLEProof raw.message 16 (by omega)
        let m3 := Model.Keccak.readWordLEProof raw.message 24 (by omega)
        match signerLayerDirectBytes pp raw.signature hsig index 0 (by omega) out m0 m1 m2 m3 with
        | .error e => .error e
        | .ok (out, r0) =>
          match signerLayerDirectBytes pp raw.signature hsig index 1 (by omega) out r0.lo r0.hi 0 0 with
          | .error e => .error e
          | .ok (out, r1) =>
            if Model.Xmss.u64Eq r1.lo pkRoot.lo && Model.Xmss.u64Eq r1.hi pkRoot.hi then .ok out
            else .error "Lean signature verification failed"
      else .error "invalid XMSS record dimensions"
    else .error "invalid XMSS record dimensions"
  else .error "invalid XMSS record dimensions"

/-- Directly verify and encode workload hints into `hints.bin` wire format without materializing
boxed `HintEntry` objects. -/
def encodeHintsFromSignersDirect (seed : Array Spec.Field.E) (signers : Array RawSignature)
    (bytecodeValue : Spec.Field.E) : Except String ByteArray := do
  let n := signers.size
  let rawIdxTable := Model.Xmss.buildCountArray n
  let wCount := min Model.Xmss.numWorkers (max n 1)
  let tasks := Fin.foldl wCount (fun ts w =>
    let start := (w.val * n) / wCount
    let stop := ((w.val + 1) * n) / wCount
    let len := stop - start
    let t : Task (Except String ByteArray) := Task.spawn fun () =>
      Fin.foldl len (fun (acc : Except String ByteArray) k =>
        match acc with
        | .error e => .error e
        | .ok b =>
          let idx := start + k.val
          if h : idx < signers.size then
            let rv := if hr : idx < rawIdxTable.size then rawIdxTable[idx] else Model.Xmss.countFast idx
            signerDirectBytes signers[idx] rv b
          else .ok b) (.ok (ByteArray.emptyWithCapacity (len * 7457)))
    ts.push t) (Array.emptyWithCapacity wCount : Array (Task (Except String ByteArray)))
  let zeroCount := Model.Xmss.countFast 0
  let nCount := if hn : n < rawIdxTable.size then rawIdxTable[n] else Model.Xmss.countFast n
  let headerEntries : Array HintEntry := Array.emptyWithCapacity (3 + n)
  let headerEntries := headerEntries.push ⟨"meta", #[nCount, zeroCount, nCount, zeroCount, zeroCount, zeroCount, zeroCount, zeroCount]⟩
  let headerEntries := headerEntries.push ⟨"fs_seed", seed⟩
  let headerEntries := if n > 0 then headerEntries.push ⟨"signers_split", Model.Xmss.listSplitFast n⟩ else headerEntries
  let headerEntries := Fin.foldl n (fun acc i =>
    if h : i.val < signers.size then
      let x := signers[i.val]
      if hpk : x.publicKey.size = 32 then
        if hmsg : x.message.size = 32 then
          acc.push ⟨"claims", #[
            Model.Xmss.packCellProof x.publicKey 0 (by omega),
            Model.Xmss.packCellProof x.publicKey 16 (by omega),
            Model.Xmss.packCellProof x.message 0 (by omega),
            Model.Xmss.packCellProof x.message 16 (by omega)]⟩
        else
          acc.push ⟨"claims", #[packCell x.publicKey, packCell x.publicKey 16, packCell x.message, packCell x.message 16]⟩
      else
        acc.push ⟨"claims", #[packCell x.publicKey, packCell x.publicKey 16, packCell x.message, packCell x.message 16]⟩
    else acc) headerEntries
  let headerBytes := encodeHintsSlice headerEntries 0 headerEntries.size
  let footerEntries : Array HintEntry := #[⟨"leaf_defer", #[bytecodeValue]⟩, ⟨"da_pick", #[zeroCount]⟩]
  let footerBytes := encodeHintsSlice footerEntries 0 footerEntries.size
  let chunks ← Fin.foldl tasks.size (fun (acc : Except String (Array ByteArray)) w =>
    match acc with
    | .error e => .error e
    | .ok arr =>
      if h : w.val < tasks.size then
        match tasks[w.val].get with
        | .error e => .error e
        | .ok chunkBytes => .ok (arr.push chunkBytes)
      else .ok arr) (.ok (Array.emptyWithCapacity wCount))
  let total := Fin.foldl chunks.size (fun s w =>
    if h : w.val < chunks.size then s + chunks[w.val].size else s) (headerBytes.size + footerBytes.size)
  let out := ByteArray.emptyWithCapacity total
  let out := ByteArray.copySlice headerBytes 0 out out.size headerBytes.size false
  let out := Fin.foldl chunks.size (fun b w =>
    if h : w.val < chunks.size then
      let c := chunks[w.val]
      ByteArray.copySlice c 0 b b.size c.size false
    else b) out
  let out := ByteArray.copySlice footerBytes 0 out out.size footerBytes.size false
  .ok out

/-- Directly verify and encode `hints.bin` wire bytes from raw inputs. -/
def encodedHintsOfVerified (seed : ByteArray) (raw : Array RawSignature)
    (bytecodeValue : Spec.Field.E) : Except String ByteArray := do
  let signers := Model.Xmss.sortedUniqueFast raw
  let out ← encodeHintsFromSignersDirect #[packCell seed, packCell seed 16] signers bytecodeValue
  if signers.size == raw.size then
    .ok out
  else
    let allOk := Fin.foldl raw.size (fun ok i =>
      if !ok then false
      else if h : i.val < raw.size then Model.Xmss.verifySignatureFast raw[i.val]
      else true) true
    if allOk then .ok out else .error "Lean signature verification failed"

/-- Directly verify, encode, and stream-hash workload hints into `(hintEntryCount, hintsKeccak256)`
without materializing boxed `HintEntry` arrays. -/
def hashWorkloadHintsFromSignersDirect (seed : Array Spec.Field.E) (signers : Array RawSignature)
    (bytecodeValue : Spec.Field.E) : Except String (Nat × ByteArray) := do
  let n := signers.size
  let rawIdxTable := Model.Xmss.buildCountArray n
  let wCount := min Model.Xmss.numWorkers (max n 1)
  let tasks := Fin.foldl wCount (fun ts w =>
    let start := (w.val * n) / wCount
    let stop := ((w.val + 1) * n) / wCount
    let len := stop - start
    let t : Task (Except String ByteArray) := Task.spawn fun () =>
      Fin.foldl len (fun (acc : Except String ByteArray) k =>
        match acc with
        | .error e => .error e
        | .ok b =>
          let idx := start + k.val
          if h : idx < signers.size then
            let rv := if hr : idx < rawIdxTable.size then rawIdxTable[idx] else Model.Xmss.countFast idx
            signerDirectBytes signers[idx] rv b
          else .ok b) (.ok (ByteArray.emptyWithCapacity (len * 7457)))
    ts.push t) (Array.emptyWithCapacity wCount : Array (Task (Except String ByteArray)))
  let zeroCount := Model.Xmss.countFast 0
  let nCount := if hn : n < rawIdxTable.size then rawIdxTable[n] else Model.Xmss.countFast n
  let headerEntries : Array HintEntry := Array.emptyWithCapacity (3 + n)
  let headerEntries := headerEntries.push ⟨"meta", #[nCount, zeroCount, nCount, zeroCount, zeroCount, zeroCount, zeroCount, zeroCount]⟩
  let headerEntries := headerEntries.push ⟨"fs_seed", seed⟩
  let headerEntries := if n > 0 then headerEntries.push ⟨"signers_split", Model.Xmss.listSplitFast n⟩ else headerEntries
  let headerEntries := Fin.foldl n (fun acc i =>
    if h : i.val < signers.size then
      let x := signers[i.val]
      if hpk : x.publicKey.size = 32 then
        if hmsg : x.message.size = 32 then
          acc.push ⟨"claims", #[
            Model.Xmss.packCellProof x.publicKey 0 (by omega),
            Model.Xmss.packCellProof x.publicKey 16 (by omega),
            Model.Xmss.packCellProof x.message 0 (by omega),
            Model.Xmss.packCellProof x.message 16 (by omega)]⟩
        else
          acc.push ⟨"claims", #[packCell x.publicKey, packCell x.publicKey 16, packCell x.message, packCell x.message 16]⟩
      else
        acc.push ⟨"claims", #[packCell x.publicKey, packCell x.publicKey 16, packCell x.message, packCell x.message 16]⟩
    else acc) headerEntries
  let headerBytes := encodeHintsSlice headerEntries 0 headerEntries.size
  let (st0, carry0) := Model.Keccak.absorbChunkCPS Model.Keccak.zeroState25Fast ByteArray.empty headerBytes
  let (st1, carry1) ← Fin.foldl tasks.size (fun (acc : Except String (Model.Keccak.State25 × ByteArray)) w =>
    match acc with
    | .error e => .error e
    | .ok (s, rem) =>
      if h : w.val < tasks.size then
        match tasks[w.val].get with
        | .error e => .error e
        | .ok chunkBytes => .ok (Model.Keccak.absorbChunkCPS s rem chunkBytes)
      else .ok (s, rem)) (.ok (st0, carry0))
  let footerEntries : Array HintEntry := #[⟨"leaf_defer", #[bytecodeValue]⟩, ⟨"da_pick", #[zeroCount]⟩]
  let footerBytes := encodeHintsSlice footerEntries 0 footerEntries.size
  let (st2, carry2) := Model.Keccak.absorbChunkCPS st1 carry1 footerBytes
  let digest := Model.Keccak.finalizeKeccak256CPS st2 carry2 0 carry2.size
  let totalEntries := headerEntries.size + n * 155 + 2
  .ok (totalEntries, digest)

/-- The `hints.bin` wire encoding of a hint list. -/
def encodeHints (hints : Array HintEntry) : ByteArray :=
  let n := hints.size
  if n <= 512 then
    encodeHintsSlice hints 0 n
  else
    let wCount := 16
    let tasks := Fin.foldl wCount (fun ts w =>
      let start := (w.val * n) / wCount
      let stop := ((w.val + 1) * n) / wCount
      let len := stop - start
      let t : Task ByteArray := Task.spawn fun () => encodeHintsSlice hints start len
      ts.push t) (Array.emptyWithCapacity wCount : Array (Task ByteArray))
    let chunks := Fin.foldl tasks.size (fun acc w =>
      if h : w.val < tasks.size then acc.push tasks[w.val].get else acc)
      (Array.emptyWithCapacity wCount : Array ByteArray)
    let total := Fin.foldl chunks.size (fun s w =>
      if h : w.val < chunks.size then s + chunks[w.val].size else s) 0
    Fin.foldl chunks.size (fun out w =>
      if h : w.val < chunks.size then
        let c := chunks[w.val]
        ByteArray.copySlice c 0 out out.size c.size false
      else out) (ByteArray.emptyWithCapacity total)

/-- Group hint entries into the named witness streams the VM pops entries from. -/
def streamsOfHints (hints : Array HintEntry) : Array Stream :=
  Fin.foldl hints.size (fun streams idx =>
    if h : idx.val < hints.size then
      let hint := hints[idx.val]
      match streams.findIdx? (fun s => s.name == hint.name) with
      | some i => streams.modify i fun s => {s with entries := s.entries.push hint.values}
      | none => streams.push ⟨hint.name, #[hint.values], 0⟩
    else streams) (Array.emptyWithCapacity 16)

def hex (bytes : ByteArray) : String := String.ofList (bytes.data.toList.flatMap fun b =>
  let digits := #[ '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f' ]
  [digits[b.toNat/16]!, digits[b.toNat%16]!])

end LeanVmXmss.Model.Cli
