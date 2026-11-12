import Spec.Xmss.Hints
import Model.Layout.Scalar
import Model.Vm.Kernel
import Model.Keccak.Registers

namespace LeanVmXmss.Model.Xmss

open Spec.Xmss
open Spec.Field (E)
open Model.Keccak (Pair64 State25 zeroState25CPS permuteAbsorb25 keccak1Block16 keccak256CPS
  readWordLEProof readWordLEFast pushU64LE)

def signatureHints := Spec.Xmss.signatureHints

def hintGpowTable : Array UInt64 := Model.Layout.gpowTable 2048

def hintCount (t : Array UInt64) (n : Nat) : E := ⟨t[n]?.getD (Spec.Xmss.gpow n), 0, 0⟩

def hashFast (b : ByteArray) : ByteArray :=
  keccak256CPS b

def tweakFast (pp : ByteArray) (k l f i s : Nat) (p : ByteArray) : ByteArray :=
  (hashFast (pp ++ address k l f i s ++ p)).extract 0 16

def chainFast (pp : ByteArray) (l i j st : Nat) (v : ByteArray) : ByteArray :=
  (List.range (3 - st)).foldl (fun c k => tweakFast pp 1 l 0 i (st + k) (c ++ writeLE j.toUInt64 16)) v

def signatureHintsFast (t : Array UInt64) (raw : RawSignature) :
    Except String (Array HintEntry × ByteArray) := do
  if raw.publicKey.size != 32 || raw.message.size != 32 || raw.signature.size != 2404 then
    throw "invalid XMSS record dimensions"
  let pp := raw.publicKey.extract 16 32
  let idx := (readLE raw.signature 0 4).toNat
  let sh := (Array.range 4).map fun i => idx >>> (i * window)
  let mut hints : Array HintEntry := #[⟨"lx_index", sh.map fun x => ⟨x.toUInt64, 0, 0⟩⟩,
    ⟨"lx_windows", sh.map fun x => hintCount t (x % 256)⟩]
  let mut root := raw.message
  for layer in [:2] do
    let o := 4 + layer * 1200
    let e := idx >>> (layer * 16)
    let rnd := raw.signature.extract o (o + 16)
    let some digits := codeword (tweakFast pp 12 layer 0 e 0 (root ++ rnd)) | throw "invalid WOTS+C codeword"
    let starts := (Array.range 58).map fun i => raw.signature.extract (o + 16 + i * 16) (o + 32 + i * 16)
    root := tweakFast pp 2 layer 0 e 0 ((starts.mapIdx fun i v => chainFast pp layer e i digits[i]! v).foldl (· ++ ·) ByteArray.empty)
    for level in [:16] do
      let sib := raw.signature.extract (o + 944 + level * 16) (o + 960 + level * 16)
      hints := hints.push ⟨"lx_path", #[packCell sib]⟩
      root := tweakFast pp 3 layer (level + 1) (e >>> (level + 1)) 0
        (if (e >>> level) &&& 1 == 0 then root ++ sib else sib ++ root)
    hints := hints.push ⟨"randomizer", #[packCell rnd]⟩
    hints := hints.push ⟨"lx_digits", (Array.range 15).map fun g =>
      hintCount t ((List.range (min 4 (58 - g * 4))).foldl (fun n j => n + digits[g * 4 + j]! * 4 ^ j) 0)⟩
    for v in starts do hints := hints.push ⟨"chain_starts", #[packCell v]⟩
  return (hints, root)

@[inline] def gpowFast (n : Nat) : UInt64 :=
  Fin.foldl n (fun x _ => Model.Vm.scalarGeneratorStep x) (1 : UInt64)

@[inline] def countFastGen (n : Nat) : E := ⟨gpowFast n, 0, 0⟩

def gpow256Table : Array E :=
  Fin.foldl 256 (fun acc i => acc.push (countFastGen i.val)) (Array.emptyWithCapacity 256)

@[inline] def countFast (n : Nat) : E :=
  if h : n < gpow256Table.size then gpow256Table[n] else countFastGen n

@[inline] def listSplitFast (n : Nat) : Array E :=
  #[countFast (n / (claimGroup * bigGroups)),
    countFast (n % (claimGroup * bigGroups) / claimGroup),
    countFast (n % claimGroup)]

@[inline] def addressLo (kind layer field index step : Nat) : UInt64 :=
  (index.toUInt64 &&& (0xffffffff : UInt64)) |||
  (((field ||| (layer <<< 23)).toUInt64 &&& (0xffffff : UInt64)) <<< 32) |||
  (((kind ||| (step <<< 5)).toUInt64 &&& (0xff : UInt64)) <<< 56)

@[inline] def packPair64 (p : Pair64) : E := ⟨p.lo, p.hi, 0⟩

@[inline] def readPair64Proof (b : @& ByteArray) (offset : Nat) (_ : offset + 15 < b.size) : Pair64 :=
  ⟨readWordLEProof b offset (by omega), readWordLEProof b (offset + 8) (by omega)⟩

@[inline] def packCellProof (b : @& ByteArray) (offset : Nat) (_ : offset + 15 < b.size) : E :=
  ⟨readWordLEProof b offset (by omega), readWordLEProof b (offset + 8) (by omega), 0⟩

@[inline] def u64Eq (a b : UInt64) : Bool := decide (a = b)
@[inline] def u64Ne (a b : UInt64) : Bool := !decide (a = b)

def codeword58 (d : Pair64) : Option (Array Nat) :=
  let sumAndOk := Fin.foldl 58 (fun acc i =>
    let bitPos := (i.val * 2).toUInt64
    let word := if i.val < 32 then d.lo else d.hi
    let shift := if i.val < 32 then bitPos else bitPos - 64
    let digit := ((word >>> shift) &&& 3).toNat
    (acc.1.push digit, acc.2 + digit)) (Array.emptyWithCapacity 58, 0)
  let tailHigh := d.hi >>> 52
  if u64Ne tailHigh 0 || sumAndOk.2 != 106 then
    none
  else
    some sumAndOk.1

@[inline] def chainFastPair (pp : Pair64) (layer index i start : Nat) (val : Pair64) : Pair64 :=
  let steps := 3 - start
  let iLo := i.toUInt64
  Fin.foldl steps (fun cur k =>
    let addr0 := addressLo 1 layer 0 index (start + k.val)
    keccak1Block16 pp.lo pp.hi addr0 0 cur.lo cur.hi iLo 0 0x01) val

def hashLeafEnds (pp : Pair64) (layer e : Nat) (ends : @& Array Pair64) : Pair64 :=
  if hends : ends.size = 58 then
    let addr0 := addressLo 2 layer 0 e 0
    let s := zeroState25CPS
    let p0 := ends[0]
    let p1 := ends[1]
    let p2 := ends[2]
    let p3 := ends[3]
    let p4 := ends[4]
    let p5 := ends[5]
    let p6 := ends[6]
    let s := permuteAbsorb25 s pp.lo pp.hi addr0 0
      p0.lo p0.hi p1.lo p1.hi p2.lo p2.hi p3.lo p3.hi p4.lo p4.hi p5.lo p5.hi p6.lo
    let p7 := ends[7]
    let p8 := ends[8]
    let p9 := ends[9]
    let p10 := ends[10]
    let p11 := ends[11]
    let p12 := ends[12]
    let p13 := ends[13]
    let p14 := ends[14]
    let s := permuteAbsorb25 s p6.hi p7.lo p7.hi p8.lo p8.hi p9.lo p9.hi p10.lo p10.hi
      p11.lo p11.hi p12.lo p12.hi p13.lo p13.hi p14.lo p14.hi
    let p15 := ends[15]
    let p16 := ends[16]
    let p17 := ends[17]
    let p18 := ends[18]
    let p19 := ends[19]
    let p20 := ends[20]
    let p21 := ends[21]
    let p22 := ends[22]
    let p23 := ends[23]
    let s := permuteAbsorb25 s p15.lo p15.hi p16.lo p16.hi p17.lo p17.hi p18.lo p18.hi
      p19.lo p19.hi p20.lo p20.hi p21.lo p21.hi p22.lo p22.hi p23.lo
    let p24 := ends[24]
    let p25 := ends[25]
    let p26 := ends[26]
    let p27 := ends[27]
    let p28 := ends[28]
    let p29 := ends[29]
    let p30 := ends[30]
    let p31 := ends[31]
    let s := permuteAbsorb25 s p23.hi p24.lo p24.hi p25.lo p25.hi p26.lo p26.hi p27.lo p27.hi
      p28.lo p28.hi p29.lo p29.hi p30.lo p30.hi p31.lo p31.hi
    let p32 := ends[32]
    let p33 := ends[33]
    let p34 := ends[34]
    let p35 := ends[35]
    let p36 := ends[36]
    let p37 := ends[37]
    let p38 := ends[38]
    let p39 := ends[39]
    let p40 := ends[40]
    let s := permuteAbsorb25 s p32.lo p32.hi p33.lo p33.hi p34.lo p34.hi p35.lo p35.hi
      p36.lo p36.hi p37.lo p37.hi p38.lo p38.hi p39.lo p39.hi p40.lo
    let p41 := ends[41]
    let p42 := ends[42]
    let p43 := ends[43]
    let p44 := ends[44]
    let p45 := ends[45]
    let p46 := ends[46]
    let p47 := ends[47]
    let p48 := ends[48]
    let s := permuteAbsorb25 s p40.hi p41.lo p41.hi p42.lo p42.hi p43.lo p43.hi p44.lo p44.hi
      p45.lo p45.hi p46.lo p46.hi p47.lo p47.hi p48.lo p48.hi
    let p49 := ends[49]
    let p50 := ends[50]
    let p51 := ends[51]
    let p52 := ends[52]
    let p53 := ends[53]
    let p54 := ends[54]
    let p55 := ends[55]
    let p56 := ends[56]
    let p57 := ends[57]
    let s := permuteAbsorb25 s p49.lo p49.hi p50.lo p50.hi p51.lo p51.hi p52.lo p52.hi
      p53.lo p53.hi p54.lo p54.hi p55.lo p55.hi p56.lo p56.hi p57.lo
    let sFinal := permuteAbsorb25 s p57.hi 0x01 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0x8000000000000000
    ⟨sFinal.a00, sFinal.a01⟩
  else ⟨0, 0⟩

def signatureLayerStep (pp : Pair64) (sig : @& ByteArray) (hsig : sig.size = 2404)
    (index layer : Nat) (hlayer : layer < 2)
    (hints : Array HintEntry) (rootLo rootHi root2 root3 : UInt64) :
    Except String (Array HintEntry × Pair64) :=
  let offset := 4 + layer * 1200
  let e := index >>> (layer * 16)
  let rand := readPair64Proof sig offset (by omega)
  let addrMsg := addressLo 12 layer 0 e 0
  let digest : Pair64 :=
    if layer == 0 then
      let s0 := permuteAbsorb25 zeroState25CPS pp.lo pp.hi addrMsg 0
        rootLo rootHi root2 root3 rand.lo rand.hi 0x01 0 0 0 0 0 0x8000000000000000
      ⟨s0.a00, s0.a01⟩
    else
      keccak1Block16 pp.lo pp.hi addrMsg 0 rootLo rootHi rand.lo rand.hi 0x01
  match codeword58 digest with
  | none => .error "invalid WOTS+C codeword"
  | some digits =>
    let ends := Fin.foldl 58 (fun acc i =>
      let stOff := offset + 16 + i.val * 16
      let startVal := readPair64Proof sig stOff (by omega)
      let dig := digits[i.val]?.getD 0
      acc.push (chainFastPair pp layer e i.val dig startVal)) (Array.emptyWithCapacity 58)
    let leafRoot := hashLeafEnds pp layer e ends
    let (hintsAfterPath, climbedRoot) := Fin.foldl 16 (fun st lv =>
      let level := lv.val
      let sibOff := offset + 944 + level * 16
      let sib := readPair64Proof sig sibOff (by omega)
      let h1 := st.1.push ⟨"lx_path", #[packPair64 sib]⟩
      let cur := st.2
      let addrTree := addressLo 3 layer (level + 1) (e >>> (level + 1)) 0
      let nextRoot :=
        if ((e >>> level) &&& 1) == 0 then
          keccak1Block16 pp.lo pp.hi addrTree 0 cur.lo cur.hi sib.lo sib.hi 0x01
        else
          keccak1Block16 pp.lo pp.hi addrTree 0 sib.lo sib.hi cur.lo cur.hi 0x01
      (h1, nextRoot)) (hints, leafRoot)
    let hints := hintsAfterPath.push ⟨"randomizer", #[packPair64 rand]⟩
    let lxDigits := Fin.foldl 15 (fun acc g =>
      let grp := g.val
      let cnt := min 4 (58 - grp * 4)
      let val := Fin.foldl cnt (fun n j =>
        let d := digits[grp * 4 + j.val]?.getD 0
        n + d * (1 <<< (2 * j.val))) 0
      acc.push (countFast val)) (Array.emptyWithCapacity 15)
    let hints := hints.push ⟨"lx_digits", lxDigits⟩
    let hints := Fin.foldl 58 (fun acc i =>
      let stOff := offset + 16 + i.val * 16
      let startCell := packCellProof sig stOff (by omega)
      acc.push ⟨"chain_starts", #[startCell]⟩) hints
    .ok (hints, climbedRoot)

def signatureHintsInto (raw : @& RawSignature) (hints : Array HintEntry) :
    Except String (Array HintEntry × Pair64 × Pair64) :=
  if hpk : raw.publicKey.size = 32 then
    if hmsg : raw.message.size = 32 then
      if hsig : raw.signature.size = 2404 then
        let pkRoot := readPair64Proof raw.publicKey 0 (by omega)
        let pp := readPair64Proof raw.publicKey 16 (by omega)
        let index : Nat :=
          (raw.signature[0]).toNat |||
          ((raw.signature[1]).toNat <<< 8) |||
          ((raw.signature[2]).toNat <<< 16) |||
          ((raw.signature[3]).toNat <<< 24)
        let s0 := index
        let s1 := index >>> 8
        let s2 := index >>> 16
        let s3 := index >>> 24
        let initHints : Array HintEntry :=
          hints
            |>.push ⟨"lx_index", #[⟨s0.toUInt64, 0, 0⟩, ⟨s1.toUInt64, 0, 0⟩, ⟨s2.toUInt64, 0, 0⟩, ⟨s3.toUInt64, 0, 0⟩]⟩
            |>.push ⟨"lx_windows", #[countFast (s0 &&& 255), countFast (s1 &&& 255), countFast (s2 &&& 255), countFast (s3 &&& 255)]⟩
        let m0 := readWordLEProof raw.message 0 (by omega)
        let m1 := readWordLEProof raw.message 8 (by omega)
        let m2 := readWordLEProof raw.message 16 (by omega)
        let m3 := readWordLEProof raw.message 24 (by omega)
        match signatureLayerStep pp raw.signature hsig index 0 (by omega) initHints m0 m1 m2 m3 with
        | .error e => .error e
        | .ok (hLayer0, r0) =>
          match signatureLayerStep pp raw.signature hsig index 1 (by omega) hLayer0 r0.lo r0.hi 0 0 with
          | .error e => .error e
          | .ok (hLayer1, r1) => .ok (hLayer1, r1, pkRoot)
      else .error "invalid XMSS record dimensions"
    else .error "invalid XMSS record dimensions"
  else .error "invalid XMSS record dimensions"

def signatureHintsPairFast (raw : @& RawSignature) : Except String (Array HintEntry × Pair64 × Pair64) :=
  signatureHintsInto raw (Array.emptyWithCapacity 154)

def verifySignatureFast (raw : @& RawSignature) : Bool :=
  match signatureHintsPairFast raw with
  | .error _ => false
  | .ok (_, root, pkRoot) => u64Eq root.lo pkRoot.lo && u64Eq root.hi pkRoot.hi

@[inline] def byteCmpLT (a b : @& ByteArray) (len : Nat) : Bool :=
  let res := Fin.foldl len (fun (st : Nat) i =>
    if st != 0 then st
    else
      let x := a[i.val]?.getD 0
      let y := b[i.val]?.getD 0
      if x < y then 1 else if x > y then 2 else 0) 0
  res == 1

@[inline] def claimLT (a b : @& RawSignature) : Bool :=
  if a.publicKey.size == 32 && b.publicKey.size == 32 && a.message.size == 32 && b.message.size == 32 then
    let pkCmp := Fin.foldl 32 (fun (st : Nat) i =>
      if st != 0 then st
      else
        let x := a.publicKey[i.val]?.getD 0
        let y := b.publicKey[i.val]?.getD 0
        if x < y then 1 else if x > y then 2 else 0) 0
    if pkCmp == 1 then true
    else if pkCmp == 2 then false
    else byteCmpLT a.message b.message 32
  else
    Spec.Xmss.bytesLT (Spec.Xmss.claimBytes a) (Spec.Xmss.claimBytes b)

@[inline] def claimEqFast (a b : @& RawSignature) : Bool :=
  a.publicKey == b.publicKey && a.message == b.message

def sortedUniqueFast (raw : Array RawSignature) : Array RawSignature :=
  let sorted := raw.qsort claimLT
  Fin.foldl sorted.size (fun out i =>
    if h : i.val < sorted.size then
      let x := sorted[i.val]
      if hne : out.size > 0 then
        let prev := out[out.size - 1]
        if claimEqFast prev x then out else out.push x
      else out.push x
    else out) (Array.emptyWithCapacity sorted.size)

def numWorkers : Nat := 16

def buildCountArray (n : Nat) : Array E :=
  let arr := Array.emptyWithCapacity n
  if n == 0 then arr
  else
    let arr := arr.push ⟨1, 0, 0⟩
    let (_, arr) := Fin.foldl (n - 1) (fun (cur, a) _ =>
      let nxt := Model.Vm.scalarGeneratorStep cur
      (nxt, a.push ⟨nxt, 0, 0⟩)) ((1 : UInt64), arr)
    arr

def parallelSignerHints (signers : Array RawSignature) (rawIdxTable : Array E) (checkRoot : Bool) :
    Except String (Array (Array HintEntry)) :=
  let n := signers.size
  if n == 0 then .ok #[]
  else if n <= 2 then
    Fin.foldl n (fun acc i =>
      match acc with
      | .error e => .error e
      | .ok arr =>
        if h : i.val < signers.size then
          let rawIdxVal := if hr : i.val < rawIdxTable.size then rawIdxTable[i.val] else countFast i.val
          let initH := (Array.emptyWithCapacity 155).push ⟨"raw_index", #[rawIdxVal]⟩
          match signatureHintsInto signers[i.val] initH with
          | .error e => .error e
          | .ok (sub, root, pkRoot) =>
            if checkRoot && (u64Ne root.lo pkRoot.lo || u64Ne root.hi pkRoot.hi) then
              .error "Lean signature verification failed"
            else
              .ok (arr.push sub)
        else .ok arr) (.ok (Array.emptyWithCapacity 1))
  else
    let wCount := min numWorkers n
    let tasks := Fin.foldl wCount (fun ts w =>
      let start := (w.val * n) / wCount
      let stop := ((w.val + 1) * n) / wCount
      let len := stop - start
      let t : Task (Except String (Array HintEntry)) := Task.spawn fun () =>
        Fin.foldl len (fun (acc : Except String (Array HintEntry)) k =>
          match acc with
          | .error e => .error e
          | .ok chunk =>
            let idx := start + k.val
            if h : idx < signers.size then
              let rawIdxVal := if hr : idx < rawIdxTable.size then rawIdxTable[idx] else countFast idx
              let chunk := chunk.push ⟨"raw_index", #[rawIdxVal]⟩
              match signatureHintsInto signers[idx] chunk with
              | .error e => .error e
              | .ok (chunk', root, pkRoot) =>
                if checkRoot && (u64Ne root.lo pkRoot.lo || u64Ne root.hi pkRoot.hi) then
                  .error "Lean signature verification failed"
                else
                  .ok chunk'
            else .ok chunk) (.ok (Array.emptyWithCapacity (len * 155)))
      ts.push t) (Array.emptyWithCapacity wCount : Array (Task (Except String (Array HintEntry))))
    Fin.foldl tasks.size (fun (acc : Except String (Array (Array HintEntry))) w =>
      match acc with
      | .error e => .error e
      | .ok out =>
        if h : w.val < tasks.size then
          match tasks[w.val].get with
          | .error e => .error e
          | .ok chunk => .ok (out.push chunk)
        else .ok out) (.ok (Array.emptyWithCapacity wCount))

def buildWorkloadHintsFromSigners (seed : Array E) (signers : Array RawSignature)
    (bytecodeValue : E) (checkRoot : Bool) : Except String (Array HintEntry) := do
  let n := signers.size
  let rawIdxTable := buildCountArray n
  let chunks ← parallelSignerHints signers rawIdxTable checkRoot
  let totalCap := 5 + n + n * 155
  let hints := Array.emptyWithCapacity totalCap
  let zeroCount := countFast 0
  let nCount := if hn : n < rawIdxTable.size then rawIdxTable[n] else countFast n
  let hints := hints.push ⟨"meta", #[nCount, zeroCount, nCount, zeroCount, zeroCount, zeroCount, zeroCount, zeroCount]⟩
  let hints := hints.push ⟨"fs_seed", seed⟩
  let hints := if n > 0 then hints.push ⟨"signers_split", listSplitFast n⟩ else hints
  let hints := Fin.foldl n (fun acc i =>
    if h : i.val < signers.size then
      let x := signers[i.val]
      if hpk : x.publicKey.size = 32 then
        if hmsg : x.message.size = 32 then
          acc.push ⟨"claims", #[
            packCellProof x.publicKey 0 (by omega),
            packCellProof x.publicKey 16 (by omega),
            packCellProof x.message 0 (by omega),
            packCellProof x.message 16 (by omega)]⟩
        else
          acc.push ⟨"claims", #[packCell x.publicKey, packCell x.publicKey 16, packCell x.message, packCell x.message 16]⟩
      else
        acc.push ⟨"claims", #[packCell x.publicKey, packCell x.publicKey 16, packCell x.message, packCell x.message 16]⟩
    else acc) hints
  let hints := Fin.foldl chunks.size (fun acc w =>
    if hw : w.val < chunks.size then
      acc.append chunks[w.val]
    else acc) hints
  let hints := hints.push ⟨"leaf_defer", #[bytecodeValue]⟩
  let hints := hints.push ⟨"da_pick", #[zeroCount]⟩
  .ok hints

def workloadHints (seed : Array E) (raw : Array RawSignature) (bytecodeValue : E) :
    Except String (Array HintEntry) :=
  buildWorkloadHintsFromSigners seed (sortedUniqueFast raw) bytecodeValue false

def workloadHintsVerified (seed : Array E) (raw : Array RawSignature) (bytecodeValue : E) :
    Except String (Array HintEntry) :=
  let signers := sortedUniqueFast raw
  match buildWorkloadHintsFromSigners seed signers bytecodeValue true with
  | .error e => .error e
  | .ok hints =>
    if signers.size == raw.size then
      .ok hints
    else
      let allOk := Fin.foldl raw.size (fun ok i =>
        if !ok then false
        else if h : i.val < raw.size then verifySignatureFast raw[i.val]
        else true) true
      if allOk then .ok hints else .error "Lean signature verification failed"

def workloadHintsParallel (seed : Array E) (raw : Array RawSignature) (bv : E) : IO (Array HintEntry) := do
  match workloadHints seed raw bv with
  | .ok h => pure h
  | .error e => throw (IO.userError e)

def emptyKeccak256 : ByteArray := keccak256CPS ByteArray.empty

def claimListDigestFast (signers : @& Array RawSignature) : ByteArray :=
  let total := signers.size * 64
  let buf := Fin.foldl signers.size (fun b i =>
    if h : i.val < signers.size then
      let x := signers[i.val]
      let b := ByteArray.copySlice x.publicKey 0 b b.size x.publicKey.size false
      ByteArray.copySlice x.message 0 b b.size x.message.size false
    else b) (ByteArray.emptyWithCapacity total)
  keccak256CPS buf

def statementDigest (seed : ByteArray) (raw : Array RawSignature) (bytecodeValue : E)
    (bytecodeVars : Nat := 23) : ByteArray :=
  let claimsHash := claimListDigestFast raw
  let emptyHash := emptyKeccak256
  let nCells := bytecodeVars + 1 + (if (bytecodeVars + 1) % 2 == 1 then 1 else 0)
  let cap := seed.size + 96 + nCells * 24
  let buf := ByteArray.emptyWithCapacity cap
  let buf := ByteArray.copySlice seed 0 buf buf.size seed.size false
  let buf := ByteArray.copySlice claimsHash 0 buf buf.size claimsHash.size false
  let buf := ByteArray.copySlice emptyHash 0 buf buf.size emptyHash.size false
  let buf := Fin.foldl 32 (fun acc _ => acc.push 0) buf
  let buf := Fin.foldl (bytecodeVars * 24) (fun acc _ => acc.push 0) buf
  let buf := pushU64LE (pushU64LE (pushU64LE buf bytecodeValue.c0) bytecodeValue.c1) bytecodeValue.c2
  let buf := if (bytecodeVars + 1) % 2 == 1 then
    Fin.foldl 24 (fun acc _ => acc.push 0) buf
  else buf
  keccak256CPS buf

end LeanVmXmss.Model.Xmss
