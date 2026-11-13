import Model.KeccakGkr.Scalar

namespace LeanVmXmss.Model.KeccakGkr

open Spec.Field (K E zero one embed)
open Spec.Layout
open Spec.Bus (SlotClaim OutputClaim)
open Spec.KeccakGkr (packBits packSize embedBits productBits bitCount localBits laneBits wordBits
  rmfeEmbed rmfeProject keccakPi along embedUnit onesMask
  GkrClaim Opening WordOpening Openings RingSwitchClaim
  segments segLog stepsLog packVars slotBits layerRound)
open Model.Field (eadd nativeKaratsuba nativeEinv)
open Model.Bus (ProverState addScalar addScalars sampleChallenge sampleVec nativeMulBase)
open Model.Pcs.Ntt (foldRange foldRangeLoop)

@[inline] def pushWordLE (bytes : ByteArray) (w : UInt64) : ByteArray :=
  bytes.push w.toUInt8
    |>.push (w >>> 8).toUInt8
    |>.push (w >>> 16).toUInt8
    |>.push (w >>> 24).toUInt8
    |>.push (w >>> 32).toUInt8
    |>.push (w >>> 40).toUInt8
    |>.push (w >>> 48).toUInt8
    |>.push (w >>> 56).toUInt8

@[noinline] def readWordLEReference (bytes : ByteArray) (index : Nat) : UInt64 :=
  let off := 8 * index
  if h : off + 7 < bytes.size then
    (bytes[off]'(by omega)).toUInt64 |||
      ((bytes[off + 1]'(by omega)).toUInt64 <<< 8) |||
      ((bytes[off + 2]'(by omega)).toUInt64 <<< 16) |||
      ((bytes[off + 3]'(by omega)).toUInt64 <<< 24) |||
      ((bytes[off + 4]'(by omega)).toUInt64 <<< 32) |||
      ((bytes[off + 5]'(by omega)).toUInt64 <<< 40) |||
      ((bytes[off + 6]'(by omega)).toUInt64 <<< 48) |||
      ((bytes[off + 7]'(by omega)).toUInt64 <<< 56)
  else 0


theorem wordOffsetNatEq (off k : Nat) (h : off + k < USize.size) :
    (USize.ofNat off + USize.ofNat k).toNat = off + k := by
  have ho : off < USize.size := by omega
  have hk : k < USize.size := by omega
  rw [USize.toNat_add, USize.toNat_ofNat', USize.toNat_ofNat']
  rw [Nat.mod_eq_of_lt ho, Nat.mod_eq_of_lt hk]
  exact Nat.mod_eq_of_lt h


@[inline] def readWordLE (bytes : ByteArray) (index : Nat) : UInt64 :=
  let off := 8 * index
  if hb : off + 7 < bytes.size then
    if hs : bytes.size < USize.size then
      let base := USize.ofNat off
      let getByte := fun (k : Nat) (hk : k ≤ 7) =>
        (bytes.uget (base + USize.ofNat k) (by
          dsimp only [base]
          rw [wordOffsetNatEq off k (by omega)]
          omega)).toUInt64
      getByte 0 (by decide) ||| (getByte 1 (by decide) <<< 8) |||
        (getByte 2 (by decide) <<< 16) ||| (getByte 3 (by decide) <<< 24) |||
        (getByte 4 (by decide) <<< 32) ||| (getByte 5 (by decide) <<< 40) |||
        (getByte 6 (by decide) <<< 48) ||| (getByte 7 (by decide) <<< 56)
    else readWordLEReference bytes index
  else 0


@[inline] def writeWordLE (bytes : ByteArray) (index : Nat) (w : UInt64) : ByteArray :=
  let off := 8 * index
  bytes.set! off w.toUInt8
    |>.set! (off + 1) (w >>> 8).toUInt8
    |>.set! (off + 2) (w >>> 16).toUInt8
    |>.set! (off + 3) (w >>> 24).toUInt8
    |>.set! (off + 4) (w >>> 32).toUInt8
    |>.set! (off + 5) (w >>> 40).toUInt8
    |>.set! (off + 6) (w >>> 48).toUInt8
    |>.set! (off + 7) (w >>> 56).toUInt8

def allocWords (n : Nat) : ByteArray :=
  foldRange n (fun b _ => pushWordLE b 0) (ByteArray.emptyWithCapacity (8 * n))

def zeroWords (bytes : ByteArray) (n : Nat) : ByteArray :=
  foldRange n (fun b i => writeWordLE b i 0) bytes

structure PlanarE where
  c0 : ByteArray
  c1 : ByteArray
  c2 : ByteArray
  deriving Inhabited

def planarEEmpty (n : Nat) : PlanarE :=
  ⟨ByteArray.emptyWithCapacity (8 * n), ByteArray.emptyWithCapacity (8 * n),
   ByteArray.emptyWithCapacity (8 * n)⟩

def planarEAlloc (n : Nat) : PlanarE :=
  ⟨allocWords n, allocWords n, allocWords n⟩

def planarEZero (p : PlanarE) (n : Nat) : PlanarE :=
  ⟨zeroWords p.c0 n, zeroWords p.c1 n, zeroWords p.c2 n⟩

@[inline] def planarEPush (p : PlanarE) (x : E) : PlanarE :=
  ⟨pushWordLE p.c0 x.c0, pushWordLE p.c1 x.c1, pushWordLE p.c2 x.c2⟩

@[inline] def planarEGet (p : PlanarE) (i : Nat) : E :=
  ⟨readWordLE p.c0 i, readWordLE p.c1 i, readWordLE p.c2 i⟩

@[inline] def planarESet (p : PlanarE) (i : Nat) (x : E) : PlanarE :=
  ⟨writeWordLE p.c0 i x.c0, writeWordLE p.c1 i x.c1, writeWordLE p.c2 i x.c2⟩

def encodePlanarE (xs : Array E) : PlanarE :=
  foldRange xs.size (fun acc i => planarEPush acc (xs[i]?.getD zero)) (planarEEmpty xs.size)

def decodePlanarE (p : PlanarE) : Array E :=
  let n := p.c0.size / 8
  foldRange n (fun acc i => acc.push (planarEGet p i)) (Array.emptyWithCapacity n)

@[inline] def selectBit (a b i : UInt64) : UInt64 :=
  a &&& (0 - ((b >>> i) &&& 1))

@[inline] def maskedAddE (acc w : E) (poly : UInt64) (bit : UInt64) : E :=
  let mask := 0 - ((poly >>> bit) &&& 1)
  ⟨acc.c0 ^^^ (w.c0 &&& mask), acc.c1 ^^^ (w.c1 &&& mask), acc.c2 ^^^ (w.c2 &&& mask)⟩

/-- Keep the owned accumulator live across planar buffer reads. The small
non-inlined boundary lets the compiler reuse it instead of allocating per bit. -/
@[noinline] def accumulateProductLimbs (w0 w1 w2 mask : UInt64) (acc : E) : E :=
  ⟨acc.c0 ^^^ (w0 &&& mask), acc.c1 ^^^ (w1 &&& mask), acc.c2 ^^^ (w2 &&& mask)⟩

@[noinline] def productBucketLoop (weights : PlanarE) (polys : ByteArray) (bit : UInt64)
    (remaining idx : Nat) (a0 a1 a2 : UInt64) : E :=
  foldRangeLoop
    (fun acc pos =>
      let mask := 0 - ((readWordLE polys pos >>> bit) &&& 1)
      accumulateProductLimbs (readWordLE weights.c0 pos) (readWordLE weights.c1 pos)
        (readWordLE weights.c2 pos) mask acc)
    remaining idx ⟨a0, a1, a2⟩

/-- Pure total carryless product (low 64 bits) via structural `Fin.foldl` (no `BEq UInt64`). -/
def clmul64 (a b : UInt64) : UInt64 :=
  foldRange 64
    (fun acc idx =>
      let sh := UInt64.ofNat idx
      acc ^^^ selectBit (a <<< sh) b sh)
    0

/-- Pure total carryless product (high 64 bits) via structural `Fin.foldl` (no `BEq UInt64`). -/
def clmul64Hi (a b : UInt64) : UInt64 :=
  foldRange 63
    (fun acc idx =>
      let bit := idx + 1
      let sh := UInt64.ofNat bit
      let rsh := UInt64.ofNat (64 - bit)
      acc ^^^ selectBit (a >>> rsh) b sh)
    0

/-- 24-bit carryless product for RMFE embedded words (`embedBits = 24`), software only. -/
@[noinline] def clmul24Soft (a b : UInt64) : UInt64 :=
  selectBit a b 0 ^^^ selectBit (a <<< 1) b 1 ^^^
  selectBit (a <<< 2) b 2 ^^^ selectBit (a <<< 3) b 3 ^^^
  selectBit (a <<< 4) b 4 ^^^ selectBit (a <<< 5) b 5 ^^^
  selectBit (a <<< 6) b 6 ^^^ selectBit (a <<< 7) b 7 ^^^
  selectBit (a <<< 8) b 8 ^^^ selectBit (a <<< 9) b 9 ^^^
  selectBit (a <<< 10) b 10 ^^^ selectBit (a <<< 11) b 11 ^^^
  selectBit (a <<< 12) b 12 ^^^ selectBit (a <<< 13) b 13 ^^^
  selectBit (a <<< 14) b 14 ^^^ selectBit (a <<< 15) b 15 ^^^
  selectBit (a <<< 16) b 16 ^^^ selectBit (a <<< 17) b 17 ^^^
  selectBit (a <<< 18) b 18 ^^^ selectBit (a <<< 19) b 19 ^^^
  selectBit (a <<< 20) b 20 ^^^ selectBit (a <<< 21) b 21 ^^^
  selectBit (a <<< 22) b 22 ^^^ selectBit (a <<< 23) b 23

/-- Low 64 bits of a 64x64 carryless product (pure software `UInt64` kernel). -/
@[noinline] def clmulLoSoft (a b : UInt64) : UInt64 :=
  clmul64 a b

/-- High 64 bits of a 64x64 carryless product (pure software `UInt64` kernel). -/
@[noinline] def clmulHiSoft (a b : UInt64) : UInt64 :=
  clmul64Hi a b

/-- Reduced GF(2^64) carryless product via `clmul64` / `clmul64Hi` (software only). -/
@[noinline] def clmul64Soft (a b : UInt64) : UInt64 :=
  Model.Field.nativeReduce (clmul64 a b) (clmul64Hi a b)

/-- Unboxed GF(2^8) linear map on the low byte (pure software `UInt64`, no GFNI claim). -/
@[noinline] def gf2AffineSoft (x m : UInt64) : UInt64 :=
  let xb := x &&& 0xff
  foldRange 8
    (fun acc row =>
      let rShift := UInt64.ofNat row
      let prod := xb &&& ((m >>> (rShift * 8)) &&& 0xff)
      let p4 := prod ^^^ (prod >>> 4)
      let p2 := p4 ^^^ (p4 >>> 2)
      let parity := (p2 ^^^ (p2 >>> 1)) &&& 1
      acc ||| (parity <<< rShift))
    0

/-- RMFE projection from 47-bit product polynomial back to a 16-bit pack mask (software only). -/
@[noinline] def rmfeProjectSoft (poly : UInt64) : UInt64 :=
  foldRange packSize
    (fun acc lane =>
      let projMask := rmfeProject[lane]?.getD 0
      let masked := poly &&& projMask
      let p32 := masked ^^^ (masked >>> 32)
      let p16 := p32 ^^^ (p32 >>> 16)
      let p8 := p16 ^^^ (p16 >>> 8)
      let p4 := p8 ^^^ (p8 >>> 4)
      let p2 := p4 ^^^ (p4 >>> 2)
      let parity := (p2 ^^^ (p2 >>> 1)) &&& 1
      acc ||| (parity <<< UInt64.ofNat lane))
    0

/-- Carryless chi product matching `Spec.KeccakGkr.chiPolynomial`. -/
@[inline] def chiProduct (left mid right : UInt64) : UInt64 :=
  clmul24Soft onesMask (left ^^^ right) ^^^ clmul24Soft mid right

def buildEmbedBytes : ByteArray :=
  foldRange (1 <<< packSize)
    (fun b bits => pushWordLE b (embedUnit (UInt64.ofNat bits)))
    (ByteArray.emptyWithCapacity (8 * (1 <<< packSize)))

@[inline] def embedLookupFlat (embedBytes : ByteArray) (bits : UInt64) : UInt64 :=
  readWordLE embedBytes (bits &&& 0xffff).toNat

@[inline] def wordAtFlat (committed : ByteArray) (base width slot step : Nat) : K :=
  if step < width then readWordLE committed (base + slot * width + step) else 0

/-- Double-buffered 1600-bitplane round tape reused in place across all 24 Keccak rounds. -/
structure BitplaneTape where
  cur : ByteArray
  nxt : ByteArray
  scratch : ByteArray
  deriving Inhabited

def bitplaneTapeAlloc : BitplaneTape :=
  ⟨allocWords bitCount, allocWords bitCount, allocWords (2 * 5 * wordBits)⟩

/-- Load 64 instances (`4` consecutive 16-bit RMFE packs) into `UInt64` bitplanes in place. -/
def loadWordBitplanes (committed : ByteArray) (base width baseStep : Nat)
    (cur : ByteArray) : ByteArray :=
  foldRange stateLanes
    (fun buf lane =>
      let lBase := wordBits * lane
      let cleared := foldRange wordBits (fun b z => writeWordLE b (lBase + z) 0) buf
      foldRange wordBits
        (fun b inst =>
          let w := wordAtFlat committed base width lane (baseStep + inst)
          let sh := UInt64.ofNat inst
          foldRange wordBits
            (fun inner z =>
              let bit := (w >>> UInt64.ofNat z) &&& 1
              let prev := readWordLE inner (lBase + z)
              writeWordLE inner (lBase + z) (prev ||| (bit <<< sh)))
            b)
        cleared)
    cur

/-- Keccak `theta`, `rho`, `pi` across 64 packed instances in place (`cur -> nxt`). -/
@[noinline] def linearBitplanes (tape : BitplaneTape) : BitplaneTape :=
  let scratch1 := foldRange 5
    (fun sc x =>
      let xBase := wordBits * x
      foldRange wordBits
        (fun s z =>
          let idx := xBase + z
          let p := readWordLE tape.cur idx ^^^
            readWordLE tape.cur (idx + 320) ^^^
            readWordLE tape.cur (idx + 640) ^^^
            readWordLE tape.cur (idx + 960) ^^^
            readWordLE tape.cur (idx + 1280)
          writeWordLE s idx p)
        sc)
    tape.scratch
  let scratch2 := foldRange 5
    (fun sc x =>
      let leftBase := wordBits * ((x + 4) % 5)
      let rightBase := wordBits * ((x + 1) % 5)
      let dstBase := 320 + wordBits * x
      foldRange wordBits
        (fun s z =>
          let d := readWordLE s (leftBase + z) ^^^
            readWordLE s (rightBase + (z + 63) % wordBits)
          writeWordLE s (dstBase + z) d)
        sc)
    scratch1
  let nxt := foldRange stateLanes
    (fun out lane =>
      let rot := Spec.Keccak.rho[lane]?.getD 0
      let img := keccakPi[lane]?.getD 0
      let aBase := wordBits * lane
      let dBase := 320 + wordBits * (lane % 5)
      let outBase := wordBits * img
      foldRange wordBits
        (fun o z =>
          let mixed := readWordLE tape.cur (aBase + z) ^^^ readWordLE scratch2 (dBase + z)
          writeWordLE o (outBase + (z + rot) % wordBits) mixed)
        out)
    tape.nxt
  ⟨tape.cur, nxt, scratch2⟩

/-- Keccak `chi` and `iota` across 64 packed instances in place (`nxt -> cur`). -/
@[noinline] def chiIotaBitplanes (tape : BitplaneTape) (rc : UInt64) : BitplaneTape :=
  let cur := foldRange 5
    (fun out row =>
      let rowBase := 320 * row
      foldRange wordBits
        (fun o z =>
          let p0 := rowBase + z
          let p1 := p0 + 64
          let p2 := p0 + 128
          let p3 := p0 + 192
          let p4 := p0 + 256
          let u0 := readWordLE tape.nxt p0
          let u1 := readWordLE tape.nxt p1
          let u2 := readWordLE tape.nxt p2
          let u3 := readWordLE tape.nxt p3
          let u4 := readWordLE tape.nxt p4
          let c0Raw := u0 ^^^ ((~~~u1) &&& u2)
          let c0 :=
            if row = 0 then
              let flip := 0 - ((rc >>> UInt64.ofNat z) &&& 1)
              c0Raw ^^^ flip
            else c0Raw
          let c1 := u1 ^^^ ((~~~u2) &&& u3)
          let c2 := u2 ^^^ ((~~~u3) &&& u4)
          let c3 := u3 ^^^ ((~~~u4) &&& u0)
          let c4 := u4 ^^^ ((~~~u0) &&& u1)
          let o0 := writeWordLE o p0 c0
          let o1 := writeWordLE o0 p1 c1
          let o2 := writeWordLE o1 p2 c2
          let o3 := writeWordLE o2 p3 c3
          writeWordLE o3 p4 c4)
        out)
    tape.cur
  ⟨cur, tape.nxt, tape.scratch⟩

/--
Flat pre-chi 64-instance `UInt64` bitplane store:
word `(wordPack * keccakRounds + round) * bitCount + position` holds 4 consecutive 16-bit RMFE
packs `4 * wordPack .. 4 * wordPack + 3` in bits `0..15`, `16..31`, `32..47`, `48..63`.
-/
structure MaskTape where
  bytes : ByteArray
  numPacks : Nat
  deriving Inhabited

@[inline] def wordMaskOffset (wordPack round : Nat) : Nat :=
  (wordPack * keccakRounds + round) * bitCount

@[inline] def readPackMask (masks : MaskTape) (pack round pos : Nat) : UInt64 :=
  let word := readWordLE masks.bytes (wordMaskOffset (pack / 4) round + pos)
  (word >>> UInt64.ofNat (16 * (pack % 4))) &&& 0xffff

/-- Sixteen disjoint range slices `[start, stop)`. -/
def packTasks (total : Nat) : Array (Nat × Nat) :=
  let workers := 16
  let span := (total + workers - 1) / workers
  foldRange workers
    (fun acc worker =>
      let start := worker * span
      let stop := min total (start + span)
      if start < stop then acc.push (start, stop) else acc)
    #[]

@[noinline] def buildMaskRangeFlat (committed : ByteArray) (base width startWord stopWord : Nat) :
    ByteArray :=
  let count := stopWord - startWord
  let maskBytes0 := allocWords (count * keccakRounds * bitCount)
  let tape0 := bitplaneTapeAlloc
  let built := foldRange count
    (fun state offset =>
      let wordPack := startWord + offset
      let curLoaded := loadWordBitplanes committed base width (wordBits * wordPack) state.1.cur
      let tInit : BitplaneTape := ⟨curLoaded, state.1.nxt, state.1.scratch⟩
      foldRange keccakRounds
        (fun inner round =>
          let lin := linearBitplanes inner.1
          let dstBase := wordMaskOffset offset round
          let copied := foldRange bitCount
            (fun mb pos => writeWordLE mb (dstBase + pos) (readWordLE lin.nxt pos))
            inner.2
          let stepped := chiIotaBitplanes lin (Spec.Keccak.rc[round]?.getD 0)
          (stepped, copied))
        (tInit, state.2))
    (tape0, maskBytes0)
  built.2

def buildMaskTapeFlat (committed : ByteArray) (base width : Nat) : MaskTape :=
  let numPacks := width / packSize
  let numWords := (numPacks + 3) / 4
  ⟨buildMaskRangeFlat committed base width 0 numWords, numPacks⟩

def taskBytesValue (task : Task (Except IO.Error ByteArray)) : ByteArray :=
  match task.get with
  | Except.ok value => value
  | Except.error _ => ByteArray.empty

/-- 16-way `IO.asTask` 64-instance bitplane builder joined in deterministic pack order. -/
def buildMaskTapePar (committed : ByteArray) (base width : Nat) : IO MaskTape := do
  let numPacks := width / packSize
  let numWords := (numPacks + 3) / 4
  if numWords < 16 then
    pure ⟨buildMaskRangeFlat committed base width 0 numWords, numPacks⟩
  else
    let ranges := packTasks numWords
    let tasks ← foldRange ranges.size
      (fun acc index => do
        let list ← acc
        let range := ranges[index]?.getD (0, 0)
        let task ← IO.asTask (prio := .dedicated)
          (IO.lazyPure fun () => buildMaskRangeFlat committed base width range.1 range.2)
        pure (list.push task))
      (pure (Array.emptyWithCapacity ranges.size))
    let totalBytes := 8 * numWords * keccakRounds * bitCount
    let joined := foldRange tasks.size
      (fun acc index =>
        match tasks[index]? with
        | some task => acc ++ taskBytesValue task
        | none => acc)
      (ByteArray.emptyWithCapacity totalBytes)
    pure ⟨joined, numPacks⟩

/-- Decode `MaskTape` to the nested `Array` shape for differential unit checks. -/
def decodeMaskTape (masks : MaskTape) : Array (Array (Array UInt64)) :=
  (Array.range keccakRounds).map fun round =>
    (Array.range masks.numPacks).map fun pack =>
      (Array.range bitCount).map fun pos => readPackMask masks pack round pos

@[noinline] def productRangeFlat (masks : MaskTape) (embedBytes : ByteArray)
    (layer eqsSize pVars : Nat) (eqs weights : PlanarE) (start stop : Nat) : PlanarE :=
  let numPacks := 1 <<< pVars
  let segCount := (eqsSize + numPacks - 1) / numPacks
  let coeffs0 := planarEAlloc productBits
  let polyScratch0 := allocWords bitCount
  let res := foldRange segCount
    (fun outer seg =>
      let round := layerRound layer seg
      foldRange (stop - start)
        (fun inner offset =>
          let pack := start + offset
          let y := (seg <<< pVars) + pack
          if eqsSize ≤ y then inner
          else if round < keccakRounds && pack < masks.numPacks then
            let scale := planarEGet eqs y
            let polys := foldRange 5
              (fun pRow row =>
                let rBase := 320 * row
                foldRange wordBits
                  (fun pZ z =>
                    let p0 := rBase + z
                    let p1 := p0 + 64
                    let p2 := p0 + 128
                    let p3 := p0 + 192
                    let p4 := p0 + 256
                    let e0 := embedLookupFlat embedBytes (readPackMask masks pack round p0)
                    let e1 := embedLookupFlat embedBytes (readPackMask masks pack round p1)
                    let e2 := embedLookupFlat embedBytes (readPackMask masks pack round p2)
                    let e3 := embedLookupFlat embedBytes (readPackMask masks pack round p3)
                    let e4 := embedLookupFlat embedBytes (readPackMask masks pack round p4)
                    let b0 := writeWordLE pZ p0 (chiProduct e0 e1 e2)
                    let b1 := writeWordLE b0 p1 (chiProduct e1 e2 e3)
                    let b2 := writeWordLE b1 p2 (chiProduct e2 e3 e4)
                    let b3 := writeWordLE b2 p3 (chiProduct e3 e4 e0)
                    writeWordLE b3 p4 (chiProduct e4 e0 e1))
                  pRow)
              inner.2
            let nextCoeffs := foldRange productBits
              (fun cf c =>
                let bit := UInt64.ofNat c
                let bucket := productBucketLoop weights polys bit bitCount 0 0 0 0
                let prev := planarEGet cf c
                planarESet cf c (eadd prev (nativeKaratsuba scale bucket)))
              inner.1
            (nextCoeffs, polys)
          else inner)
        outer)
    (coeffs0, polyScratch0)
  res.1

def joinProductsFlat (parts : Array PlanarE) : Array E :=
  let merged := foldRange parts.size
    (fun acc idx =>
      let part := parts[idx]?.getD (planarEEmpty 0)
      foldRange productBits
        (fun cur c => planarESet cur c (eadd (planarEGet cur c) (planarEGet part c)))
        acc)
    (planarEAlloc productBits)
  decodePlanarE merged

def taskPlanarValue (task : Task (Except IO.Error PlanarE)) : PlanarE :=
  match task.get with
  | Except.ok value => value
  | Except.error _ => planarEAlloc productBits

/-- 16-way `IO.asTask` pack-range reduction joined deterministically before transcript absorb. -/
def productAtFlat (masks : MaskTape) (embedBytes : ByteArray) (layer : Nat)
    (eqs : Array E) (weights : PlanarE) : IO (Array E) := do
  let pVars := Nat.log2 eqs.size - segLog
  let numPacks := 1 <<< pVars
  let eqsPlanar := encodePlanarE eqs
  if numPacks < 32 then
    pure (decodePlanarE (productRangeFlat masks embedBytes layer eqs.size pVars
      eqsPlanar weights 0 numPacks))
  else
    let ranges := packTasks numPacks
    let tasks ← foldRange ranges.size
      (fun acc index => do
        let list ← acc
        let range := ranges[index]?.getD (0, 0)
        let task ← IO.asTask (prio := .dedicated)
          (IO.lazyPure fun () => productRangeFlat masks embedBytes layer eqs.size pVars
            eqsPlanar weights range.1 range.2)
        pure (list.push task))
      (pure (Array.emptyWithCapacity ranges.size))
    let parts := foldRange tasks.size
      (fun acc index =>
        match tasks[index]? with
        | some task => acc.push (taskPlanarValue task)
        | none => acc)
      (Array.emptyWithCapacity tasks.size)
    pure (joinProductsFlat parts)

/-- Double-buffered planar `E` tape reused across all 12 GKR layers. -/
structure RoundETape where
  cur : PlanarE
  nxt : PlanarE
  deriving Inhabited

/-- Planar buffers for the 11 local sumcheck rounds (`cube = 2048`) and transpose scratch. -/
structure LocalETape where
  w : PlanarE
  a : PlanarE
  b : PlanarE
  c : PlanarE
  deriving Inhabited

def byteSumsPlanar (mu : Array E) (offset : Nat) : PlanarE :=
  foldRange 256
    (fun acc byte =>
      let sum := foldRange 8
        (fun cur bit =>
          if (byte >>> bit) % 2 = 1 then eadd cur (mu[offset + bit]?.getD zero) else cur)
        zero
      planarEPush acc sum)
    (planarEEmpty 256)

/-- Populate `tape.cur` in place over pack range `[startPack, stopPack)`. -/
@[noinline] def fillInitialRangeFlat (masks : MaskTape) (layer : Nat) (loSums hiSums : PlanarE)
    (startPack stopPack : Nat) : PlanarE :=
  let packCount := stopPack - startPack
  let out0 := planarEAlloc (segments * packCount * bitCount)
  foldRange segments
    (fun tbl seg =>
      let round := layerRound layer seg
      foldRange packCount
        (fun segTbl offset =>
          let pack := startPack + offset
          let rowBase := (seg * packCount + offset) * bitCount
          foldRange bitCount
            (fun inner pos =>
              let mask := readPackMask masks pack round pos
              let lo := planarEGet loSums (mask &&& 0xff).toNat
              let hi := planarEGet hiSums ((mask >>> 8) &&& 0xff).toNat
              planarESet inner (rowBase + pos) (eadd lo hi))
            segTbl)
        tbl)
    out0

/-- Populate `tape.cur` in place with the layer's initial `segments * numPacks * 1600` table. -/
@[noinline] def fillInitialTableFlat (masks : MaskTape) (layer : Nat) (mu : Array E)
    (cur : PlanarE) : IO PlanarE := do
  let loSums := byteSumsPlanar mu 0
  let hiSums := byteSumsPlanar mu 8
  if masks.numPacks < 32 then
    let totalRows := segments * masks.numPacks
    pure <| foldRange totalRows
      (fun tbl y =>
        let seg := y / masks.numPacks
        let pack := y % masks.numPacks
        let round := layerRound layer seg
        let rowBase := y * bitCount
        foldRange bitCount
          (fun inner pos =>
            let mask := readPackMask masks pack round pos
            let lo := planarEGet loSums (mask &&& 0xff).toNat
            let hi := planarEGet hiSums ((mask >>> 8) &&& 0xff).toNat
            planarESet inner (rowBase + pos) (eadd lo hi))
          tbl)
      cur
  else
    let ranges := packTasks masks.numPacks
    let tasks ← foldRange ranges.size
      (fun acc index => do
        let list ← acc
        let range := ranges[index]?.getD (0, 0)
        let task ← IO.asTask (prio := .dedicated)
          (IO.lazyPure fun () => fillInitialRangeFlat masks layer loSums hiSums range.1 range.2)
        pure (list.push task))
      (pure (Array.emptyWithCapacity ranges.size))
    pure <| foldRange tasks.size
      (fun dst index =>
        let range := ranges[index]?.getD (0, 0)
        let pCount := range.2 - range.1
        match tasks[index]? with
        | some task =>
          let part := taskPlanarValue task
          foldRange segments
            (fun dSeg seg =>
              foldRange (pCount * bitCount)
                (fun inner cell =>
                  let srcIdx := seg * pCount * bitCount + cell
                  let dstIdx := (seg * masks.numPacks + range.1) * bitCount + cell
                  planarESet inner dstIdx (planarEGet part srcIdx))
                dSeg)
            dst
        | none => dst)
      cur

/-- Sumcheck pair evaluations on range `[start, stop)` over the planar `cur` buffer. -/
@[noinline] def pairSumsRangeFlat (cur : PlanarE) (claimWeights : PlanarE)
    (eqs : Array E) (kappa : E) (start stop : Nat) : E × E :=
  foldRange (stop - start)
    (fun acc offset =>
      let index := start + offset
      let lowBase := (2 * index) * bitCount
      let highBase := (2 * index + 1) * bitCount
      let eqv := eqs[index]?.getD zero
      let sums := foldRange 5
        (fun rAcc row =>
          let rBase := 320 * row
          foldRange wordBits
            (fun zAcc z =>
              let p0 := rBase + z
              let p1 := p0 + 64
              let p2 := p0 + 128
              let p3 := p0 + 192
              let p4 := p0 + 256
              let l0 := planarEGet cur (lowBase + p0)
              let l1 := planarEGet cur (lowBase + p1)
              let l2 := planarEGet cur (lowBase + p2)
              let l3 := planarEGet cur (lowBase + p3)
              let l4 := planarEGet cur (lowBase + p4)
              let h0 := planarEGet cur (highBase + p0)
              let h1 := planarEGet cur (highBase + p1)
              let h2 := planarEGet cur (highBase + p2)
              let h3 := planarEGet cur (highBase + p3)
              let h4 := planarEGet cur (highBase + p4)
              let w0 := planarEGet claimWeights p0
              let w1 := planarEGet claimWeights p1
              let w2 := planarEGet claimWeights p2
              let w3 := planarEGet claimWeights p3
              let w4 := planarEGet claimWeights p4
              let z0 := nativeKaratsuba w0
                (eadd (nativeKaratsuba kappa l0) (nativeKaratsuba (eadd kappa l1) l2))
              let z1 := nativeKaratsuba w1
                (eadd (nativeKaratsuba kappa l1) (nativeKaratsuba (eadd kappa l2) l3))
              let z2 := nativeKaratsuba w2
                (eadd (nativeKaratsuba kappa l2) (nativeKaratsuba (eadd kappa l3) l4))
              let z3 := nativeKaratsuba w3
                (eadd (nativeKaratsuba kappa l3) (nativeKaratsuba (eadd kappa l4) l0))
              let z4 := nativeKaratsuba w4
                (eadd (nativeKaratsuba kappa l4) (nativeKaratsuba (eadd kappa l0) l1))
              let d0 := eadd l0 h0
              let d1 := eadd l1 h1
              let d2 := eadd l2 h2
              let d3 := eadd l3 h3
              let d4 := eadd l4 h4
              let i0 := nativeKaratsuba w0 (nativeKaratsuba d1 d2)
              let i1 := nativeKaratsuba w1 (nativeKaratsuba d2 d3)
              let i2 := nativeKaratsuba w2 (nativeKaratsuba d3 d4)
              let i3 := nativeKaratsuba w3 (nativeKaratsuba d4 d0)
              let i4 := nativeKaratsuba w4 (nativeKaratsuba d0 d1)
              let zSum := eadd (eadd (eadd z0 z1) (eadd z2 z3)) z4
              let iSum := eadd (eadd (eadd i0 i1) (eadd i2 i3)) i4
              (eadd zAcc.1 zSum, eadd zAcc.2 iSum))
            rAcc)
        (zero, zero)
      (eadd acc.1 (nativeKaratsuba eqv sums.1), eadd acc.2 (nativeKaratsuba eqv sums.2)))
    (zero, zero)

def pairSumsFlat (cur : PlanarE) (activeRows : Nat) (claimWeights : PlanarE)
    (eqs : Array E) (kappa : E) : E × E :=
  pairSumsRangeFlat cur claimWeights eqs kappa 0 (activeRows / 2)

def taskPairValue (task : Task (Except IO.Error (E × E))) : E × E :=
  match task.get with
  | Except.ok value => value
  | Except.error _ => (zero, zero)

def pairSumsPar (cur : PlanarE) (activeRows : Nat) (claimWeights : PlanarE)
    (eqs : Array E) (kappa : E) : IO (E × E) := do
  let pairs := activeRows / 2
  if pairs < 64 then
    pure (pairSumsRangeFlat cur claimWeights eqs kappa 0 pairs)
  else
    let ranges := packTasks pairs
    let tasks ← foldRange ranges.size
      (fun acc index => do
        let list ← acc
        let range := ranges[index]?.getD (0, 0)
        let task ← IO.asTask (prio := .dedicated)
          (IO.lazyPure fun () => pairSumsRangeFlat cur claimWeights eqs kappa range.1 range.2)
        pure (list.push task))
      (pure (Array.emptyWithCapacity ranges.size))
    pure <| foldRange tasks.size
      (fun acc index =>
        match tasks[index]? with
        | some task =>
          let p := taskPairValue task
          (eadd acc.1 p.1, eadd acc.2 p.2)
        | none => acc)
      (zero, zero)

/-- Fold rows with the source and destination owned separately. -/
@[noinline] def foldRowsFlat (tape : RoundETape) (activeRows : Nat) (challenge : E) : RoundETape :=
  match tape with
  | ⟨cur, nxt⟩ =>
    let half := activeRows / 2
    let nxt := foldRange half
      (fun dst index =>
        let lowBase := (2 * index) * bitCount
        let highBase := (2 * index + 1) * bitCount
        let dstBase := index * bitCount
        foldRange bitCount
          (fun inner pos =>
            let lo := planarEGet cur (lowBase + pos)
            let hi := planarEGet cur (highBase + pos)
            planarESet inner (dstBase + pos) (eadd lo (nativeKaratsuba challenge (eadd lo hi))))
          dst)
      nxt
    ⟨nxt, cur⟩

def initLocalTape (loc : LocalETape) (row0 : PlanarE) (weights : PlanarE) : LocalETape :=
  let cube := 1 <<< localBits
  let w := foldRange cube
    (fun buf j => planarESet buf j (if j < bitCount then planarEGet weights j else zero))
    loc.w
  let a := foldRange cube
    (fun buf j => planarESet buf j (if j < bitCount then planarEGet row0 j else zero))
    loc.a
  let b := foldRange cube
    (fun buf j => planarESet buf j (if j < bitCount then planarEGet row0 (along j 1) else zero))
    loc.b
  let c := foldRange cube
    (fun buf j => planarESet buf j (if j < bitCount then planarEGet row0 (along j 2) else zero))
    loc.c
  ⟨w, a, b, c⟩

@[noinline] def localRoundFlat (loc : LocalETape) (half : Nat) (kappa scale : E) : Array E :=
  let raw := foldRange half
    (fun acc index =>
      let i0 := 2 * index
      let i1 := i0 + 1
      let w0 := planarEGet loc.w i0
      let w1 := eadd w0 (planarEGet loc.w i1)
      let t00 := planarEGet loc.a i0
      let t01 := eadd t00 (planarEGet loc.a i1)
      let t10 := planarEGet loc.b i0
      let t11 := eadd t10 (planarEGet loc.b i1)
      let t20 := planarEGet loc.c i0
      let t21 := eadd t20 (planarEGet loc.c i1)
      let u0 := eadd kappa t10
      let p0 := eadd (nativeKaratsuba kappa t00) (nativeKaratsuba u0 t20)
      let p1 := eadd (eadd (nativeKaratsuba kappa t01) (nativeKaratsuba u0 t21))
        (nativeKaratsuba t11 t20)
      let p2 := nativeKaratsuba t11 t21
      (eadd acc.1 (nativeKaratsuba w0 p0),
        eadd acc.2.1 (eadd (nativeKaratsuba w0 p1) (nativeKaratsuba w1 p0)),
        eadd acc.2.2.1 (eadd (nativeKaratsuba w0 p2) (nativeKaratsuba w1 p1)),
        eadd acc.2.2.2 (nativeKaratsuba w1 p2)))
    (zero, zero, zero, zero)
  #[nativeKaratsuba scale raw.1, nativeKaratsuba scale raw.2.1,
    nativeKaratsuba scale raw.2.2.1, nativeKaratsuba scale raw.2.2.2]

@[noinline] def fold1InPlace (buf : PlanarE) (half : Nat) (challenge : E) : PlanarE :=
  foldRange half
    (fun acc index =>
      let lo := planarEGet acc (2 * index)
      let hi := planarEGet acc (2 * index + 1)
      planarESet acc index (eadd lo (nativeKaratsuba challenge (eadd lo hi))))
    buf

/-- Adjoint of `theta, rho, pi` into a planar weight buffer in place. -/
@[noinline] def linearTransposePlanar (chiIn gathered colScratch out : PlanarE) :
    PlanarE × PlanarE × PlanarE :=
  let g := foldRange stateLanes
    (fun acc lane =>
      let rot := Spec.Keccak.rho[lane]?.getD 0
      let img := keccakPi[lane]?.getD 0
      foldRange wordBits
        (fun cur z =>
          planarESet cur (wordBits * lane + z)
            (planarEGet chiIn (wordBits * img + (z + rot) % wordBits)))
        acc)
    gathered
  let cols0 := planarEZero colScratch (5 * wordBits)
  let cols := foldRange bitCount
    (fun acc j =>
      let col := wordBits * ((j / wordBits) % 5) + j % wordBits
      planarESet acc col (eadd (planarEGet acc col) (planarEGet g j)))
    cols0
  let res := foldRange bitCount
    (fun acc j =>
      let x := (j / wordBits) % 5
      let z := j % wordBits
      let v := eadd (planarEGet g j)
        (eadd (planarEGet cols (wordBits * ((x + 1) % 5) + z))
          (planarEGet cols (wordBits * ((x + 4) % 5) + (z + 1) % wordBits)))
      planarESet acc j v)
    out
  (g, cols, res)

structure FlatLayerClaim where
  value : E
  mu : Array E
  point : Array E
  weights : PlanarE
  deriving Inhabited

def proveLayerFlat (state : ProverState) (masks : MaskTape) (embedBytes : ByteArray)
    (layer : Nat) (claim : FlatLayerClaim) (tape : RoundETape) (loc : LocalETape) :
    IO (FlatLayerClaim × ProverState × RoundETape × LocalETape) := do
  let product ← productAtFlat masks embedBytes layer (eqTable claim.point) claim.weights
  let sent := addScalars state product
  let (seed, s1) := sampleChallenge sent
  let mu := instanceWeights seed
  let kappa := sumSlice mu
  let value0 := polyEval product seed
  let cur0 ← fillInitialTableFlat masks layer mu tape.cur
  let tape0 : RoundETape := ⟨cur0, tape.nxt⟩
  let startRows := segments * masks.numPacks
  let bound ← foldRange claim.point.size
    (fun accIo index => do
      let acc ← accIo
      let point := acc.1
      let value := acc.2.1
      let scale := acc.2.2.1
      let current := acc.2.2.2.1
      let activeRows := acc.2.2.2.2.1
      let rTape := acc.2.2.2.2.2
      let here := claim.point[index]?.getD zero
      let later := eqTable (claim.point.extract (index + 1) claim.point.size)
      let pair ← pairSumsPar rTape.cur activeRows claim.weights later kappa
      let coeffs := roundCoefficients scale pair.1 pair.2 value here
      let written := addRoundPoly current coeffs true
      let (challenge, next) := sampleChallenge written
      let grown := eadd (eadd one here) challenge
      let nextTape := foldRowsFlat rTape activeRows challenge
      pure (point.push challenge, nativeKaratsuba grown (polyEval coeffs challenge),
        nativeKaratsuba scale grown, next, (activeRows / 2, nextTape)))
    (pure (Array.emptyWithCapacity claim.point.size, value0, one, s1, (startRows, tape0)))
  let point := bound.1
  let scale := bound.2.2.1
  let current := bound.2.2.2.1
  let rTape := bound.2.2.2.2.2
  let loc0 := initLocalTape loc rTape.cur claim.weights
  let boundLocal := foldRange localBits
    (fun acc round =>
      let lp := acc.1
      let lTape := acc.2.1
      let cur := acc.2.2
      let half := 1 <<< (localBits - 1 - round)
      let coeffs := localRoundFlat lTape half kappa scale
      let written := addRoundPoly cur coeffs false
      let (challenge, next) := sampleChallenge written
      let folded : LocalETape :=
        ⟨fold1InPlace lTape.w half challenge,
         fold1InPlace lTape.a half challenge,
         fold1InPlace lTape.b half challenge,
         fold1InPlace lTape.c half challenge⟩
      (lp.push challenge, folded, next))
    (Array.emptyWithCapacity localBits, loc0, current)
  let lp := boundLocal.1
  let lTape := boundLocal.2.1
  let cur := boundLocal.2.2
  let t0 := planarEGet lTape.a 0
  let t1 := planarEGet lTape.b 0
  let t2 := planarEGet lTape.c 0
  let written := addScalars cur #[t0, t1, t2]
  let (beta, done) := sampleChallenge written
  let eqv := eqTable lp
  let chiBuf := foldRange bitCount
    (fun buf j =>
      let v := eadd (eqv[j]?.getD zero)
        (nativeKaratsuba beta
          (eadd (eqv[along j 4]?.getD zero) (nativeKaratsuba beta (eqv[along j 3]?.getD zero))))
      planarESet buf j v)
    lTape.a
  let transposed := linearTransposePlanar chiBuf lTape.b lTape.c claim.weights
  let nextVal := eadd t0 (nativeKaratsuba beta (eadd t1 (nativeKaratsuba beta t2)))
  let nextLoc : LocalETape := ⟨lTape.w, chiBuf, transposed.1, transposed.2.1⟩
  pure (⟨nextVal, mu, point, transposed.2.2⟩, done, rTape, nextLoc)

/-- Flat slot-bit weight array (`(1 <<< slotBits) * wordBits`) without `Array (Array E)`. -/
def slotWeightsFlat (point : Array E) (weights : PlanarE) (first count : Nat) : Array E :=
  let segmentsEq := eqTable (point.extract (point.size - segLog) point.size)
  let slots := 1 <<< slotBits
  let out0 := planarEAlloc (slots * wordBits)
  let filled := foldRange count
    (fun buf segment =>
      let segScale := segmentsEq[segment]?.getD zero
      foldRange bitCount
        (fun cur position =>
          let slot := stateLanes * (first + segment) + position / wordBits
          let dst := slot * wordBits + position % wordBits
          planarESet cur dst (nativeKaratsuba segScale (planarEGet weights position)))
        buf)
    out0
  decodePlanarE filled

/-- Flat word weights (`1 <<< slotBits`) without intermediate `Array (Array E)`. -/
def wordWeightsFlat (point : Array E) (weights : PlanarE) : Array E :=
  let segmentsEq := eqTable (point.extract (point.size - segLog) point.size)
  let slots := 1 <<< slotBits
  let out0 := planarEAlloc slots
  let filled := foldRange (segments - 1)
    (fun buf segment =>
      let segScale := segmentsEq[segment]?.getD zero
      foldRange stateLanes
        (fun cur lane =>
          let slot := stateLanes * (1 + segment) + lane
          planarESet cur slot (nativeKaratsuba segScale (planarEGet weights (lane * wordBits))))
        buf)
    out0
  decodePlanarE filled

@[noinline] def outputWordsRangePacks (committed : ByteArray) (base width : Nat)
    (eqs : Array E) (startPack stopPack : Nat) : PlanarE :=
  let slots := 1 <<< slotBits
  let startStep := startPack * packSize
  let stepCount := min eqs.size (stopPack * packSize) - startStep
  foldRange slots
    (fun out slot =>
      let sum := foldRange stepCount
        (fun acc offset =>
          let step := startStep + offset
          eadd acc (nativeMulBase (eqs[step]?.getD zero) (wordAtFlat committed base width slot step)))
        zero
      planarESet out slot sum)
    (planarEAlloc slots)

def outputWordsPar (committed : ByteArray) (base width : Nat) (inst : Array E) : IO (Array E) := do
  let eqs := eqTable inst
  let numPacks := width / packSize
  let slots := 1 <<< slotBits
  if numPacks < 32 then
    pure (decodePlanarE (outputWordsRangePacks committed base width eqs 0 numPacks))
  else
    let ranges := packTasks numPacks
    let tasks ← foldRange ranges.size
      (fun acc index => do
        let list ← acc
        let range := ranges[index]?.getD (0, 0)
        let task ← IO.asTask (prio := .dedicated)
          (IO.lazyPure fun () =>
            outputWordsRangePacks committed base width eqs range.1 range.2)
        pure (list.push task))
      (pure (Array.emptyWithCapacity ranges.size))
    let merged := foldRange tasks.size
      (fun acc index =>
        match tasks[index]? with
        | some task =>
          let part := taskPlanarValue task
          foldRange slots
            (fun cur s => planarESet cur s (eadd (planarEGet cur s) (planarEGet part s)))
            acc
        | none => acc)
      (planarEAlloc slots)
    pure (decodePlanarE merged)

def openOutputsWithWords (state : ProverState) (words wordW : Array E)
    (inst : Array E) (value : E) : WordOpening × ProverState :=
  let bound := proveRounds state words wordW 1 one value
  let slot := bound.1
  let word := bound.2.1[0]?.getD zero
  let written := addScalar bound.2.2.2.2 word
  (⟨inst ++ slot, word⟩, written)

@[noinline] def packEvalRangePacks (committed : ByteArray) (base width : Nat)
    (eqs : Array E) (startPack stopPack : Nat) : PlanarE :=
  let slots := 1 <<< slotBits
  let count := slots * packSize * wordBits
  let packSpan := min eqs.size stopPack - startPack
  foldRange slots
    (fun out slot =>
      foldRange packSize
        (fun rowOut packRow =>
          let rowBase := (slot * packSize + packRow) * wordBits
          foldRange wordBits
            (fun bitOut bit =>
              let bShift := UInt64.ofNat bit
              let sum := foldRange packSpan
                (fun acc offset =>
                  let packIndex := startPack + offset
                  let w := wordAtFlat committed base width slot (packIndex * packSize + packRow)
                  maskedAddE acc (eqs[packIndex]?.getD zero) w bShift)
                zero
              planarESet bitOut (rowBase + bit) sum)
            rowOut)
        out)
    (planarEAlloc count)

def packEvalPar (committed : ByteArray) (base width : Nat) (pack : Array E) : IO (Array E) := do
  let eqs := eqTable pack
  let numPacks := width / packSize
  let total := (1 <<< slotBits) * packSize * wordBits
  if numPacks < 32 then
    pure (decodePlanarE (packEvalRangePacks committed base width eqs 0 numPacks))
  else
    let ranges := packTasks numPacks
    let tasks ← foldRange ranges.size
      (fun acc index => do
        let list ← acc
        let range := ranges[index]?.getD (0, 0)
        let task ← IO.asTask (prio := .dedicated)
          (IO.lazyPure fun () =>
            packEvalRangePacks committed base width eqs range.1 range.2)
        pure (list.push task))
      (pure (Array.emptyWithCapacity ranges.size))
    let merged := foldRange tasks.size
      (fun acc index =>
        match tasks[index]? with
        | some task =>
          let part := taskPlanarValue task
          foldRange total
            (fun cur idx => planarESet cur idx (eadd (planarEGet cur idx) (planarEGet part idx)))
            acc
        | none => acc)
      (planarEAlloc total)
    pure (decodePlanarE merged)

def openInputsFlat (state : ProverState) (committed : ByteArray) (base width : Nat)
    (claim : FlatLayerClaim) : IO (Opening × ProverState) := do
  let pack := claim.point.extract 0 (claim.point.size - segLog)
  let folded ← packEvalPar committed base width pack
  let weights := slotWeightsFlat claim.point claim.weights 0 segments
  let instances := perInstance folded weights
  let bound := proveRounds state instances claim.mu 1 one claim.value
  let low := bound.1
  let mu0 := bound.2.2.1[0]?.getD zero
  let value := bound.2.2.2.1
  let current := bound.2.2.2.2
  let slices0 := atInstance folded low
  let slotBound := proveRounds current slices0 weights wordBits mu0 value
  let slices := slotBound.2.1
  let written := addScalars slotBound.2.2.2.2 slices
  pure (⟨low ++ pack ++ slotBound.1, slices⟩, written)

def proveReductionFlat (state : ProverState) (committed : ByteArray) (executed : Nat)
    (output : OutputClaim) (base : Nat := 0) : IO (Openings × ProverState) := do
  let logSteps := stepsLog executed
  let width := 1 <<< logSteps
  let masks ← buildMaskTapePar committed base width
  let embedBytes := buildEmbedBytes
  let (segment, afterSegment) := sampleVec state segLog
  let (lanes, afterLanes) := sampleVec afterSegment laneBits
  let laneEq := eqTable lanes
  let segmentEq := eqTable segment
  let weightsPlanar := foldRange bitCount
    (fun buf position =>
      let v := nativeKaratsuba (laneEq[position / wordBits]?.getD zero)
        (embed (UInt64.ofNat (1 <<< (position % wordBits))))
      planarESet buf position v)
    (planarEAlloc bitCount)
  let last := nativeKaratsuba (segmentEq[segments - 1]?.getD zero)
    (dot (laneEq.extract 0 stateLanes) output.lanes)
  let words ← outputWordsPar committed base width output.instancePoint
  let firstPoint := output.instancePoint.extract packBits output.instancePoint.size ++ segment
  let firstWordWeights := wordWeightsFlat firstPoint weightsPlanar
  let committedValue := dot words firstWordWeights
  let afterValue := if segments > 1 then addScalar afterLanes committedValue else afterLanes
  let firstVal := eadd committedValue last
  let firstFlat : FlatLayerClaim :=
    ⟨firstVal, eqTable (output.instancePoint.extract 0 packBits), firstPoint, weightsPlanar⟩
  let maxCells := segments * masks.numPacks * bitCount
  let rTape0 : RoundETape := ⟨planarEAlloc maxCells, planarEAlloc maxCells⟩
  let cube := 1 <<< localBits
  let lTape0 : LocalETape :=
    ⟨planarEAlloc cube, planarEAlloc cube, planarEAlloc cube, planarEAlloc cube⟩
  let reduced ← foldRange keccakDepth
    (fun acc layer => do
      let st ← acc
      proveLayerFlat st.2.1 masks embedBytes layer st.1 st.2.2.1 st.2.2.2)
    (pure (firstFlat, afterValue, rTape0, lTape0))
  let finalFlat := reduced.1
  let opened := reduced.2.1
  let (outputs, afterOutputs) :=
    if segments > 1 then
      let openedOut := openOutputsWithWords opened words firstWordWeights
        output.instancePoint committedValue
      (some openedOut.1, openedOut.2)
    else (none, opened)
  let inputs ← openInputsFlat afterOutputs committed base width finalFlat
  pure (⟨outputs, inputs.1⟩, inputs.2)

/-- Encode a slice of `K` words as a flat little-endian `ByteArray` (`8 * i` byte layout). -/
def encodeColumn (words : Array K) : ByteArray :=
  foldRange words.size (fun acc i => pushWordLE acc (words[i]?.getD 0))
    (ByteArray.emptyWithCapacity (8 * words.size))

/-- Extract the committed `q_keccak` column window (`span` LE `UInt64` words at `qBase`). -/
def extractQKeccakWindow (bundle : Spec.Witness.WitnessBundle) : ByteArray :=
  let qBase := (bundle.sized.layout.placements[qKeccak]?.join).map Placement.index |>.getD 0
  let executed := bundle.sized.rows[opKeccak]?.getD 0
  let span := (1 <<< slotBits) * (1 <<< stepsLog executed)
  foldRange span
    (fun acc i => pushWordLE acc (bundle.message[qBase + i]?.getD 0))
    (ByteArray.emptyWithCapacity (8 * span))

/--
Flat Keccak-GKR stage prover.

`committed` holds the `q_keccak` `UInt64` words in little-endian layout at word offset `base`
(default `0` when passing the `span`-word `q_keccak` `ByteArray` window directly, or `qBase`
when passing the full flat `bundle.message` buffer). Preserves exact Fiat-Shamir transcript
and opening parity with `proveKeccakGkr`.
-/
def proveKeccakGkrFlat (program : Array Spec.Vm.Op) (iv : ByteArray) (publicInput : Array E)
    (bundle : Spec.Witness.WitnessBundle) (committed : ByteArray) (base : Nat := 0) :
    IO KeccakGkrStageOutput := do
  let bus := Model.Bus.proveBusAndConstraints program iv publicInput bundle
  let executed := bundle.sized.rows[opKeccak]?.getD 0
  let reduced ← proveReductionFlat bus.ps committed executed bus.keccakOutput base
  let qBase := (bundle.sized.layout.placements[qKeccak]?.join).map Placement.index |>.getD 0
  let extra :=
    match reduced.1.outputs with
    | none => #[]
    | some opening => #[⟨qBase, opening.point, opening.value⟩]
  pure ⟨reduced.2, bus.slotClaims ++ extra,
    ⟨qBase, reduced.1.inputs.point, reduced.1.inputs.slices⟩, reduced.1⟩

/-- Convenience wrapper extracting the `q_keccak` `ByteArray` window from `bundle`. -/
def proveKeccakGkrFlatOf (program : Array Spec.Vm.Op) (iv : ByteArray) (publicInput : Array E)
    (bundle : Spec.Witness.WitnessBundle) : IO KeccakGkrStageOutput :=
  proveKeccakGkrFlat program iv publicInput bundle (extractQKeccakWindow bundle) 0

end LeanVmXmss.Model.KeccakGkr
