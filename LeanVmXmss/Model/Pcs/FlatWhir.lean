import Model.Pcs.Whir
import Model.Merkle.Flat
import Model.Witness.Flat

namespace LeanVmXmss.Model.Pcs.FlatWhir

open Spec.Field (K E)
open Model.Merkle (Digest32)
open Model.Pcs.Whir
open Model.Pcs.Ntt (Vec8 foldRange foldRangeLoop)

@[inline] def wordAt (bytes : @& ByteArray) (i : Nat) : K :=
  let off := 8 * i
  if decide (off + 8 ≤ bytes.size) then
    (bytes.get! off).toUInt64 |||
      ((bytes.get! (off + 1)).toUInt64 <<< 8) |||
      ((bytes.get! (off + 2)).toUInt64 <<< 16) |||
      ((bytes.get! (off + 3)).toUInt64 <<< 24) |||
      ((bytes.get! (off + 4)).toUInt64 <<< 32) |||
      ((bytes.get! (off + 5)).toUInt64 <<< 40) |||
      ((bytes.get! (off + 6)).toUInt64 <<< 48) |||
      ((bytes.get! (off + 7)).toUInt64 <<< 56)
  else 0

@[inline] def witnessWord (bytes : @& ByteArray) (i : Nat) : K := wordAt bytes i

@[inline] def isZeroE (v : E) : Bool :=
  decide (v.c0 = 0 ∧ v.c1 = 0 ∧ v.c2 = 0)

@[inline] def eqE (u v : E) : Bool :=
  decide (u.c0 = v.c0 ∧ u.c1 = v.c1 ∧ u.c2 = v.c2)

structure PlanarE where
  c0 : ByteArray
  c1 : ByteArray
  c2 : ByteArray
  deriving Inhabited

@[inline] def planarSize (p : @& PlanarE) : Nat := p.c0.size / 8

def planarEmpty (n : Nat) : PlanarE :=
  ⟨ByteArray.emptyWithCapacity (8 * n),
   ByteArray.emptyWithCapacity (8 * n),
   ByteArray.emptyWithCapacity (8 * n)⟩

@[inline] def planarPush (p : PlanarE) (x : E) : PlanarE :=
  match p with
  | ⟨c0, c1, c2⟩ =>
    ⟨Model.Witness.pushU64LE c0 x.c0,
     Model.Witness.pushU64LE c1 x.c1,
     Model.Witness.pushU64LE c2 x.c2⟩

@[inline] def planarGet (p : @& PlanarE) (i : Nat) : E :=
  ⟨wordAt p.c0 i, wordAt p.c1 i, wordAt p.c2 i⟩

def planarOf (xs : @& Array E) : PlanarE :=
  foldRange xs.size (fun acc i => planarPush acc (xs.getD i Spec.Field.zero)) (planarEmpty xs.size)

def planarToArray (p : @& PlanarE) : Array E :=
  let n := planarSize p
  foldRange n (fun acc i => acc.push (planarGet p i)) (Array.emptyWithCapacity n)

def foldPlanar (p : @& PlanarE) (r : E) : PlanarE :=
  let half := planarSize p / 2
  foldRange half (fun acc i =>
    let lo := planarGet p (2 * i)
    let hi := planarGet p (2 * i + 1)
    planarPush acc (Spec.Field.eadd lo (Model.Field.nativeKaratsuba r (Spec.Field.eadd lo hi))))
    (planarEmpty half)

def msgPlanar (f b : @& PlanarE) : E × E :=
  let pairs := min (planarSize f / 2) (planarSize b / 2)
  foldRange pairs (fun (u0, u2) i =>
    let f0 := planarGet f (2 * i)
    let f1 := planarGet f (2 * i + 1)
    let b0 := planarGet b (2 * i)
    let b1 := planarGet b (2 * i + 1)
    (Spec.Field.eadd u0 (Model.Field.nativeKaratsuba f0 b0),
     Spec.Field.eadd u2 (Model.Field.nativeKaratsuba (Spec.Field.eadd f0 f1) (Spec.Field.eadd b0 b1))))
    (Spec.Field.zero, Spec.Field.zero)

inductive Factor where
  | eq (p : E)
  | fixed (bit : Bool)
  deriving Inhabited

def factorEq (a b : Factor) : Bool :=
  match a, b with
  | .eq x, .eq y => eqE x y
  | .fixed x, .fixed y => x == y
  | _, _ => false

def factorsEq (xs ys : @& Array Factor) : Bool :=
  decide (xs.size = ys.size) &&
    foldRange xs.size (fun ok i =>
      ok && factorEq (xs.getD i (.fixed false)) (ys.getD i (.fixed false))) true

def factorAt (point : @& Array E) (offset b : Nat) : Factor :=
  if decide (b < point.size) then .eq (point.getD b Spec.Field.zero)
  else .fixed (Nat.testBit offset b)

def evalFactors (fs : @& Array Factor) : Array E :=
  fs.foldl (fun acc f =>
    match f with
    | .eq p =>
      let high := acc.map (fun v => Model.Field.nativeKaratsuba v p)
      acc.mapIdx (fun i v => Spec.Field.eadd v (high.getD i Spec.Field.zero)) ++ high
    | .fixed true => acc.map (fun _ => Spec.Field.zero) ++ acc
    | .fixed false => acc ++ acc.map (fun _ => Spec.Field.zero)) #[Spec.Field.one]

def topPointScale (point : @& Array E) (offset topStart : Nat) : E :=
  let bound := max topStart point.size
  if decide (offset >>> bound ≠ 0) then Spec.Field.zero
  else
    foldRange (point.size - topStart) (fun acc k =>
      Model.Field.nativeKaratsuba acc
        (Spec.Field.eadd Spec.Field.one (point.getD (topStart + k) Spec.Field.zero)))
      Spec.Field.one

structure PointPattern where
  lowFs : Array Factor
  lowTable : Array E
  claims : Array Nat
  active : Array Bool
  deriving Inhabited

structure RingTerm where
  first : Nat
  weights : Array E
  eLo : Array E
  eHi : Array E
  laneTable : Array E
  bitLut : Array E
  deriving Inhabited

inductive UnalignedKind where
  | point (scale : E) (offset : Nat) (eq : Array E)
  | ring (weights : Array E) (offset : Nat) (eq : Array E)
  deriving Inhabited

structure UnalignedTerm where
  termIdx : Nat
  laneIdx : Nat
  loX : Nat
  lenX : Nat
  kind : UnalignedKind
  deriving Inhabited

structure WeightTerms where
  laneVars : Nat
  lowVars : Nat
  nTerms : Nat
  gammas : Array (Array E)
  lows : Array (Array E)
  lanes : Array (Array E)
  patterns : Array PointPattern
  rings : Array RingTerm
  unaligned : Array UnalignedTerm
  ringStart : Nat
  deriving Inhabited

def lowVarsOf (laneVars : Nat) : Nat := min laneVars 10

def boolScale (poly : Array E) (c : E) : Array E :=
  let high := poly.map (fun v => Model.Field.nativeKaratsuba v c)
  poly.mapIdx (fun i v => Spec.Field.eadd v (high.getD i Spec.Field.zero)) ++ high

def fixedScale (poly : Array E) (bit : Bool) : Array E :=
  if bit then poly.map (fun _ => Spec.Field.zero) ++ poly
  else poly ++ poly.map (fun _ => Spec.Field.zero)

def extendPoint (point : Array E) (offset bits : Nat) : Array E :=
  (Array.range bits).foldl (fun acc b =>
    match point[b]? with
    | some p => boolScale acc p
    | none => fixedScale acc (Nat.testBit offset b)) #[Spec.Field.one]

def buildGroupLut8 (src : @& Array E) (base : Nat) : Array E :=
  foldRange 8 (fun tbl j =>
    let v := src.getD (base + j) Spec.Field.zero
    tbl ++ tbl.map (fun u => Spec.Field.eadd u v)) #[Spec.Field.zero]

def buildBitLut (eLo : @& Array E) : Array E :=
  let nGroups := (eLo.size + 7) / 8
  foldRange nGroups (fun acc g => acc ++ buildGroupLut8 eLo (8 * g))
    (Array.emptyWithCapacity (nGroups * 256))

def buildLinearLut (weights : @& Array E) : Array E :=
  foldRange 24 (fun acc g => acc ++ buildGroupLut8 weights (8 * g))
    (Array.emptyWithCapacity (24 * 256))

@[inline] def applyLinearLut (lut : @& Array E) (v : E) : E :=
  let w0 := v.c0
  let w1 := v.c1
  let w2 := v.c2
  let s0 := Spec.Field.eadd
    (Spec.Field.eadd
      (lut.getD ((w0 &&& 0xff).toNat) Spec.Field.zero)
      (lut.getD (256 + ((w0 >>> 8) &&& 0xff).toNat) Spec.Field.zero))
    (Spec.Field.eadd
      (lut.getD (512 + ((w0 >>> 16) &&& 0xff).toNat) Spec.Field.zero)
      (lut.getD (768 + ((w0 >>> 24) &&& 0xff).toNat) Spec.Field.zero))
  let s1 := Spec.Field.eadd
    (Spec.Field.eadd
      (lut.getD (1024 + ((w0 >>> 32) &&& 0xff).toNat) Spec.Field.zero)
      (lut.getD (1280 + ((w0 >>> 40) &&& 0xff).toNat) Spec.Field.zero))
    (Spec.Field.eadd
      (lut.getD (1536 + ((w0 >>> 48) &&& 0xff).toNat) Spec.Field.zero)
      (lut.getD (1792 + ((w0 >>> 56) &&& 0xff).toNat) Spec.Field.zero))
  let s2 := Spec.Field.eadd
    (Spec.Field.eadd
      (lut.getD (2048 + (w1 &&& 0xff).toNat) Spec.Field.zero)
      (lut.getD (2304 + ((w1 >>> 8) &&& 0xff).toNat) Spec.Field.zero))
    (Spec.Field.eadd
      (lut.getD (2560 + ((w1 >>> 16) &&& 0xff).toNat) Spec.Field.zero)
      (lut.getD (2816 + ((w1 >>> 24) &&& 0xff).toNat) Spec.Field.zero))
  let s3 := Spec.Field.eadd
    (Spec.Field.eadd
      (lut.getD (3072 + ((w1 >>> 32) &&& 0xff).toNat) Spec.Field.zero)
      (lut.getD (3328 + ((w1 >>> 40) &&& 0xff).toNat) Spec.Field.zero))
    (Spec.Field.eadd
      (lut.getD (3584 + ((w1 >>> 48) &&& 0xff).toNat) Spec.Field.zero)
      (lut.getD (3840 + ((w1 >>> 56) &&& 0xff).toNat) Spec.Field.zero))
  let s4 := Spec.Field.eadd
    (Spec.Field.eadd
      (lut.getD (4096 + (w2 &&& 0xff).toNat) Spec.Field.zero)
      (lut.getD (4352 + ((w2 >>> 8) &&& 0xff).toNat) Spec.Field.zero))
    (Spec.Field.eadd
      (lut.getD (4608 + ((w2 >>> 16) &&& 0xff).toNat) Spec.Field.zero)
      (lut.getD (4864 + ((w2 >>> 24) &&& 0xff).toNat) Spec.Field.zero))
  let s5 := Spec.Field.eadd
    (Spec.Field.eadd
      (lut.getD (5120 + ((w2 >>> 32) &&& 0xff).toNat) Spec.Field.zero)
      (lut.getD (5376 + ((w2 >>> 40) &&& 0xff).toNat) Spec.Field.zero))
    (Spec.Field.eadd
      (lut.getD (5632 + ((w2 >>> 48) &&& 0xff).toNat) Spec.Field.zero)
      (lut.getD (5888 + ((w2 >>> 56) &&& 0xff).toNat) Spec.Field.zero))
  Spec.Field.eadd (Spec.Field.eadd (Spec.Field.eadd s0 s1) (Spec.Field.eadd s2 s3))
    (Spec.Field.eadd s4 s5)

@[inline] def transpose8x8 (x : UInt64) : UInt64 :=
  let t1 := ((x >>> 7) ^^^ x) &&& (0x00aa00aa00aa00aa : UInt64)
  let x1 := x ^^^ t1 ^^^ (t1 <<< 7)
  let t2 := ((x1 >>> 14) ^^^ x1) &&& (0x0000cccc0000cccc : UInt64)
  let x2 := x1 ^^^ t2 ^^^ (t2 <<< 14)
  let t3 := ((x2 >>> 28) ^^^ x2) &&& (0x00000000f0f0f0f0 : UInt64)
  x2 ^^^ t3 ^^^ (t3 <<< 28)

@[inline] def packByteCol (w0 w1 w2 w3 w4 w5 w6 w7 : UInt64) (sh : UInt64) : UInt64 :=
  let m : UInt64 := 0xff
  ((w0 >>> sh) &&& m) |||
    (((w1 >>> sh) &&& m) <<< 8) |||
    (((w2 >>> sh) &&& m) <<< 16) |||
    (((w3 >>> sh) &&& m) <<< 24) |||
    (((w4 >>> sh) &&& m) <<< 32) |||
    (((w5 >>> sh) &&& m) <<< 40) |||
    (((w6 >>> sh) &&& m) <<< 48) |||
    (((w7 >>> sh) &&& m) <<< 56)

@[inline] def accumTransposedByte (lut : @& Array E) (lutBase bitBase : Nat)
    (tr : UInt64) (acc : Array E) : Array E :=
  let b0 := (tr &&& 0xff).toNat
  let b1 := ((tr >>> 8) &&& 0xff).toNat
  let b2 := ((tr >>> 16) &&& 0xff).toNat
  let b3 := ((tr >>> 24) &&& 0xff).toNat
  let b4 := ((tr >>> 32) &&& 0xff).toNat
  let b5 := ((tr >>> 40) &&& 0xff).toNat
  let b6 := ((tr >>> 48) &&& 0xff).toNat
  let b7 := ((tr >>> 56) &&& 0xff).toNat
  let acc := acc.setIfInBounds (bitBase + 0)
    (Spec.Field.eadd (acc.getD (bitBase + 0) Spec.Field.zero) (lut.getD (lutBase + b0) Spec.Field.zero))
  let acc := acc.setIfInBounds (bitBase + 1)
    (Spec.Field.eadd (acc.getD (bitBase + 1) Spec.Field.zero) (lut.getD (lutBase + b1) Spec.Field.zero))
  let acc := acc.setIfInBounds (bitBase + 2)
    (Spec.Field.eadd (acc.getD (bitBase + 2) Spec.Field.zero) (lut.getD (lutBase + b2) Spec.Field.zero))
  let acc := acc.setIfInBounds (bitBase + 3)
    (Spec.Field.eadd (acc.getD (bitBase + 3) Spec.Field.zero) (lut.getD (lutBase + b3) Spec.Field.zero))
  let acc := acc.setIfInBounds (bitBase + 4)
    (Spec.Field.eadd (acc.getD (bitBase + 4) Spec.Field.zero) (lut.getD (lutBase + b4) Spec.Field.zero))
  let acc := acc.setIfInBounds (bitBase + 5)
    (Spec.Field.eadd (acc.getD (bitBase + 5) Spec.Field.zero) (lut.getD (lutBase + b5) Spec.Field.zero))
  let acc := acc.setIfInBounds (bitBase + 6)
    (Spec.Field.eadd (acc.getD (bitBase + 6) Spec.Field.zero) (lut.getD (lutBase + b6) Spec.Field.zero))
  acc.setIfInBounds (bitBase + 7)
    (Spec.Field.eadd (acc.getD (bitBase + 7) Spec.Field.zero) (lut.getD (lutBase + b7) Spec.Field.zero))

def foldBlockBits (bytes : @& ByteArray) (wordBase lowN : Nat) (lut : @& Array E) : Array E :=
  let nGroups := lowN / 8
  let init := Array.replicate 64 Spec.Field.zero
  let out := foldRange nGroups (fun acc g =>
    let idx := wordBase + 8 * g
    let w0 := wordAt bytes (idx + 0)
    let w1 := wordAt bytes (idx + 1)
    let w2 := wordAt bytes (idx + 2)
    let w3 := wordAt bytes (idx + 3)
    let w4 := wordAt bytes (idx + 4)
    let w5 := wordAt bytes (idx + 5)
    let w6 := wordAt bytes (idx + 6)
    let w7 := wordAt bytes (idx + 7)
    let lutBase := g * 256
    foldRange 8 (fun acc B =>
      let sh := UInt64.ofNat (8 * B)
      let tr := transpose8x8 (packByteCol w0 w1 w2 w3 w4 w5 w6 w7 sh)
      accumTransposedByte lut lutBase (8 * B) tr acc) acc) init
  let remStart := nGroups * 8
  if decide (remStart = lowN) then out
  else
    foldRange (lowN - remStart) (fun acc r =>
      let w := wordAt bytes (wordBase + remStart + r)
      let lutBase := nGroups * 256
      foldRange 64 (fun acc b =>
        if decide (((w >>> UInt64.ofNat b) &&& 1) ≠ 0) then
          acc.setIfInBounds b
            (Spec.Field.eadd (acc.getD b Spec.Field.zero)
              (lut.getD (lutBase + (1 <<< r)) Spec.Field.zero))
        else acc) acc) out

def coordBasis (w : Nat) : E :=
  if decide (w < 64) then ⟨(1 : UInt64) <<< UInt64.ofNat w, 0, 0⟩
  else if decide (w < 128) then ⟨0, (1 : UInt64) <<< UInt64.ofNat (w - 64), 0⟩
  else ⟨0, 0, (1 : UInt64) <<< UInt64.ofNat (w - 128)⟩

def insertPattern (pats : Array PointPattern) (gammas : @& Array (Array E))
    (lowFs : Array Factor) (lowTable : Array E) (claimIdx nBlocks : Nat) : Array PointPattern :=
  let gamma := gammas.getD claimIdx #[]
  let found := foldRange pats.size (fun res i =>
    match res with
    | some _ => res
    | none =>
      if factorsEq (pats.getD i default).lowFs lowFs then some i else none) none
  match found with
  | some idx =>
    let pat := pats.getD idx default
    let active := foldRange nBlocks (fun act h =>
      act.setIfInBounds h (act.getD h false || !isZeroE (gamma.getD h Spec.Field.zero))) pat.active
    pats.setIfInBounds idx ⟨pat.lowFs, pat.lowTable, pat.claims.push claimIdx, active⟩
  | none =>
    let active := (Array.range nBlocks).map (fun h => !isZeroE (gamma.getD h Spec.Field.zero))
    pats.push ⟨lowFs, lowTable, #[claimIdx], active⟩

def overlappedLanes (nLanes laneBlock offset span : Nat) : Array Nat :=
  let nWords := nLanes * laneBlock
  if decide (span = 0 ∨ offset ≥ nWords) then #[]
  else
    let hi := min nWords (offset + span)
    let firstLane := offset / laneBlock
    let lastLane := (hi - 1) / laneBlock
    (Array.range (lastLane + 1 - firstLane)).map (fun k => firstLane + k)

def termsOf (stackLen laneVars : Nat) (lambda : E)
    (points : Array Spec.Pcs.StackOpen.StackClaim)
    (ring : Spec.Pcs.StackOpen.RingSwitchOpen)
    (ringWeights : Array (Array E)) : WeightTerms :=
  let lowVars := lowVarsOf laneVars
  let midVars := laneVars - lowVars
  let laneBlock := 1 <<< laneVars
  let nBlocks := 1 <<< midVars
  let nLanes := stackLen / laneBlock
  let laneBits := 6
  let topStart := laneVars + laneBits
  let allScales := powers lambda (ring.claims.size + points.size)
  let (gammas, lows, lanes, patterns, unaligned, nextIdx) :=
    foldRange points.size (fun (gs, ls, lns, pats, unal, curIdx) i =>
      match points[i]? with
      | some (.point offset low _) =>
        let scale := allScales.getD (ring.claims.size + i) Spec.Field.zero
        if Spec.Pcs.StackOpen.aligned offset low.size then
          let topS := Model.Field.nativeKaratsuba scale (topPointScale low offset topStart)
          let lowFs := (Array.range lowVars).map (factorAt low offset)
          let midFs := (Array.range midVars).map (fun k => factorAt low offset (lowVars + k))
          let laneFs := (Array.range laneBits).map (fun k => factorAt low offset (laneVars + k))
          let lowT := evalFactors lowFs
          let gammaT := evalFactors midFs
          let laneT := (evalFactors laneFs).map (Model.Field.nativeKaratsuba topS)
          let gs' := gs.push gammaT
          let ls' := ls.push lowT
          let lns' := lns.push laneT
          let pats' := insertPattern pats gs' lowFs lowT curIdx nBlocks
          (gs', ls', lns', pats', unal, curIdx + 1)
        else
          let eq := eqKernel low
          let touched := overlappedLanes nLanes laneBlock offset eq.size
          foldRange touched.size (fun (gs, ls, lns, pats, unal, tIdx) k =>
            let l0 := touched.getD k 0
            let lStart := l0 * laneBlock
            let gLo := max offset lStart
            let gHi := min stackLen (min (offset + eq.size) (lStart + laneBlock))
            let laneT := Array.replicate (1 <<< laneBits) Spec.Field.zero
            (gs.push #[], ls.push #[], lns.push laneT, pats,
             unal.push ⟨tIdx, l0, gLo - lStart, gHi - gLo, .point scale offset eq⟩, tIdx + 1))
            (gs, ls, lns, pats, unal, curIdx)
      | none => (gs, ls, lns, pats, unal, curIdx)) (#[], #[], #[], #[], #[], 0)
  let ringStart := nextIdx
  let (rings, unaligned, totalTerms) :=
    foldRange ring.claims.size (fun (rs, unal, curIdx) i =>
      let claim := ring.claims.getD i default
      let weights := ringWeights.getD i #[]
      let pt := claim.suffixPoint
      if Spec.Pcs.StackOpen.aligned ring.offset pt.size then
        let topS := topPointScale pt ring.offset topStart
        let lowFs := (Array.range lowVars).map (factorAt pt ring.offset)
        let midFs := (Array.range midVars).map (fun k => factorAt pt ring.offset (lowVars + k))
        let laneFs := (Array.range laneBits).map (fun k => factorAt pt ring.offset (laneVars + k))
        let eLo := evalFactors lowFs
        let eHi := evalFactors midFs
        let laneT := (evalFactors laneFs).map (Model.Field.nativeKaratsuba topS)
        let lut := buildBitLut eLo
        (rs.push ⟨curIdx, weights, eLo, eHi, laneT, lut⟩, unal, curIdx + 192)
      else
        let eq := eqKernel pt
        let touched := overlappedLanes nLanes laneBlock ring.offset eq.size
        let (unal', curIdx') := foldRange touched.size (fun (uAcc, tIdx) k =>
          let l0 := touched.getD k 0
          let lStart := l0 * laneBlock
          let gLo := max ring.offset lStart
          let gHi := min stackLen (min (ring.offset + eq.size) (lStart + laneBlock))
          (uAcc.push ⟨tIdx, l0, gLo - lStart, gHi - gLo, .ring weights ring.offset eq⟩, tIdx + 1))
          (unal, curIdx)
        (rs, unal', curIdx')) (#[], unaligned, nextIdx)
  let finalTerms := max 1 totalTerms
  ⟨laneVars, lowVars, finalTerms, gammas, lows, lanes, patterns, rings, unaligned, ringStart⟩

def dotBaseBlock (bytes : @& ByteArray) (wordBase lowN : Nat) (lowT : @& Array E) : E :=
  foldRange lowN (fun acc x =>
    let w := wordAt bytes (wordBase + x)
    if decide (w = 0) then acc
    else Spec.Field.eadd acc (RingSwitch.nativeMulBase (lowT.getD x Spec.Field.zero) w))
    Spec.Field.zero

def unalignedWeightAt (kind : @& UnalignedKind) (globalIdx : Nat) : E :=
  match kind with
  | .point scale offset eq =>
    if decide (offset ≤ globalIdx ∧ globalIdx < offset + eq.size) then
      Model.Field.nativeKaratsuba scale (eq.getD (globalIdx - offset) Spec.Field.zero)
    else Spec.Field.zero
  | .ring weights offset eq =>
    if decide (offset ≤ globalIdx ∧ globalIdx < offset + eq.size) then
      Spec.Pcs.Whir.applyLinearMap weights (eq.getD (globalIdx - offset) Spec.Field.zero)
    else Spec.Field.zero

def projectLane (bytes : @& ByteArray) (lane laneBlock : Nat) (terms : @& WeightTerms) : Array E :=
  let lowN := 1 <<< terms.lowVars
  let nBlocks := laneBlock / lowN
  let base := lane * laneBlock
  let row := Array.replicate terms.nTerms Spec.Field.zero
  let row := foldRange terms.patterns.size (fun row pIdx =>
    let pat := terms.patterns.getD pIdx default
    let qs := foldRange nBlocks (fun acc h =>
      if pat.active.getD h false then
        acc.push (dotBaseBlock bytes (base + h * lowN) lowN pat.lowTable)
      else acc.push Spec.Field.zero) (Array.emptyWithCapacity nBlocks)
    foldRange pat.claims.size (fun row k =>
      let c := pat.claims.getD k 0
      let gamma := terms.gammas.getD c #[]
      let total := foldRange nBlocks (fun acc h =>
        let g := gamma.getD h Spec.Field.zero
        if isZeroE g then acc
        else Spec.Field.eadd acc (Model.Field.nativeKaratsuba g (qs.getD h Spec.Field.zero)))
        Spec.Field.zero
      row.setIfInBounds c total) row) row
  let row := foldRange terms.rings.size (fun row rIdx =>
    let rt := terms.rings.getD rIdx default
    let sigma := foldRange nBlocks (fun sig h =>
      let eh := rt.eHi.getD h Spec.Field.zero
      if isZeroE eh then sig
      else
        let folded := foldBlockBits bytes (base + h * lowN) lowN rt.bitLut
        foldRange 64 (fun sig b =>
          let fb := folded.getD b Spec.Field.zero
          if isZeroE fb then sig
          else
            sig.setIfInBounds b
              (Spec.Field.eadd (sig.getD b Spec.Field.zero) (Model.Field.nativeKaratsuba eh fb))) sig)
      (Array.replicate 64 Spec.Field.zero)
    let cols := RingSwitch.transposeSlices sigma
    foldRange 192 (fun row w =>
      row.setIfInBounds (rt.first + w) (Spec.Field.embed (cols.getD w 0))) row) row
  foldRange terms.unaligned.size (fun row uIdx =>
    let ut := terms.unaligned.getD uIdx default
    let refBase := ut.laneIdx * laneBlock
    let v := foldRange ut.lenX (fun acc k =>
      let x := ut.loX + k
      let w := wordAt bytes (base + x)
      if decide (w = 0) then acc
      else Spec.Field.eadd acc (RingSwitch.nativeMulBase (unalignedWeightAt ut.kind (refBase + x)) w))
      Spec.Field.zero
    row.setIfInBounds ut.termIdx v) row

def buildLaneMatrixA (nLanes : Nat) (terms : @& WeightTerms) : Array E :=
  foldRange nLanes (fun acc lane =>
    let row := Array.replicate terms.nTerms Spec.Field.zero
    let row := foldRange terms.lanes.size (fun row c =>
      row.setIfInBounds c ((terms.lanes.getD c #[]).getD lane Spec.Field.zero)) row
    let row := foldRange terms.rings.size (fun row rIdx =>
      let rt := terms.rings.getD rIdx default
      let s := rt.laneTable.getD lane Spec.Field.zero
      if isZeroE s then row
      else
        foldRange 192 (fun row w =>
          let img := Spec.Pcs.Whir.applyLinearMap rt.weights
            (Model.Field.nativeKaratsuba s (coordBasis w))
          row.setIfInBounds (rt.first + w) img) row) row
    let row := foldRange terms.unaligned.size (fun row uIdx =>
      let ut := terms.unaligned.getD uIdx default
      let v := if decide (ut.laneIdx = lane) then Spec.Field.one else Spec.Field.zero
      row.setIfInBounds ut.termIdx v) row
    acc ++ row) (Array.emptyWithCapacity (nLanes * terms.nTerms))

def projectStack (bytes : ByteArray) (laneBlock : Nat) (terms : WeightTerms) : Array E :=
  let nLanes := (bytes.size / 8) / laneBlock
  foldRange nLanes (fun acc lane => acc ++ projectLane bytes lane laneBlock terms)
    (Array.emptyWithCapacity (nLanes * terms.nTerms))

structure LiftTables where
  patCoefs : Array (Array E)
  ringLuts : Array (Array E)
  unalignedCoefs : Array E
  deriving Inhabited

def prepareLift (terms : @& WeightTerms) (a : @& Array E) (nBlocks : Nat) : LiftTables :=
  let patCoefs := terms.patterns.map fun pat =>
    (Array.range nBlocks).map fun h =>
      foldRange pat.claims.size (fun acc k =>
        let c := pat.claims.getD k 0
        let ac := a.getD c Spec.Field.zero
        let gh := (terms.gammas.getD c #[]).getD h Spec.Field.zero
        if isZeroE ac || isZeroE gh then acc
        else Spec.Field.eadd acc (Model.Field.nativeKaratsuba ac gh)) Spec.Field.zero
  let ringLuts := terms.rings.map fun rt =>
    buildLinearLut (a.extract rt.first (rt.first + 192))
  let unalignedCoefs := terms.unaligned.map fun ut => a.getD ut.termIdx Spec.Field.zero
  ⟨patCoefs, ringLuts, unalignedCoefs⟩

def liftBlockWith (terms : @& WeightTerms) (lt : @& LiftTables) (laneBlock h : Nat) : Array E :=
  let lowN := 1 <<< terms.lowVars
  let out := Array.replicate lowN Spec.Field.zero
  let out := foldRange terms.patterns.size (fun out pIdx =>
    let coef := (lt.patCoefs.getD pIdx #[]).getD h Spec.Field.zero
    if isZeroE coef then out
    else
      let lowT := (terms.patterns.getD pIdx default).lowTable
      foldRange lowN (fun out x =>
        out.setIfInBounds x
          (Spec.Field.eadd (out.getD x Spec.Field.zero)
            (Model.Field.nativeKaratsuba coef (lowT.getD x Spec.Field.zero)))) out) out
  let out := foldRange terms.rings.size (fun out rIdx =>
    let rt := terms.rings.getD rIdx default
    let eh := rt.eHi.getD h Spec.Field.zero
    if isZeroE eh then out
    else
      let lut := lt.ringLuts.getD rIdx #[]
      foldRange lowN (fun out x =>
        let prod := Model.Field.nativeKaratsuba eh (rt.eLo.getD x Spec.Field.zero)
        if isZeroE prod then out
        else
          out.setIfInBounds x
            (Spec.Field.eadd (out.getD x Spec.Field.zero) (applyLinearLut lut prod))) out) out
  foldRange terms.unaligned.size (fun out uIdx =>
    let coef := lt.unalignedCoefs.getD uIdx Spec.Field.zero
    if isZeroE coef then out
    else
      let ut := terms.unaligned.getD uIdx default
      let blockStart := h * lowN
      let refBase := ut.laneIdx * laneBlock
      let lo := max blockStart ut.loX
      let hi := min (blockStart + lowN) (ut.loX + ut.lenX)
      if decide (hi ≤ lo) then out
      else
        foldRange (hi - lo) (fun out k =>
          let y := lo + k
          let x := y - blockStart
          let w := unalignedWeightAt ut.kind (refBase + y)
          if isZeroE w then out
          else
            out.setIfInBounds x
              (Spec.Field.eadd (out.getD x Spec.Field.zero)
                (Model.Field.nativeKaratsuba coef w))) out) out

def liftBlock (terms : WeightTerms) (a : Array E) (h : Nat) : Array E :=
  let lowN := 1 <<< terms.lowVars
  let laneBlock := 1 <<< terms.laneVars
  let lt := prepareLift terms a (laneBlock / lowN)
  liftBlockWith terms lt laneBlock h

def foldWitnessAndLift (bytes : @& ByteArray) (nLanes laneBlock : Nat)
    (laneWeights : @& Array E) (terms : @& WeightTerms) (a : @& Array E) :
    PlanarE × PlanarE × (E × E) :=
  let lowN := 1 <<< terms.lowVars
  let nBlocks := laneBlock / lowN
  let lt := prepareLift terms a nBlocks
  foldRange nBlocks (fun (fAcc, bAcc, u0, u2) h =>
    let bBlk := liftBlockWith terms lt laneBlock h
    let fBlk := foldRange lowN (fun acc x =>
      let idx := h * lowN + x
      let sum := foldRange nLanes (fun s l =>
        let w := wordAt bytes (l * laneBlock + idx)
        if decide (w = 0) then s
        else Spec.Field.eadd s (RingSwitch.nativeMulBase (laneWeights.getD l Spec.Field.zero) w))
        Spec.Field.zero
      acc.push sum) (Array.emptyWithCapacity lowN)
    let pairs := lowN / 2
    let (u0', u2') := foldRange pairs (fun (u0, u2) i =>
      let f0 := fBlk.getD (2 * i) Spec.Field.zero
      let f1 := fBlk.getD (2 * i + 1) Spec.Field.zero
      let b0 := bBlk.getD (2 * i) Spec.Field.zero
      let b1 := bBlk.getD (2 * i + 1) Spec.Field.zero
      (Spec.Field.eadd u0 (Model.Field.nativeKaratsuba f0 b0),
       Spec.Field.eadd u2 (Model.Field.nativeKaratsuba (Spec.Field.eadd f0 f1) (Spec.Field.eadd b0 b1))))
      (u0, u2)
    let fAcc' := foldRange lowN (fun p x => planarPush p (fBlk.getD x Spec.Field.zero)) fAcc
    let bAcc' := foldRange lowN (fun p x => planarPush p (bBlk.getD x Spec.Field.zero)) bAcc
    (fAcc', bAcc', u0', u2'))
    (planarEmpty laneBlock, planarEmpty laneBlock, Spec.Field.zero, Spec.Field.zero)

@[inline] def firstCosetWordBytes (bytes : @& ByteArray) (lanes width rows rowIndex col : Nat) : K :=
  if decide (col + lanes < width) then 0
  else wordAt bytes ((width - 1 - col) * rows + rowIndex)

def firstCosetFromBytes (bytes : @& ByteArray) (lanes nVecs logRows : Nat) : Array Vec8 :=
  let width := 8 * nVecs
  let rows := 1 <<< logRows
  foldRange rows (fun out curRow =>
    foldRange nVecs (fun out curV =>
      let base := 8 * curV
      out.push
        ⟨firstCosetWordBytes bytes lanes width rows curRow (base + 0),
         firstCosetWordBytes bytes lanes width rows curRow (base + 1),
         firstCosetWordBytes bytes lanes width rows curRow (base + 2),
         firstCosetWordBytes bytes lanes width rows curRow (base + 3),
         firstCosetWordBytes bytes lanes width rows curRow (base + 4),
         firstCosetWordBytes bytes lanes width rows curRow (base + 5),
         firstCosetWordBytes bytes lanes width rows curRow (base + 6),
         firstCosetWordBytes bytes lanes width rows curRow (base + 7)⟩) out)
    (Array.emptyWithCapacity (rows * nVecs))

def l0CosetRoots (bytes : ByteArray) (lanes logRows logInvRate : Nat) : Array Digest32 :=
  let nVecs := Spec.Pcs.Commit.rowWords lanes / 8
  let table := Model.Pcs.Ntt.evals (logRows + logInvRate)
  let st1 := Model.Pcs.Commit.zeroPrefixState 1
  let st2 := Model.Pcs.Commit.zeroPrefixState 2
  let st3 := Model.Pcs.Commit.zeroPrefixState 3
  foldRange (1 <<< logInvRate) (fun acc curC =>
    let first := firstCosetFromBytes bytes lanes nVecs logRows
    let encoded := Model.Pcs.Ntt.encodeCosetVec8 table first nVecs logRows logInvRate curC
    acc.push (Model.Pcs.Commit.subtreeRootBuf st1 st2 st3 encoded nVecs logRows 0))
    (Array.emptyWithCapacity (1 <<< logInvRate))

def l0Root (bytes : ByteArray) (lanes logRows logInvRate : Nat) : ByteArray :=
  let roots := l0CosetRoots bytes lanes logRows logInvRate
  Digest32.toBytesFast (Model.Pcs.Commit.subtreeRoot (fun i => roots.getD i default) logInvRate 0)

def extractL0Row (encoded : @& Array Vec8) (lanes width nVecs localRow : Nat) : Array K :=
  let start := localRow * nVecs
  foldRange lanes (fun acc j =>
    let col := width - lanes + j
    let v := encoded.getD (start + col / 8) default
    acc.push (v.lane (col % 8))) (Array.emptyWithCapacity lanes)

def l0Row (bytes : ByteArray) (lanes logRows logInvRate pos : Nat) : Array K :=
  let width := Spec.Pcs.Commit.rowWords lanes
  let nVecs := width / 8
  let rows := 1 <<< logRows
  let coset := pos / rows
  let localRow := pos % rows
  let table := Model.Pcs.Ntt.evals (logRows + logInvRate)
  let first := firstCosetFromBytes bytes lanes nVecs logRows
  let encoded := Model.Pcs.Ntt.encodeCosetVec8 table first nVecs logRows logInvRate coset
  extractL0Row encoded lanes width nVecs localRow

def advanceCursor (indices : @& Array Nat) (bound cur0 : Nat) : Nat :=
  Fin.foldl (indices.size - cur0) (fun cur _ =>
    if decide (cur < indices.size) && decide (indices.getD cur 0 < bound) then cur + 1
    else cur) cur0

def collectLocalActive (indices : @& Array Nat) (base start stop : Nat) : List Nat :=
  (Array.range (stop - start)).toList.map (fun k => indices.getD (start + k) 0 - base)

def streamCosetsOpen (nCosets logRows subK blockLog : Nat) (indices : @& Array Nat)
    (encodeCoset : Nat → Array Vec8)
    (extractRow : Array Vec8 → Nat → Array K)
    (leafAt : Array Vec8 → Nat → Digest32)
    (fastSubRoot : Array Vec8 → Nat → Nat → Digest32) :
    Option Spec.Merkle.PrunedMerklePaths := do
  let rowsPerCoset := 1 <<< logRows
  let subSize := 1 <<< subK
  let subsPerCoset := 1 <<< (logRows - subK)
  let totalSubs := 1 <<< (blockLog - subK)
  let initLow := Array.replicate subK (#[] : Array Digest32)
  let (openedRows, lowSibs, topActive, subRoots, _) ←
    (Array.range nCosets).foldlM
      (fun (opRows, lowAcc, topAct, roots, qCur) curC => do
        let cosetBase := curC * rowsPerCoset
        let cosetEnd := cosetBase + rowsPerCoset
        let encoded := encodeCoset curC
        let cosetStop := advanceCursor indices cosetEnd qCur
        let opRows := foldRange (cosetStop - qCur) (fun acc k =>
          let gIdx := indices.getD (qCur + k) 0
          acc.push (extractRow encoded (gIdx - cosetBase))) opRows
        let (lowAcc, topAct, roots, qNext) ←
          (Array.range subsPerCoset).foldlM
            (fun (lSibs, tAct, rAcc, cur) m => do
              let subGlobalBase := cosetBase + (m <<< subK)
              let subGlobalEnd := subGlobalBase + subSize
              let nextCur := advanceCursor indices subGlobalEnd cur
              if decide (cur = nextCur) then
                let r := fastSubRoot encoded subK (m <<< subK)
                some (lSibs, tAct, rAcc.push r, cur)
              else
                let leaves := foldRange subSize (fun acc j =>
                  acc.push (leafAt encoded ((m <<< subK) + j))) (Array.emptyWithCapacity subSize)
                let subTree ← Model.Merkle.buildFlat subK leaves
                let locAct := collectLocalActive indices subGlobalBase cur nextCur
                let (_, perLvl) := Model.Merkle.flatLevelsSiblings subTree locAct
                let lSibs := foldRange subK (fun ls lvl =>
                  ls.setIfInBounds lvl ((ls.getD lvl #[]) ++ (perLvl.getD lvl #[]))) lSibs
                let r := Model.Merkle.flatRoot subTree
                some (lSibs, tAct.push (curC * subsPerCoset + m), rAcc.push r, nextCur))
            (lowAcc, topAct, roots, qCur)
        some (opRows, lowAcc, topAct, roots, qNext))
      (Array.emptyWithCapacity indices.size, initLow, (#[] : Array Nat),
       Array.emptyWithCapacity totalSubs, 0)
  let topTree ← Model.Merkle.buildFlat (blockLog - subK) subRoots
  let topSibs := Model.Merkle.flatSiblings topTree topActive.toList
  let lowFlat := foldRange subK (fun acc lvl => acc ++ (lowSibs.getD lvl #[])) #[]
  let allSibs := (lowFlat ++ topSibs).map Digest32.toSpecDigest
  some ⟨openedRows, allSibs⟩

def openL0Cosets (bytes : @& ByteArray) (lanes logRows logInvRate : Nat)
    (queries : @& Array Nat) : Option Spec.Merkle.PrunedMerklePaths := do
  let blockLog := logRows + logInvRate
  let indices := Spec.Merkle.sortedUnique queries
  if !Spec.Merkle.validIndices blockLog indices then none
  else
    let width := Spec.Pcs.Commit.rowWords lanes
    let nVecs := width / 8
    let table := Model.Pcs.Ntt.evals blockLog
    let st1 := Model.Pcs.Commit.zeroPrefixState 1
    let st2 := Model.Pcs.Commit.zeroPrefixState 2
    let st3 := Model.Pcs.Commit.zeroPrefixState 3
    let subK := min logRows 10
    streamCosetsOpen (1 <<< logInvRate) logRows subK blockLog indices
      (fun curC =>
        let first := firstCosetFromBytes bytes lanes nVecs logRows
        Model.Pcs.Ntt.encodeCosetVec8 table first nVecs logRows logInvRate curC)
      (fun encoded loc => extractL0Row encoded lanes width nVecs loc)
      (fun encoded loc => Model.Pcs.Commit.hashLeafVec8From st1 st2 st3 encoded nVecs loc)
      (fun encoded k base => Model.Pcs.Commit.subtreeRootBuf st1 st2 st3 encoded nVecs k base)

@[inline] def extFirstWord (poly : @& PlanarE) (interleaved width rowIndex col : Nat) : K :=
  if decide (col ≥ width) then 0
  else
    let elemIdx := rowIndex * interleaved + col / 3
    let limb := col % 3
    if decide (limb = 0) then wordAt poly.c0 elemIdx
    else if decide (limb = 1) then wordAt poly.c1 elemIdx
    else wordAt poly.c2 elemIdx

def extFirstCoset (poly : @& PlanarE) (logRows logNumInterleaved : Nat) : Array Vec8 :=
  let interleaved := 1 <<< logNumInterleaved
  let width := 3 * interleaved
  let nVecs := (width + 7) / 8
  let rows := 1 <<< logRows
  foldRange rows (fun out curRow =>
    foldRange nVecs (fun out curV =>
      let base := 8 * curV
      out.push
        ⟨extFirstWord poly interleaved width curRow (base + 0),
         extFirstWord poly interleaved width curRow (base + 1),
         extFirstWord poly interleaved width curRow (base + 2),
         extFirstWord poly interleaved width curRow (base + 3),
         extFirstWord poly interleaved width curRow (base + 4),
         extFirstWord poly interleaved width curRow (base + 5),
         extFirstWord poly interleaved width curRow (base + 6),
         extFirstWord poly interleaved width curRow (base + 7)⟩) out)
    (Array.emptyWithCapacity (rows * nVecs))

def extractExtRow (encoded : @& Array Vec8) (width nVecs localRow : Nat) : Array K :=
  let start := localRow * nVecs
  foldRange width (fun acc col =>
    let v := encoded.getD (start + col / 8) default
    acc.push (v.lane (col % 8))) (Array.emptyWithCapacity width)

def hashWordsDigest32 (words : @& Array UInt64) : Digest32 :=
  let nFull := words.size / 17
  let st := foldRange nFull (fun st blk =>
    let b := blk * 17
    Model.Pcs.Commit.absorbWords17 st
      (words.getD (b + 0) 0) (words.getD (b + 1) 0) (words.getD (b + 2) 0)
      (words.getD (b + 3) 0) (words.getD (b + 4) 0) (words.getD (b + 5) 0)
      (words.getD (b + 6) 0) (words.getD (b + 7) 0) (words.getD (b + 8) 0)
      (words.getD (b + 9) 0) (words.getD (b + 10) 0) (words.getD (b + 11) 0)
      (words.getD (b + 12) 0) (words.getD (b + 13) 0) (words.getD (b + 14) 0)
      (words.getD (b + 15) 0) (words.getD (b + 16) 0)) Model.Layout.zeroState25
  let rem := words.size % 17
  let base := nFull * 17
  let tail := (Array.range 17).map fun i =>
    let v :=
      if decide (i < rem) then words.getD (base + i) 0
      else if decide (i = rem) then (1 : UInt64)
      else 0
    if decide (i = 16) then v ^^^ (0x8000000000000000 : UInt64) else v
  let st := Model.Pcs.Commit.absorbWords17 st
    (tail.getD 0 0) (tail.getD 1 0) (tail.getD 2 0) (tail.getD 3 0)
    (tail.getD 4 0) (tail.getD 5 0) (tail.getD 6 0) (tail.getD 7 0)
    (tail.getD 8 0) (tail.getD 9 0) (tail.getD 10 0) (tail.getD 11 0)
    (tail.getD 12 0) (tail.getD 13 0) (tail.getD 14 0) (tail.getD 15 0)
    (tail.getD 16 0)
  ⟨st.a00, st.a01, st.a02, st.a03⟩

def hashLeafExtVec8 (encoded : @& Array Vec8) (width nVecs localRow : Nat) : Digest32 :=
  if decide (width = 48 ∧ nVecs = 6) then
    let b := localRow * 6
    let v0 := encoded.getD (b + 0) default
    let v1 := encoded.getD (b + 1) default
    let v2 := encoded.getD (b + 2) default
    let v3 := encoded.getD (b + 3) default
    let v4 := encoded.getD (b + 4) default
    let v5 := encoded.getD (b + 5) default
    let st := Model.Pcs.Commit.absorbWords17 Model.Layout.zeroState25
      v0.w0 v0.w1 v0.w2 v0.w3 v0.w4 v0.w5 v0.w6 v0.w7
      v1.w0 v1.w1 v1.w2 v1.w3 v1.w4 v1.w5 v1.w6 v1.w7 v2.w0
    let st := Model.Pcs.Commit.absorbWords17 st
      v2.w1 v2.w2 v2.w3 v2.w4 v2.w5 v2.w6 v2.w7
      v3.w0 v3.w1 v3.w2 v3.w3 v3.w4 v3.w5 v3.w6 v3.w7 v4.w0 v4.w1
    let st := Model.Pcs.Commit.absorbWords17 st
      v4.w2 v4.w3 v4.w4 v4.w5 v4.w6 v4.w7
      v5.w0 v5.w1 v5.w2 v5.w3 v5.w4 v5.w5 v5.w6 v5.w7
      1 0 (0x8000000000000000 : UInt64)
    ⟨st.a00, st.a01, st.a02, st.a03⟩
  else
    hashWordsDigest32 (extractExtRow encoded width nVecs localRow)

def subtreeRootExtVec8 (encoded : Array Vec8) (width nVecs k : Nat) : Nat → Digest32 :=
  Nat.rec
    (fun idx => hashLeafExtVec8 encoded width nVecs idx)
    (fun d rec base =>
      Digest32.hashPairFlat (rec base) (rec (base + (1 <<< d))))
    k

structure ExtPrepared where
  first : Array Vec8
  logRows : Nat
  logNumInterleaved : Nat
  logInvRate : Nat
  deriving Inhabited

def addRootDigest32 (s : Spec.Transcript.ProverState) (d : Digest32) : Spec.Transcript.ProverState :=
  Spec.Transcript.addScalar (Spec.Transcript.addScalar s ⟨d.lo0, d.lo1, 0⟩) ⟨d.hi0, d.hi1, 0⟩

def putPhaseBytesFast (phase : @& Spec.Merkle.PrunedMerklePaths) : ByteArray :=
  let estWords := 2 + phase.rows.size * 65 + phase.siblings.size * 4
  let init := Model.Witness.pushU64LE (ByteArray.emptyWithCapacity (8 * estWords))
    (UInt64.ofNat phase.rows.size)
  let b := phase.rows.foldl (fun b row =>
    row.foldl Model.Witness.pushU64LE
      (Model.Witness.pushU64LE b (UInt64.ofNat row.size))) init
  let b := Model.Witness.pushU64LE b (UInt64.ofNat phase.siblings.size)
  phase.siblings.foldl (fun b d =>
    foldRange 32 (fun b i => b.push (d[i]?.getD 0)) b) b

def hintPhaseFast (s : Spec.Transcript.ProverState)
    (phase : @& Spec.Merkle.PrunedMerklePaths) : Spec.Transcript.ProverState :=
  Spec.Transcript.hintMerkle s (putPhaseBytesFast phase)

def commitExtPlanar (poly : @& PlanarE) (logRows logNumInterleaved logInvRate : Nat) :
    ExtPrepared × Digest32 :=
  let width := 3 * (1 <<< logNumInterleaved)
  let nVecs := (width + 7) / 8
  let first := extFirstCoset poly logRows logNumInterleaved
  let table := Model.Pcs.Ntt.evals (logRows + logInvRate)
  let cosetRoots := foldRange (1 <<< logInvRate) (fun acc curC =>
    let encoded := Model.Pcs.Ntt.encodeCosetVec8 table first nVecs logRows logInvRate curC
    acc.push (subtreeRootExtVec8 encoded width nVecs logRows 0))
    (Array.emptyWithCapacity (1 <<< logInvRate))
  let root := Model.Pcs.Commit.subtreeRoot (fun i => cosetRoots.getD i default) logInvRate 0
  (⟨first, logRows, logNumInterleaved, logInvRate⟩, root)

def openExtCosets (prep : @& ExtPrepared) (queries : @& Array Nat) :
    Option Spec.Merkle.PrunedMerklePaths := do
  let logRows := prep.logRows
  let logInvRate := prep.logInvRate
  let blockLog := logRows + logInvRate
  let indices := Spec.Merkle.sortedUnique queries
  if !Spec.Merkle.validIndices blockLog indices then none
  else
    let width := 3 * (1 <<< prep.logNumInterleaved)
    let nVecs := (width + 7) / 8
    let table := Model.Pcs.Ntt.evals blockLog
    let subK := min logRows 10
    streamCosetsOpen (1 <<< logInvRate) logRows subK blockLog indices
      (fun curC =>
        Model.Pcs.Ntt.encodeCosetVec8 table prep.first nVecs logRows logInvRate curC)
      (fun encoded loc => extractExtRow encoded width nVecs loc)
      (fun encoded loc => hashLeafExtVec8 encoded width nVecs loc)
      (fun encoded k base => subtreeRootExtVec8 encoded width nVecs k base)

def openQueriesFlat (rowsAt : Nat → Array K) (nRows : Nat) (queries : Array Nat)
    (depth leafWords : Nat) : Option Spec.Merkle.PrunedMerklePaths := do
  let indices := Spec.Merkle.sortedUnique queries
  if !Spec.Merkle.validIndices depth indices then none
  else if decide (nRows ≠ 1 <<< depth) then none
  else
    let leaves := foldRange nRows (fun acc i =>
      let row := rowsAt i
      let padded := Array.replicate (leafWords - row.size) 0 ++ row
      acc.push (hashWordsDigest32 padded))
      (Array.emptyWithCapacity nRows)
    let tree ← Model.Merkle.buildFlat depth leaves
    let sibs := (Model.Merkle.flatSiblings tree indices.toList).map Digest32.toSpecDigest
    let opened := indices.map rowsAt
    some ⟨opened, sibs⟩

def bsearchIdx (xs : @& Array Nat) (target : Nat) : Nat :=
  let (lo, _) := Fin.foldl xs.size (fun (lo, hi) _ =>
    if decide (lo ≥ hi) then (lo, hi)
    else
      let mid := (lo + hi) / 2
      let v := xs.getD mid 0
      if decide (v = target) then (mid, mid)
      else if decide (v < target) then (mid + 1, hi)
      else (lo, mid)) (0, xs.size)
  lo

def enforcedSumPhase (level : Nat) (indices : @& Array Nat) (openedRows : @& Array (Array K))
    (queries : @& Array Nat) (laneFolds weights : @& Array E) : E :=
  let kernel := eqKernel laneFolds
  let values := queries.map fun q =>
    let pos := bsearchIdx indices q
    let row := openedRows.getD pos #[]
    if decide (level = 0) then baseRowDot row kernel else rowDot row kernel
  dot values weights

def introduceOodPlanar (f : @& PlanarE) (s : Spec.Transcript.ProverState) (nVars : Nat) :
    (Array E × E × Array E) × Spec.Transcript.ProverState :=
  let (z, s) := Spec.Pcs.Whir.proverSamples s nVars
  if decide (nVars = 0) then
    let val := if decide (planarSize f = 1) then planarGet f 0 else Spec.Field.zero
    let s := Spec.Transcript.addScalar s val
    let (quad, s) := Spec.Pcs.Whir.sendRound s val Spec.Field.zero Spec.Field.zero
    ((z, val, quad), s)
  else
    let loVars := min nVars 10
    let eqLo := eqTable (z.extract 0 loVars)
    let eqHi := eqTable (z.extract loVars nVars)
    let loPairs := (1 <<< loVars) / 2
    let (u0, u2, value) := foldRange eqHi.size (fun (u0, u2, val) h =>
      let eh := eqHi.getD h Spec.Field.zero
      let base := h * (1 <<< loVars)
      foldRange loPairs (fun (u0, u2, val) i =>
        let f0 := planarGet f (base + 2 * i)
        let f1 := planarGet f (base + 2 * i + 1)
        let b0 := Model.Field.nativeKaratsuba eh (eqLo.getD (2 * i) Spec.Field.zero)
        let b1 := Model.Field.nativeKaratsuba eh (eqLo.getD (2 * i + 1) Spec.Field.zero)
        let p0 := Model.Field.nativeKaratsuba f0 b0
        let p1 := Model.Field.nativeKaratsuba f1 b1
        let pSum := Model.Field.nativeKaratsuba (Spec.Field.eadd f0 f1) (Spec.Field.eadd b0 b1)
        (Spec.Field.eadd u0 p0,
         Spec.Field.eadd u2 pSum,
         Spec.Field.eadd val (Spec.Field.eadd p0 p1))) (u0, u2, val))
      (Spec.Field.zero, Spec.Field.zero, Spec.Field.zero)
    let s := Spec.Transcript.addScalar s value
    let (quad, s) := Spec.Pcs.Whir.sendRound s value u0 u2
    ((z, value, quad), s)

def transposedLayerCoset (table : @& Array K) (buf : Array E)
    (messageLog rate coset step : Nat) : Array E :=
  let layer := rate + step
  let logD := messageLog + rate
  let localBlocks := 1 <<< step
  let half := 1 <<< (messageLog - step - 1)
  let values := Model.Pcs.Ntt.rowFromEvals table logD (logD - layer - 1)
  let blockBase := coset <<< step
  foldRange localBlocks (fun buf curBlock =>
    let t := Model.Pcs.Ntt.twiddleFromRow values (blockBase + curBlock)
    let blockRowBase := curBlock * (2 * half)
    foldRange half (fun buf curRow =>
      let topIdx := blockRowBase + curRow
      let botIdx := topIdx + half
      let topV := buf.getD topIdx Spec.Field.zero
      let botV := buf.getD botIdx Spec.Field.zero
      let sumV := Spec.Field.eadd topV botV
      let botOut :=
        if decide (t = 0) then botV
        else Spec.Field.eadd botV (RingSwitch.nativeMulBase sumV t)
      (buf.setIfInBounds topIdx sumV).setIfInBounds botIdx botOut) buf) buf

def addArrayToPlanar (acc : @& PlanarE) (buf : @& Array E) : PlanarE :=
  let n := buf.size
  if decide (planarSize acc = 0) then planarOf buf
  else
    foldRange n (fun out i =>
      planarPush out (Spec.Field.eadd (planarGet acc i) (buf.getD i Spec.Field.zero)))
      (planarEmpty n)

def inducedBasisPlanar (messageLog rate : Nat) (queries : @& Array Nat)
    (weights : @& Array E) : PlanarE :=
  let n := min queries.size weights.size
  if decide (messageLog = 0) then
    let total := foldRange n (fun acc i =>
      Spec.Field.eadd acc (weights.getD i Spec.Field.zero)) Spec.Field.zero
    planarOf #[total]
  else
    let rows := 1 <<< messageLog
    let logD := messageLog + rate
    let table := Model.Pcs.Ntt.evals logD
    let qSlice := queries.extract 0 n
    let activeCosets := Spec.Merkle.sortedUnique (qSlice.map (fun q => q >>> messageLog))
    let built := foldRange activeCosets.size (fun acc cIdx =>
      let curC := activeCosets.getD cIdx 0
      let cosetBase := curC * rows
      let cosetEnd := cosetBase + rows
      let buf := foldRange n (fun b i =>
        let q := queries.getD i 0
        if decide (cosetBase ≤ q ∧ q < cosetEnd) then
          let loc := q - cosetBase
          b.setIfInBounds loc
            (Spec.Field.eadd (b.getD loc Spec.Field.zero) (weights.getD i Spec.Field.zero))
        else b) (Array.replicate rows Spec.Field.zero)
      let buf := foldRange messageLog (fun b rev =>
        let step := messageLog - 1 - rev
        transposedLayerCoset table b messageLog rate curC step) buf
      addArrayToPlanar acc buf) (planarEmpty 0)
    if decide (planarSize built = 0) then
      foldRange rows (fun p _ => planarPush p Spec.Field.zero) (planarEmpty rows)
    else built

def glueBasisPlanar (basis : @& PlanarE) (oodPoint? : Option (Array E))
    (sOod sInd : E) (basisI : @& PlanarE) : PlanarE :=
  let n := planarSize basis
  match oodPoint? with
  | none =>
    foldRange n (fun out i =>
      let v := Spec.Field.eadd (planarGet basis i)
        (Model.Field.nativeKaratsuba sInd (planarGet basisI i))
      planarPush out v) (planarEmpty n)
  | some z =>
    if decide (z.size = 0) then
      foldRange n (fun out i =>
        let v := Spec.Field.eadd (planarGet basis i)
          (Spec.Field.eadd sOod (Model.Field.nativeKaratsuba sInd (planarGet basisI i)))
        planarPush out v) (planarEmpty n)
    else
      let loVars := min z.size 10
      let eqLo := eqTable (z.extract 0 loVars)
      let eqHi := (eqTable (z.extract loVars z.size)).map (Model.Field.nativeKaratsuba sOod)
      let loN := 1 <<< loVars
      foldRange eqHi.size (fun out h =>
        let eh := eqHi.getD h Spec.Field.zero
        let base := h * loN
        foldRange loN (fun out x =>
          let idx := base + x
          let oodV := Model.Field.nativeKaratsuba eh (eqLo.getD x Spec.Field.zero)
          let indV := Model.Field.nativeKaratsuba sInd (planarGet basisI idx)
          let v := Spec.Field.eadd (planarGet basis idx) (Spec.Field.eadd oodV indV)
          planarPush out v) out) (planarEmpty n)

structure PlanarFoldState where
  f : PlanarE
  basis : PlanarE
  claim : E
  quad : Array E
  folds : Array E
  state : Spec.Transcript.ProverState

def stepFoldPlanar (p : PlanarFoldState) : PlanarFoldState :=
  let (r, s) := Spec.Transcript.sample p.state
  let claim := polyEval p.quad r
  let f := foldPlanar p.f r
  let basis := foldPlanar p.basis r
  let (u0, u2) := msgPlanar f basis
  let (quad, s) := Spec.Pcs.Whir.sendRound s claim u0 u2
  ⟨f, basis, claim, quad, p.folds.push r, s⟩

def absorbFoldPlanar (p : PlanarFoldState) : PlanarFoldState :=
  let (r, s) := Spec.Transcript.sample p.state
  ⟨foldPlanar p.f r, foldPlanar p.basis r, polyEval p.quad r, p.quad, p.folds.push r, s⟩

def foldInitialLanes (bytes : @& ByteArray) (nLanes laneBlock foldCount : Nat)
    (terms : @& WeightTerms) (target : E) (s : Spec.Transcript.ProverState) : PlanarFoldState :=
  let projP := projectStack bytes laneBlock terms
  let matA := buildLaneMatrixA nLanes terms
  let (u0, u2) := sumcheckMsgBlocks terms.nTerms projP matA
  let (quad, s) := Spec.Pcs.Whir.sendRound s target u0 u2
  if decide (foldCount = 0) then
    let weights := Array.replicate nLanes Spec.Field.one
    let (f, b, _) := foldWitnessAndLift bytes nLanes laneBlock weights terms matA
    ⟨f, b, target, quad, #[], s⟩
  else
    let (_, matA, _, quad, folds, s) :=
      foldRange (foldCount - 1) (fun (curP, curA, _, qd, fs, st) _ =>
        let (r, st) := Spec.Transcript.sample st
        let cl := polyEval qd r
        let nextP := foldBlocks terms.nTerms curP r
        let nextA := foldBlocks terms.nTerms curA r
        let (u0, u2) := sumcheckMsgBlocks terms.nTerms nextP nextA
        let (qd, st) := Spec.Pcs.Whir.sendRound st cl u0 u2
        (nextP, nextA, cl, qd, fs.push r, st))
      (projP, matA, target, quad, (#[] : Array E), s)
    let (rLast, s) := Spec.Transcript.sample s
    let claim := polyEval quad rLast
    let finalA := foldBlocks terms.nTerms matA rLast
    let folds := folds.push rLast
    let laneWeights := (eqKernel folds).extract 0 nLanes
    let (f, basis, (u0, u2)) := foldWitnessAndLift bytes nLanes laneBlock laneWeights terms finalA
    let (quad, s) := Spec.Pcs.Whir.sendRound s claim u0 u2
    ⟨f, basis, claim, quad, folds, s⟩

def proveLevelPlanar (config : Spec.Pcs.Whir.Config) (logN lanes : Nat)
    (witness : @& ByteArray) (terms : @& WeightTerms)
    (p : PlanarFoldState) (level : Nat) (extPrep? : Option ExtPrepared) :
    Option (PlanarFoldState × Option ExtPrepared) := do
  let foldCount := config.folds.getD level 0
  let laneBlock := 1 <<< (logN - config.folds.getD 0 0)
  let p :=
    if decide (level = 0) then
      foldInitialLanes witness lanes laneBlock foldCount terms p.claim p.state
    else
      foldRange foldCount (fun cur _ => stepFoldPlanar cur) p
  let messageLog := logN - p.folds.size
  let finalLevel := decide (level + 1 = config.folds.size)
  let (s, oodInfo?, nextPrep?) ←
    if finalLevel then
      let s := Spec.Transcript.addScalars p.state (planarToArray p.f)
      pure (s, none, none)
    else
      let nextFold := config.folds.getD (level + 1) 0
      let nextRate := config.logInvRates.getD (level + 1) 0
      let (prep, root) := commitExtPlanar p.f (messageLog - nextFold) nextFold nextRate
      let s := addRootDigest32 p.state root
      let (ood, s) := introduceOodPlanar p.f s messageLog
      pure (s, some ood, some prep)
  let s ← grindWhirFast s queryGrindingBits
  let rate := config.logInvRates.getD level 0
  let blockLog := messageLog + rate
  let count := config.queries.getD level 0
  let perWord := 192 / blockLog
  if decide (perWord = 0) then none
  else
    let (drawn, s) := Spec.Pcs.Whir.proverSamples s ((count + perWord - 1) / perWord)
    let queries := sampleQueries count blockLog drawn
    let (lam, s) := Spec.Transcript.sample s
    let weights := powers lam queries.size
    let indices := Spec.Merkle.sortedUnique queries
    let phase ←
      if decide (level = 0) then
        openL0Cosets witness lanes messageLog rate queries
      else
        match extPrep? with
        | some prep => openExtCosets prep queries
        | none => none
    let s := hintPhaseFast s phase
    let laneFolds := p.folds.extract (p.folds.size - foldCount) p.folds.size
    let enforced := enforcedSumPhase level indices phase.rows queries laneFolds weights
    let basisI := inducedBasisPlanar messageLog rate queries weights
    let (u0, u2) := msgPlanar p.f basisI
    let (quadI, s) := Spec.Pcs.Whir.sendRound s enforced u0 u2
    let (basis, claim, quad) :=
      match oodInfo? with
      | some (z, oodVal, oodQuad) =>
        let s1 := lam
        let s2 := Model.Field.nativeKaratsuba lam lam
        let nextBasis := glueBasisPlanar p.basis (some z) s1 s2 basisI
        let nextClaim := Spec.Field.eadd p.claim
          (Spec.Field.eadd (Model.Field.nativeKaratsuba s1 oodVal)
            (Model.Field.nativeKaratsuba s2 enforced))
        let nextQuad := addScaled (addScaled p.quad s1 oodQuad) s2 quadI
        (nextBasis, nextClaim, nextQuad)
      | none =>
        let s1 := lam
        let nextBasis := glueBasisPlanar p.basis none Spec.Field.zero s1 basisI
        let nextClaim := Spec.Field.eadd p.claim (Model.Field.nativeKaratsuba s1 enforced)
        let nextQuad := addScaled p.quad s1 quadI
        (nextBasis, nextClaim, nextQuad)
    some (⟨p.f, basis, claim, quad, p.folds, s⟩, nextPrep?)

def provePcsOpenFlat (s : Spec.Transcript.ProverState) (stackLog logInvRate : Nat)
    (witness : ByteArray) (points : Array Spec.Pcs.StackOpen.StackClaim)
    (ring : Spec.Pcs.StackOpen.RingSwitchOpen) : Option Spec.Transcript.ProverState := do
  let config ← deriveConfig stackLog logInvRate
  if config.folds.isEmpty then none
  else
    let k0 := config.folds.getD 0 0
    let laneVars := stackLog - k0
    let laneBlock := 1 <<< laneVars
    let nWords := witness.size / 8
    if decide (nWords = 0 ∨ nWords % laneBlock ≠ 0) then none
    else
      let lanes := nWords / laneBlock
      let maps := (Array.range 6).foldl (fun acc _ =>
        let (c, s) := Spec.Transcript.sample acc.2
        (acc.1.push c, s)) (#[], s)
      let (lam, s) := Spec.Transcript.sample maps.2
      let coordWeights := RingSwitch.coordinateWeights maps.1
      let rsScales := powers lam ring.claims.size
      let ringWeights := (Array.range ring.claims.size).map fun i =>
        coordWeights.map (Model.Field.nativeKaratsuba (rsScales.getD i Spec.Field.zero))
      let values := (Array.range ring.claims.size).map (fun i =>
        let claim := ring.claims.getD i default
        let cols := RingSwitch.transposeSlices claim.slices
        (Array.range (min cols.size coordWeights.size)).foldl (fun acc j =>
          Spec.Field.eadd acc (RingSwitch.nativeMulBase
            (coordWeights.getD j Spec.Field.zero) (cols.getD j 0))) Spec.Field.zero)
        ++ points.map Spec.Pcs.StackOpen.StackClaim.value
      let target := dot (powers lam values.size) values
      let terms := termsOf nWords laneVars lam points ring ringWeights
      let p0 : PlanarFoldState := ⟨planarEmpty 0, planarEmpty 0, target, #[], #[], s⟩
      let (done, _) ← (Array.range config.folds.size).foldlM
        (fun (p, prep?) level =>
          proveLevelPlanar config stackLog lanes witness terms p level prep?)
        (p0, none)
      let resLog := stackLog - done.folds.size
      let done := foldRange resLog (fun p j =>
        if decide (j + 1 < resLog) then stepFoldPlanar p else absorbFoldPlanar p) done
      some done.state

def provePcsOpenFlatPlanar (s : Spec.Transcript.ProverState) (stackLog logInvRate : Nat)
    (witness : ByteArray) (points : Array Spec.Pcs.StackOpen.StackClaim)
    (ring : Spec.Pcs.StackOpen.RingSwitchOpen) : Option Spec.Transcript.ProverState :=
  provePcsOpenFlat s stackLog logInvRate witness points ring

end LeanVmXmss.Model.Pcs.FlatWhir
