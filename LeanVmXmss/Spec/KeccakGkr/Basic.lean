import Spec.Bus.Basic

namespace LeanVmXmss.Spec.KeccakGkr

open Spec.Field (K E zero one eadd emul mulBase einv embed esquare)
open Spec.Layout
open Spec.Bus (SlotClaim OutputClaim ProverState addScalar addScalars sampleChallenge sampleVec)
open Model.Pcs.Ntt (foldRange)

def packBits : Nat := 4
def packSize : Nat := 16
def embedBits : Nat := 24
def productBits : Nat := 47
def bitCount : Nat := 1600
def localBits : Nat := 11
def laneBits : Nat := 5
def wordBits : Nat := 64

def rmfeEmbed : Array UInt64 := #[
  0x40c50b, 0x7f79f2, 0x4b4e0a, 0x72740c, 0x5357da, 0x1d1c9e, 0x04be6e, 0x785246,
  0x097cdc, 0x109e7e, 0x1f1454, 0x213cfc, 0x4cfcc8, 0x775770, 0x187386, 0x818a16]

def rmfeProject : Array UInt64 := #[
  0x1, 0x7fffffffffff, 0x274e9d3a74e9, 0x1d3a74e9d3a7, 0x65cb972e5cb9, 0x5cb972e5cb97,
  0x6690aec7cd21, 0x5d8f9a42bb1f, 0x73485763e690, 0x3750967c6ea1, 0x12cf8dd4259f,
  0x1ba84b3e3750, 0x0ad0c9f715a1, 0x064fb8ad0c9f, 0x456864fb8ad0, 0x400000000000]

def keccakPi : Array Nat :=
  (Array.range stateLanes).map fun i =>
    let x := i % 5
    let y := i / 5
    y + 5 * ((2 * x + 3 * y) % 5)

def dot (a b : Array E) : E :=
  foldRange (min a.size b.size)
    (fun acc i => eadd acc (emul (a[i]?.getD zero) (b[i]?.getD zero))) zero

def sumSlice (xs : Array E) : E :=
  foldRange xs.size (fun acc i => eadd acc (xs[i]?.getD zero)) zero

def eqTable (point : Array E) : Array E := Spec.Bus.eqTable point

def polyEval (coeffs : Array E) (point : E) : E := Spec.Bus.polyEval coeffs point

def along (j k : Nat) : Nat :=
  let lane := j / wordBits
  let z := j % wordBits
  wordBits * ((lane % 5 + k) % 5 + 5 * (lane / 5)) + z

def linearTranspose (weights : Array E) : Array E :=
  let gathered := foldRange stateLanes
    (fun acc lane =>
      let rotation := Spec.Keccak.rho[lane]?.getD 0
      let image := keccakPi[lane]?.getD 0
      foldRange wordBits
        (fun cur z =>
          cur.setIfInBounds (wordBits * lane + z)
            (weights[wordBits * image + (z + rotation) % wordBits]?.getD zero))
        acc)
    (Array.replicate bitCount zero)
  let columns := foldRange bitCount
    (fun acc j =>
      let column := wordBits * ((j / wordBits) % 5) + j % wordBits
      acc.setIfInBounds column (eadd (acc[column]?.getD zero) (gathered[j]?.getD zero)))
    (Array.replicate (5 * wordBits) zero)
  (Array.range bitCount).map fun j =>
    let x := (j / wordBits) % 5
    let z := j % wordBits
    eadd (gathered[j]?.getD zero)
      (eadd (columns[wordBits * ((x + 1) % 5) + z]?.getD zero)
        (columns[wordBits * ((x + 4) % 5) + (z + 1) % wordBits]?.getD zero))

def powersOf (seed : E) (count : Nat) : Array E :=
  foldRange count
    (fun acc index =>
      if index = 0 then acc.setIfInBounds 0 one
      else acc.setIfInBounds index (emul (acc[index - 1]?.getD zero) seed))
    (Array.replicate count zero)

def instanceWeights (seed : E) : Array E :=
  let powers := powersOf seed embedBits
  (Array.range packSize).map fun index =>
    let mask := rmfeEmbed[index]?.getD 0
    foldRange embedBits
      (fun acc bit =>
        if decide (((mask >>> UInt64.ofNat bit) &&& 1) = 1) then
          eadd acc (powers[bit]?.getD zero)
        else acc)
      zero

def embedUnit (bits : UInt64) : UInt64 :=
  foldRange packSize
    (fun acc index =>
      if decide (((bits >>> UInt64.ofNat index) &&& 1) = 1) then
        acc ^^^ (rmfeEmbed[index]?.getD 0)
      else acc)
    0

def embedTable : Array UInt64 :=
  (Array.range (1 <<< packSize)).map fun bits => embedUnit (UInt64.ofNat bits)

def embedLookup (bits : UInt64) : UInt64 :=
  embedTable[bits.toNat]?.getD 0

def carryless (left right : UInt64) : UInt64 :=
  foldRange embedBits
    (fun acc index =>
      let shift := UInt64.ofNat index
      let mask := 0 - ((right >>> shift) &&& 1)
      acc ^^^ ((left <<< shift) &&& mask))
    0

def onesMask : UInt64 := embedUnit 0xffff

def chiPolynomial (left middle right : UInt64) : UInt64 :=
  carryless onesMask (left ^^^ right) ^^^ carryless middle right

structure GkrClaim where
  value : E
  mu : Array E
  point : Array E
  weights : Array E
  deriving Inhabited

structure Opening where
  point : Array E
  slices : Array E
  deriving Inhabited

structure WordOpening where
  point : Array E
  value : E
  deriving Inhabited

structure Openings where
  outputs : Option WordOpening
  inputs : Opening
  deriving Inhabited

structure RingSwitchClaim where
  offset : Nat
  suffixPoint : Array E
  slices : Array E
  deriving Inhabited

structure KeccakGkrStageOutput where
  ps : ProverState
  slotClaims : Array SlotClaim
  ringClaim : RingSwitchClaim
  openings : Openings
  deriving Inhabited

def segments : Nat := keccakRounds / keccakDepth

def segLog : Nat := log2Ceil segments

def stepsLog (rows : Nat) : Nat := max (log2Ceil rows) keccakMinStepsLog

def packVars (logSteps : Nat) : Nat := logSteps - packBits

def slotBits : Nat := log2Ceil (stateLanes * segments)

def addRoundPoly (state : ProverState) (coeffs : Array E) (equality : Bool) : ProverState :=
  foldRange coeffs.size
    (fun acc index =>
      if index = (if equality then 0 else 1) then acc
      else addScalar acc (coeffs[index]?.getD zero))
    state

def wordAt (committed : Array K) (width slot step : Nat) : K :=
  committed[slot * width + step]?.getD 0

def inputState (committed : Array K) (width step : Nat) : Spec.Keccak.State :=
  (Array.range stateLanes).map fun lane => wordAt committed width lane step

def afterRounds (state : Spec.Keccak.State) (count : Nat) : Spec.Keccak.State :=
  Spec.Keccak.rounds count 0 state

def preChi (state : Spec.Keccak.State) : Spec.Keccak.State :=
  Spec.Keccak.rhoPi (Spec.Keccak.theta state)

def roundState (state : Spec.Keccak.State) (round : Nat) : Spec.Keccak.State :=
  Spec.Keccak.iota (Spec.Keccak.chi (preChi state)) (Spec.Keccak.rc[round]?.getD 0)

def packMasksOf (states : Array Spec.Keccak.State) : Array UInt64 :=
  (Array.range bitCount).map fun position =>
    let lane := position / wordBits
    let z := position % wordBits
    foldRange packSize
      (fun acc index =>
        let bit := ((states[index]?.getD Spec.Keccak.zero)[lane]?.getD 0 >>> UInt64.ofNat z) &&& 1
        acc ||| (bit <<< UInt64.ofNat index))
      0

def buildRoundMasks (committed : Array K) (width : Nat) : Array (Array (Array UInt64)) :=
  let numPacks := width / packSize
  let byPack := foldRange numPacks
    (fun acc pack =>
      let base := packSize * pack
      let start := (Array.range packSize).map fun index => inputState committed width (base + index)
      let rounds := foldRange keccakRounds
        (fun step _ =>
          let states := step.1
          let masks := step.2
          let prepared := (Array.range packSize).map fun index =>
            preChi (states[index]?.getD Spec.Keccak.zero)
          let next := (Array.range packSize).map fun index =>
            Spec.Keccak.iota (Spec.Keccak.chi (prepared[index]?.getD Spec.Keccak.zero))
              (Spec.Keccak.rc[masks.size]?.getD 0)
          (next, masks.push (packMasksOf prepared)))
        (start, Array.emptyWithCapacity keccakRounds)
      acc.push rounds.2)
    (Array.emptyWithCapacity numPacks)
  (Array.range keccakRounds).map fun round =>
    (Array.range numPacks).map fun pack =>
      (byPack[pack]?.getD #[])[round]?.getD (Array.replicate bitCount 0)

def maskAt (masks : Array (Array (Array UInt64))) (round pack position : Nat) : UInt64 :=
  ((masks[round]?.getD #[])[pack]?.getD #[])[position]?.getD 0

def layerRound (layer segment : Nat) : Nat :=
  keccakDepth * (segment + 1) - layer - 1

def productAt (masks : Array (Array (Array UInt64))) (layer : Nat)
    (eqs weights : Array E) : Array E :=
  let pVars := Nat.log2 eqs.size - segLog
  let numPacks := 1 <<< pVars
  foldRange eqs.size
    (fun coeffs y =>
      let scale := eqs[y]?.getD zero
      let segment := y >>> pVars
      let pack := y % numPacks
      let round := layerRound layer segment
      let rowMasks := (masks[round]?.getD #[])[pack]?.getD #[]
      let rowBuckets := foldRange bitCount
        (fun buckets position =>
          let polynomial := chiPolynomial
            (embedLookup (rowMasks[position]?.getD 0))
            (embedLookup (rowMasks[along position 1]?.getD 0))
            (embedLookup (rowMasks[along position 2]?.getD 0))
          let w := weights[position]?.getD zero
          foldRange productBits
            (fun cur c =>
              if decide (((polynomial >>> UInt64.ofNat c) &&& 1) = 1) then
                cur.setIfInBounds c (eadd (cur[c]?.getD zero) w)
              else cur)
            buckets)
        (Array.replicate productBits zero)
      foldRange productBits
        (fun cur c =>
          cur.setIfInBounds c (eadd (cur[c]?.getD zero) (emul scale (rowBuckets[c]?.getD zero))))
        coeffs)
    (Array.replicate productBits zero)

def roundCoefficients (scale zeroV infinity value here : E) : Array E :=
  let c0 := emul scale zeroV
  let c2 := emul scale infinity
  #[c0, eadd (emul (eadd value c0) (einv here)) c2, c2]

def pairSums (rows : Array (Array E)) (claimWeights eqs : Array E) (kappa : E) : E × E :=
  foldRange (rows.size / 2)
    (fun acc index =>
      let low := rows[2 * index]?.getD (Array.replicate bitCount zero)
      let high := rows[2 * index + 1]?.getD (Array.replicate bitCount zero)
      let eqv := eqs[index]?.getD zero
      let lookup (table : Array E) (shift position : Nat) : E :=
        table[along position shift]?.getD zero
      let zeroV := foldRange bitCount
        (fun total position =>
          let left := lookup low 0 position
          let mid := lookup low 1 position
          let right := lookup low 2 position
          eadd total (emul (claimWeights[position]?.getD zero)
            (eadd (emul kappa left) (emul (eadd kappa mid) right))))
        zero
      let infinity := foldRange bitCount
        (fun total position =>
          let mid := eadd (lookup low 1 position) (lookup high 1 position)
          let right := eadd (lookup low 2 position) (lookup high 2 position)
          eadd total (emul (claimWeights[position]?.getD zero) (emul mid right)))
        zero
      (eadd acc.1 (emul eqv zeroV), eadd acc.2 (emul eqv infinity)))
    (zero, zero)

def foldRows (rows : Array (Array E)) (challenge : E) : Array (Array E) :=
  foldRange (rows.size / 2)
    (fun acc index =>
      let low := rows[2 * index]?.getD (Array.replicate bitCount zero)
      let high := rows[2 * index + 1]?.getD (Array.replicate bitCount zero)
      acc.push ((Array.range bitCount).map fun position =>
        eadd (low[position]?.getD zero)
          (emul challenge (eadd (low[position]?.getD zero) (high[position]?.getD zero)))))
    (Array.emptyWithCapacity (rows.size / 2))

def byteSums (mu : Array E) (offset : Nat) : Array E :=
  (Array.range 256).map fun byte =>
    foldRange 8
      (fun acc bit =>
        if decide (((byte >>> bit) &&& 1) = 1) then
          eadd acc (mu[offset + bit]?.getD zero)
        else acc)
      zero

def initialTable (masks : Array (Array (Array UInt64))) (layer : Nat) (mu : Array E) : Array (Array E) :=
  let loSums := byteSums mu 0
  let hiSums := byteSums mu 8
  let numPacks := (masks[0]?.getD #[]).size
  (Array.range (segments * numPacks)).map fun y =>
    let segment := y / numPacks
    let pack := y % numPacks
    let round := layerRound layer segment
    let rowMasks := (masks[round]?.getD #[])[pack]?.getD #[]
    (Array.range bitCount).map fun position =>
      let mask := (rowMasks[position]?.getD 0).toNat
      eadd (loSums[mask &&& 255]?.getD zero) (hiSums[(mask >>> 8) &&& 255]?.getD zero)

def localRound (w a b c : Array E) (kappa scale : E) : Array E :=
  let raw := foldRange (w.size / 2)
    (fun acc index =>
      let w0 := w[2 * index]?.getD zero
      let w1 := eadd w0 (w[2 * index + 1]?.getD zero)
      let t00 := a[2 * index]?.getD zero
      let t01 := eadd t00 (a[2 * index + 1]?.getD zero)
      let t10 := b[2 * index]?.getD zero
      let t11 := eadd t10 (b[2 * index + 1]?.getD zero)
      let t20 := c[2 * index]?.getD zero
      let t21 := eadd t20 (c[2 * index + 1]?.getD zero)
      let u0 := eadd kappa t10
      let p0 := eadd (emul kappa t00) (emul u0 t20)
      let p1 := eadd (eadd (emul kappa t01) (emul u0 t21)) (emul t11 t20)
      let p2 := emul t11 t21
      #[eadd (acc[0]?.getD zero) (emul w0 p0),
        eadd (acc[1]?.getD zero) (eadd (emul w0 p1) (emul w1 p0)),
        eadd (acc[2]?.getD zero) (eadd (emul w0 p2) (emul w1 p1)),
        eadd (acc[3]?.getD zero) (emul w1 p2)])
    #[zero, zero, zero, zero]
  raw.map fun coeff => emul scale coeff

def fold1 (table : Array E) (challenge : E) : Array E :=
  foldRange (table.size / 2)
    (fun acc index =>
      let lo := table[2 * index]?.getD zero
      let hi := table[2 * index + 1]?.getD zero
      acc.push (eadd lo (emul challenge (eadd lo hi))))
    (Array.emptyWithCapacity (table.size / 2))

def proveLayer (state : ProverState) (masks : Array (Array (Array UInt64))) (layer : Nat)
    (claim : GkrClaim) : GkrClaim × ProverState :=
  let product := productAt masks layer (eqTable claim.point) claim.weights
  let sent := addScalars state product
  let (seed, s1) := sampleChallenge sent
  let mu := instanceWeights seed
  let kappa := sumSlice mu
  let value0 := polyEval product seed
  let table0 := initialTable masks layer mu
  let bound := foldRange claim.point.size
    (fun acc index =>
      let point := acc.1
      let value := acc.2.1
      let scale := acc.2.2.1
      let current := acc.2.2.2.1
      let table := acc.2.2.2.2
      let here := claim.point[index]?.getD zero
      let later := eqTable (claim.point.extract (index + 1) claim.point.size)
      let pair := pairSums table claim.weights later kappa
      let coeffs := roundCoefficients scale pair.1 pair.2 value here
      let written := addRoundPoly current coeffs true
      let (challenge, next) := sampleChallenge written
      let grown := eadd (eadd one here) challenge
      (point.push challenge, emul grown (polyEval coeffs challenge), emul scale grown, next,
        foldRows table challenge))
    (Array.emptyWithCapacity claim.point.size, value0, one, s1, table0)
  let point := bound.1
  let scale := bound.2.2.1
  let current := bound.2.2.2.1
  let table := bound.2.2.2.2[0]?.getD (Array.replicate bitCount zero)
  let cube := 1 <<< localBits
  let shift (k : Nat) := (Array.range cube).map fun j =>
    if j < bitCount then table[along j k]?.getD zero else zero
  let w0 := claim.weights ++ Array.replicate (cube - claim.weights.size) zero
  let a0 := table ++ Array.replicate (cube - bitCount) zero
  let boundLocal := foldRange localBits
    (fun acc _ =>
      let lp := acc.1
      let w := acc.2.1
      let a := acc.2.2.1
      let b := acc.2.2.2.1
      let c := acc.2.2.2.2.1
      let cur := acc.2.2.2.2.2
      let coeffs := localRound w a b c kappa scale
      let written := addRoundPoly cur coeffs false
      let (challenge, next) := sampleChallenge written
      (lp.push challenge, fold1 w challenge, fold1 a challenge, fold1 b challenge,
        fold1 c challenge, next))
    (Array.emptyWithCapacity localBits, w0, a0, shift 1, shift 2, current)
  let lp := boundLocal.1
  let a := boundLocal.2.2.1
  let b := boundLocal.2.2.2.1
  let c := boundLocal.2.2.2.2.1
  let cur := boundLocal.2.2.2.2.2
  let t := #[a[0]?.getD zero, b[0]?.getD zero, c[0]?.getD zero]
  let written := addScalars cur t
  let (beta, done) := sampleChallenge written
  let eqv := eqTable lp
  let chi := (Array.range bitCount).map fun j =>
    eadd (eqv[j]?.getD zero)
      (emul beta (eadd (eqv[along j 4]?.getD zero) (emul beta (eqv[along j 3]?.getD zero))))
  (⟨eadd (t[0]?.getD zero) (emul beta (eadd (t[1]?.getD zero) (emul beta (t[2]?.getD zero)))),
    mu, point, linearTranspose chi⟩, done)

def slotWeights (claim : GkrClaim) (first count : Nat) : Array (Array E) :=
  let segmentsEq := eqTable (claim.point.extract (claim.point.size - segLog) claim.point.size)
  let slots := 1 <<< slotBits
  foldRange count
    (fun rows segment =>
      foldRange bitCount
        (fun cur position =>
          let slot := stateLanes * (first + segment) + position / wordBits
          let row := cur[slot]?.getD (Array.replicate wordBits zero)
          cur.setIfInBounds slot
            (row.setIfInBounds (position % wordBits)
              (emul (segmentsEq[segment]?.getD zero) (claim.weights[position]?.getD zero))))
        rows)
    (Array.replicate slots (Array.replicate wordBits zero))

def roundValues (a b : Array E) (width : Nat) : E × E :=
  let chunks := if width = 0 then 0 else a.size / (2 * width)
  foldRange chunks
    (fun acc chunk =>
      foldRange width
        (fun inner j =>
          let base := chunk * (2 * width)
          let al := a[base + j]?.getD zero
          let ah := a[base + width + j]?.getD zero
          let bl := b[base + j]?.getD zero
          let bh := b[base + width + j]?.getD zero
          (eadd inner.1 (emul al bl),
            eadd inner.2 (emul (eadd al ah) (eadd bl bh))))
        acc)
    (zero, zero)

def foldWidth (table : Array E) (width : Nat) (challenge : E) : Array E :=
  let chunks := if width = 0 then 0 else table.size / (2 * width)
  foldRange chunks
    (fun acc chunk =>
      foldRange width
        (fun cur j =>
          let base := chunk * (2 * width)
          let lo := table[base + j]?.getD zero
          let hi := table[base + width + j]?.getD zero
          cur.push (eadd lo (emul challenge (eadd lo hi))))
        acc)
    (Array.emptyWithCapacity (table.size / 2))

def proveRounds (state : ProverState) (a b : Array E) (width : Nat) (scale value : E) :
    Array E × Array E × Array E × E × ProverState :=
  let rounds := if a.size = 0 ∨ width = 0 ∨ a.size ≤ width then 0 else Nat.log2 (a.size / width)
  foldRange rounds
    (fun acc _ =>
      let point := acc.1
      let left := acc.2.1
      let right := acc.2.2.1
      let value := acc.2.2.2.1
      let current := acc.2.2.2.2
      let pair := roundValues left right width
      let coeffs := #[emul scale pair.1, eadd value (emul scale pair.2), emul scale pair.2]
      let written := addRoundPoly current coeffs false
      let (challenge, next) := sampleChallenge written
      (point.push challenge, foldWidth left width challenge, foldWidth right width challenge,
        polyEval coeffs challenge, next))
    (Array.emptyWithCapacity rounds, a, b, value, state)

def outputWords (committed : Array K) (width : Nat) (inst : Array E) : Array E :=
  let eqs := eqTable inst
  (Array.range (1 <<< slotBits)).map fun slot =>
    foldRange eqs.size
      (fun acc step =>
        eadd acc (mulBase (eqs[step]?.getD zero) (wordAt committed width slot step)))
      zero

def wordWeights (claim : GkrClaim) : Array E :=
  (slotWeights claim 1 (segments - 1)).map fun row => row[0]?.getD zero

def openOutputs (state : ProverState) (committed : Array K) (width : Nat)
    (inst : Array E) (claim : GkrClaim) (value : E) :
    WordOpening × ProverState :=
  let words := outputWords committed width inst
  let bound := proveRounds state words (wordWeights claim) 1 one value
  let slot := bound.1
  let word := bound.2.1[0]?.getD zero
  let written := addScalar bound.2.2.2.2 word
  (⟨inst ++ slot, word⟩, written)

def bitOf (word : K) (index : Nat) : Bool :=
  decide (((word >>> UInt64.ofNat index) &&& 1) = 1)

def packEval (committed : Array K) (width : Nat) (pack : Array E) : Array E :=
  let eqs := eqTable pack
  let slots := 1 <<< slotBits
  (Array.range (packSize * slots * wordBits)).map fun index =>
    let slot := index / (packSize * wordBits)
    let rest := index % (packSize * wordBits)
    let packRow := rest / wordBits
    let bit := rest % wordBits
    foldRange eqs.size
      (fun acc packIndex =>
        if bitOf (wordAt committed width slot (packIndex * packSize + packRow)) bit then
          eadd acc (eqs[packIndex]?.getD zero)
        else acc)
      zero

def perInstance (folded weights : Array E) : Array E :=
  (Array.range packSize).map fun packRow =>
    foldRange (1 <<< slotBits)
      (fun acc slot =>
        eadd acc (dot
          (folded.extract ((packRow + packSize * slot) * wordBits)
            ((packRow + packSize * slot + 1) * wordBits))
          (weights.extract (slot * wordBits) ((slot + 1) * wordBits))))
      zero

def atInstance (folded low : Array E) : Array E :=
  let eqs := eqTable low
  (Array.range ((1 <<< slotBits) * wordBits)).map fun index =>
    let slot := index / wordBits
    let bit := index % wordBits
    foldRange packSize
      (fun acc packRow =>
        eadd acc (emul (eqs[packRow]?.getD zero)
          (folded[(packRow + packSize * slot) * wordBits + bit]?.getD zero)))
      zero

def openInputs (state : ProverState) (committed : Array K) (width : Nat) (claim : GkrClaim) :
    Opening × ProverState :=
  let pack := claim.point.extract 0 (claim.point.size - segLog)
  let folded := packEval committed width pack
  let weights := (slotWeights claim 0 segments).foldl (fun acc row => acc ++ row) #[]
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
  (⟨low ++ pack ++ slotBound.1, slices⟩, written)

def proveReduction (state : ProverState) (committed : Array K) (executed : Nat)
    (output : OutputClaim) : Openings × ProverState :=
  let logSteps := stepsLog executed
  let width := 1 <<< logSteps
  let masks := buildRoundMasks committed width
  let (segment, afterSegment) := sampleVec state segLog
  let (lanes, afterLanes) := sampleVec afterSegment laneBits
  let laneEq := eqTable lanes
  let segmentEq := eqTable segment
  let weights := (Array.range bitCount).map fun position =>
    emul (laneEq[position / wordBits]?.getD zero)
      (embed (UInt64.ofNat (1 <<< (position % wordBits))))
  let last := emul (segmentEq[segments - 1]?.getD zero)
    (dot (laneEq.extract 0 stateLanes) output.lanes)
  let words := outputWords committed width output.instancePoint
  let firstClaim : GkrClaim :=
    ⟨zero, eqTable (output.instancePoint.extract 0 packBits),
      output.instancePoint.extract packBits output.instancePoint.size ++ segment, weights⟩
  let committedValue := dot words (wordWeights firstClaim)
  let afterValue := if segments > 1 then addScalar afterLanes committedValue else afterLanes
  let first : GkrClaim := { firstClaim with value := eadd committedValue last }
  let reduced := foldRange keccakDepth
    (fun acc layer =>
      let step := proveLayer acc.2 masks layer acc.1
      (step.1, step.2))
    (first, afterValue)
  let claim := reduced.1
  let opened := reduced.2
  let (outputs, afterOutputs) :=
    if segments > 1 then
      let openedOut := openOutputs opened committed width output.instancePoint first committedValue
      (some openedOut.1, openedOut.2)
    else (none, opened)
  let inputs := openInputs afterOutputs committed width claim
  (⟨outputs, inputs.1⟩, inputs.2)

def proveKeccakGkr (program : Array Spec.Vm.Op) (iv : ByteArray) (publicInput : Array E)
    (bundle : Spec.Witness.WitnessBundle) : KeccakGkrStageOutput :=
  let bus := Spec.Bus.proveBusAndConstraints program iv publicInput bundle
  let qBase := (bundle.sized.layout.placements[qKeccak]?.join).map Placement.index |>.getD 0
  let executed := bundle.sized.rows[opKeccak]?.getD 0
  let width := 1 <<< stepsLog executed
  let span := (1 <<< slotBits) * width
  let committed := (Array.range span).map fun index => bundle.message[qBase + index]?.getD 0
  let reduced := proveReduction bus.ps committed executed bus.keccakOutput
  let extra :=
    match reduced.1.outputs with
    | none => #[]
    | some opening => #[⟨qBase, opening.point, opening.value⟩]
  ⟨reduced.2, bus.slotClaims ++ extra,
    ⟨qBase, reduced.1.inputs.point, reduced.1.inputs.slices⟩, reduced.1⟩

end LeanVmXmss.Spec.KeccakGkr
