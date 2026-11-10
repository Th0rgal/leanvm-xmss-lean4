import Spec.KeccakGkr.Basic
import Model.Bus.Scalar

namespace LeanVmXmss.Model.KeccakGkr

open Spec.Field (K E zero one embed)
open Spec.Layout
open Spec.Bus (SlotClaim OutputClaim)
open Spec.KeccakGkr (packBits packSize embedBits productBits bitCount localBits laneBits wordBits
  rmfeEmbed rmfeProject keccakPi along embedUnit embedTable embedLookup carryless onesMask chiPolynomial
  GkrClaim Opening WordOpening Openings RingSwitchClaim
  segments segLog stepsLog packVars slotBits wordAt inputState afterRounds preChi roundState
  packMasksOf buildRoundMasks maskAt layerRound bitOf)
open Model.Field (eadd nativeKaratsuba nativeEinv)
open Model.Bus (ProverState addScalar addScalars sampleChallenge sampleVec nativeMulBase)
open Model.Pcs.Ntt (foldRange)

def dot (a b : Array E) : E :=
  foldRange (min a.size b.size)
    (fun acc i => eadd acc (nativeKaratsuba (a[i]?.getD zero) (b[i]?.getD zero))) zero

def sumSlice (xs : Array E) : E :=
  Spec.KeccakGkr.sumSlice xs

def eqTable (point : Array E) : Array E := Model.Bus.eqTable point

def polyEval (coeffs : Array E) (point : E) : E := Model.Bus.polyEval coeffs point

def linearTranspose (weights : Array E) : Array E :=
  Spec.KeccakGkr.linearTranspose weights

def powersOf (seed : E) (count : Nat) : Array E :=
  foldRange count
    (fun acc index =>
      if index = 0 then acc.setIfInBounds 0 one
      else acc.setIfInBounds index (nativeKaratsuba (acc[index - 1]?.getD zero) seed))
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

structure KeccakGkrStageOutput where
  ps : ProverState
  slotClaims : Array SlotClaim
  ringClaim : RingSwitchClaim
  openings : Openings
  deriving Inhabited

def KeccakGkrStageOutput.toSpec (o : KeccakGkrStageOutput) : Spec.KeccakGkr.KeccakGkrStageOutput :=
  ⟨o.ps.toSpec, o.slotClaims, o.ringClaim, o.openings⟩

def addRoundPoly (state : ProverState) (coeffs : Array E) (equality : Bool) : ProverState :=
  foldRange coeffs.size
    (fun acc index =>
      if index = (if equality then 0 else 1) then acc
      else addScalar acc (coeffs[index]?.getD zero))
    state

@[noinline] def productAt (masks : Array (Array (Array UInt64))) (layer : Nat)
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
          cur.setIfInBounds c
            (eadd (cur[c]?.getD zero) (nativeKaratsuba scale (rowBuckets[c]?.getD zero))))
        coeffs)
    (Array.replicate productBits zero)

def roundCoefficients (scale zeroV infinity value here : E) : Array E :=
  let c0 := nativeKaratsuba scale zeroV
  let c2 := nativeKaratsuba scale infinity
  #[c0, eadd (nativeKaratsuba (eadd value c0) (nativeEinv here)) c2, c2]

@[noinline] def pairSums (rows : Array (Array E)) (claimWeights eqs : Array E) (kappa : E) : E × E :=
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
          eadd total (nativeKaratsuba (claimWeights[position]?.getD zero)
            (eadd (nativeKaratsuba kappa left) (nativeKaratsuba (eadd kappa mid) right))))
        zero
      let infinity := foldRange bitCount
        (fun total position =>
          let mid := eadd (lookup low 1 position) (lookup high 1 position)
          let right := eadd (lookup low 2 position) (lookup high 2 position)
          eadd total (nativeKaratsuba (claimWeights[position]?.getD zero) (nativeKaratsuba mid right)))
        zero
      (eadd acc.1 (nativeKaratsuba eqv zeroV), eadd acc.2 (nativeKaratsuba eqv infinity)))
    (zero, zero)

@[noinline] def foldRows (rows : Array (Array E)) (challenge : E) : Array (Array E) :=
  foldRange (rows.size / 2)
    (fun acc index =>
      let low := rows[2 * index]?.getD (Array.replicate bitCount zero)
      let high := rows[2 * index + 1]?.getD (Array.replicate bitCount zero)
      acc.push ((Array.range bitCount).map fun position =>
        eadd (low[position]?.getD zero)
          (nativeKaratsuba challenge (eadd (low[position]?.getD zero) (high[position]?.getD zero)))))
    (Array.emptyWithCapacity (rows.size / 2))

@[noinline] def initialTable (masks : Array (Array (Array UInt64))) (layer : Nat)
    (mu : Array E) : Array (Array E) :=
  Spec.KeccakGkr.initialTable masks layer mu

@[noinline] def localRound (w a b c : Array E) (kappa scale : E) : Array E :=
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
      let p0 := eadd (nativeKaratsuba kappa t00) (nativeKaratsuba u0 t20)
      let p1 := eadd (eadd (nativeKaratsuba kappa t01) (nativeKaratsuba u0 t21))
        (nativeKaratsuba t11 t20)
      let p2 := nativeKaratsuba t11 t21
      #[eadd (acc[0]?.getD zero) (nativeKaratsuba w0 p0),
        eadd (acc[1]?.getD zero) (eadd (nativeKaratsuba w0 p1) (nativeKaratsuba w1 p0)),
        eadd (acc[2]?.getD zero) (eadd (nativeKaratsuba w0 p2) (nativeKaratsuba w1 p1)),
        eadd (acc[3]?.getD zero) (nativeKaratsuba w1 p2)])
    #[zero, zero, zero, zero]
  raw.map fun coeff => nativeKaratsuba scale coeff

@[noinline] def fold1 (table : Array E) (challenge : E) : Array E :=
  foldRange (table.size / 2)
    (fun acc index =>
      let lo := table[2 * index]?.getD zero
      let hi := table[2 * index + 1]?.getD zero
      acc.push (eadd lo (nativeKaratsuba challenge (eadd lo hi))))
    (Array.emptyWithCapacity (table.size / 2))

@[noinline] def proveLayer (state : ProverState) (masks : Array (Array (Array UInt64))) (layer : Nat)
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
      (point.push challenge, nativeKaratsuba grown (polyEval coeffs challenge),
        nativeKaratsuba scale grown, next, foldRows table challenge))
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
      (nativeKaratsuba beta
        (eadd (eqv[along j 4]?.getD zero) (nativeKaratsuba beta (eqv[along j 3]?.getD zero))))
  (⟨eadd (t[0]?.getD zero)
      (nativeKaratsuba beta (eadd (t[1]?.getD zero) (nativeKaratsuba beta (t[2]?.getD zero)))),
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
              (nativeKaratsuba (segmentsEq[segment]?.getD zero) (claim.weights[position]?.getD zero))))
        rows)
    (Array.replicate slots (Array.replicate wordBits zero))

@[noinline] def roundValues (a b : Array E) (width : Nat) : E × E :=
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
          (eadd inner.1 (nativeKaratsuba al bl),
            eadd inner.2 (nativeKaratsuba (eadd al ah) (eadd bl bh))))
        acc)
    (zero, zero)

@[noinline] def foldWidth (table : Array E) (width : Nat) (challenge : E) : Array E :=
  let chunks := if width = 0 then 0 else table.size / (2 * width)
  foldRange chunks
    (fun acc chunk =>
      foldRange width
        (fun cur j =>
          let base := chunk * (2 * width)
          let lo := table[base + j]?.getD zero
          let hi := table[base + width + j]?.getD zero
          cur.push (eadd lo (nativeKaratsuba challenge (eadd lo hi))))
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
      let coeffs := #[nativeKaratsuba scale pair.1,
        eadd value (nativeKaratsuba scale pair.2), nativeKaratsuba scale pair.2]
      let written := addRoundPoly current coeffs false
      let (challenge, next) := sampleChallenge written
      (point.push challenge, foldWidth left width challenge, foldWidth right width challenge,
        polyEval coeffs challenge, next))
    (Array.emptyWithCapacity rounds, a, b, value, state)

@[noinline] def outputWords (committed : Array K) (width : Nat) (inst : Array E) : Array E :=
  let eqs := eqTable inst
  (Array.range (1 <<< slotBits)).map fun slot =>
    foldRange eqs.size
      (fun acc step =>
        eadd acc (nativeMulBase (eqs[step]?.getD zero) (wordAt committed width slot step)))
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

@[noinline] def packEval (committed : Array K) (width : Nat) (pack : Array E) : Array E :=
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

@[noinline] def perInstance (folded weights : Array E) : Array E :=
  (Array.range packSize).map fun packRow =>
    foldRange (1 <<< slotBits)
      (fun acc slot =>
        eadd acc (dot
          (folded.extract ((packRow + packSize * slot) * wordBits)
            ((packRow + packSize * slot + 1) * wordBits))
          (weights.extract (slot * wordBits) ((slot + 1) * wordBits))))
      zero

@[noinline] def atInstance (folded low : Array E) : Array E :=
  let eqs := eqTable low
  (Array.range ((1 <<< slotBits) * wordBits)).map fun index =>
    let slot := index / wordBits
    let bit := index % wordBits
    foldRange packSize
      (fun acc packRow =>
        eadd acc (nativeKaratsuba (eqs[packRow]?.getD zero)
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
    nativeKaratsuba (laneEq[position / wordBits]?.getD zero)
      (embed (UInt64.ofNat (1 <<< (position % wordBits))))
  let last := nativeKaratsuba (segmentEq[segments - 1]?.getD zero)
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
  let bus := Model.Bus.proveBusAndConstraints program iv publicInput bundle
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

end LeanVmXmss.Model.KeccakGkr
