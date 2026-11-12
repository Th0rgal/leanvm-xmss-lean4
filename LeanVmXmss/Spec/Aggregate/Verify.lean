import Spec.Aggregate.Wire
import Spec.Bus.Basic
import Spec.KeccakGkr.Basic
import Spec.Pcs.Whir
import Spec.Transcript.Replay
import Spec.Xmss.Hints

namespace LeanVmXmss.Spec.Aggregate.Verify

open Spec.Field (K E zero one eadd emul mulBase embed)
open Spec.Layout
open Spec.Bus (BusForm ProdTerm ColumnClaim emptyBusForm scaleBusForm addBusForm accumulateCoord
  paddingWeight indexMle polyEval eqEval selectorPoint jumpIdentityForm)
open Spec.Transcript (VerifierState ReplayProof)

def foldRange {α : Type} (n : Nat) (f : α → Nat → α) (init : α) : α :=
  (Array.range n).foldl f init

structure PublicLayout where
  logMem : Nat
  logBytecode : Nat
  rows : Array Nat
  taus : Array Nat
  placements : Array (Option Placement)
  shape : Shape
  placed : Nat
  push : Array Block
  pull : Array Block
  count : Array Block
  pushLayout : BusLayout
  pullLayout : BusLayout
  countLayout : BusLayout
  deriving DecidableEq, Repr

def validateSizes (logMem logBytecode logInvRate : Nat) (rows : Array Nat) : Bool :=
  rows.size == nTables &&
    decide (minLogMem ≤ logMem ∧ logMem ≤ maxLogMem) &&
    decide (logBytecode ≤ maxTableLog) &&
    decide (minLogInvRate ≤ logInvRate ∧ logInvRate ≤ maxLogInvRate) &&
    rows.all (fun r => decide (r ≤ (1 <<< maxTableLog)))

def buildPublicLayout (logMem logBytecode : Nat) (rowArr : Array Nat) : PublicLayout :=
  let rows (t : Fin nTables) : Nat := rowArr[t.val]?.getD 0
  let taus := tableLog rows
  let (placements, shape, placed) := placementsOf logMem logBytecode taus
  let (push, pull, count) := busBlocks logMem logBytecode rows taus
  let tausArr : Array Nat :=
    #[taus ⟨0, by decide⟩, taus ⟨1, by decide⟩, taus ⟨2, by decide⟩,
      taus ⟨3, by decide⟩, taus ⟨4, by decide⟩, taus ⟨5, by decide⟩]
  let rowsNorm : Array Nat :=
    #[rows ⟨0, by decide⟩, rows ⟨1, by decide⟩, rows ⟨2, by decide⟩,
      rows ⟨3, by decide⟩, rows ⟨4, by decide⟩, rows ⟨5, by decide⟩]
  { logMem
    logBytecode
    rows := rowsNorm
    taus := tausArr
    placements
    shape
    placed
    push
    pull
    count
    pushLayout := busSideLayout push
    pullLayout := busSideLayout pull
    countLayout := busSideLayout count }

structure PreparedBytecode where
  logBytecode : Nat
  table : Array K
  iv : ByteArray
  deriving Inhabited

def prepareBytecode (program : Array Spec.Vm.Op) : Option PreparedBytecode :=
  if program.size < 2 || decide ((program.size &&& (program.size - 1)) ≠ 0) then
    none
  else
    let logBytecode := Spec.Witness.log2FloorPow2 program.size
    let cols := Spec.Layout.bytecodeColumns program
    let table := Spec.Layout.stackBytecodeColumns logBytecode cols
    let iv := Spec.Layout.fiatShamirIv table
    some ⟨logBytecode, table, iv⟩

def verifierSamples (s : VerifierState) (n : Nat) : Array E × VerifierState :=
  Spec.Pcs.Whir.verifierSamples s n

def dot (a b : Array E) : E :=
  Spec.Pcs.Whir.dot a b

def powers (x : E) (n : Nat) : Array E :=
  Spec.Pcs.Whir.powers x n

def eqKernel (point : Array E) : Array E :=
  Spec.Pcs.Whir.eqKernel point

def multilinearEvalE (values point : Array E) : Option E :=
  if decide (values.size = 1 <<< point.size) then
    some <|
      (Array.range point.size).foldl
        (fun cur k =>
          let r := point.getD k zero
          let half := cur.size / 2
          (Array.range half).map fun i =>
            let lo := cur.getD (2 * i) zero
            eadd lo (emul r (eadd lo (cur.getD (2 * i + 1) zero))))
        values |>.getD 0 zero
  else
    none

def sumcheckPlain (s : VerifierState) (degree rounds : Nat) (claim : E) :
    Option (Array E × E × VerifierState) :=
  (Array.range rounds).foldlM
    (fun (pts, curClaim, curS) _ => do
      let (coeffs, s1) ← Spec.Transcript.sumcheckRoundPoly curS degree curClaim none
      let (ch, s2) := Spec.Transcript.verifierSample s1
      some (pts.push ch, polyEval coeffs ch, s2))
    (#[], claim, s)

def sumcheckWithEq (s : VerifierState) (degree : Nat) (claim : E) (equalities : Array E) :
    Option (Array E × E × VerifierState) :=
  (Array.range equalities.size).foldlM
    (fun (pts, curClaim, curS) idx => do
      let r := equalities.getD idx zero
      let (coeffs, s1) ← Spec.Transcript.sumcheckRoundPoly curS degree curClaim (some r)
      let (ch, s2) := Spec.Transcript.verifierSample s1
      some (pts.push ch, polyEval coeffs ch, s2))
    (#[], claim, s)

def gkrLayerSchedule (depth : Nat) : Array (Nat × Nat) :=
  let (acc, _) :=
    (Array.range depth).foldl
      (fun (out, rem) _ =>
        if rem = 0 then
          (out, 0)
        else
          let step := if rem % 2 = 1 then 1 else 2
          (out.push (rem, step), rem - step))
      (#[], depth)
  acc

def prodArray (xs : Array E) : E :=
  xs.foldl emul one

def verifyGkrGrandProducts (depth : Nat) (s : VerifierState) :
    Option (E × Array E × Array E × VerifierState) := do
  let (shared, s) ← Spec.Transcript.nextScalar s
  let (count, s) ← Spec.Transcript.nextScalar s
  if Spec.Vm.wordBEq count zero then
    none
  else
    let schedule := gkrLayerSchedule depth
    let (point, values, s) ←
      schedule.foldlM
        (fun (pt, vals, curS) (_, step) => do
          let (combiner, s1) := Spec.Transcript.verifierSample curS
          let claim0 := polyEval vals combiner
          let (x, claim1, s2) ← sumcheckWithEq s1 (1 <<< step) claim0 pt
          let childLen := 1 <<< step
          let (c0, s3) ← Spec.Transcript.nextScalars childLen s2
          let (c1, s4) ← Spec.Transcript.nextScalars childLen s3
          let (c2, s5) ← Spec.Transcript.nextScalars childLen s4
          let prods := #[prodArray c0, prodArray c1, prodArray c2]
          if !Spec.Vm.wordBEq claim1 (polyEval prods combiner) then
            none
          else
            let (y, s6) := verifierSamples s5 step
            let v0 ← multilinearEvalE c0 y
            let v1 ← multilinearEvalE c1 y
            let v2 ← multilinearEvalE c2 y
            some (y ++ x, #[v0, v1, v2], s6))
        (#[], #[shared, shared, count], s)
    some (count, point, values, s)

def evalBusForm (form : BusForm) (evals : Array E) : E :=
  let lin :=
    foldRange form.coeffs.size
      (fun acc i => eadd acc (emul (form.coeffs.getD i zero) (evals.getD i zero)))
      form.constant
  foldRange form.prods.size
    (fun acc idx =>
      match form.prods[idx]? with
      | none => acc
      | some p =>
        let va := evals.getD p.colA zero
        let vb := evals.getD p.colB zero
        eadd acc (emul p.coeff (emul va vb)))
    lin

def verifySideBlocks (blocks : Array Block) (lay : BusLayout) (mu : Nat)
    (point : Array E) (frameworkCount : Nat) (frameworkFps : Array E)
    (weights : Array E) (sideBeta treeValue : E) : Array BusForm × E :=
  let formsInit := Spec.Bus.initTableForms
  let (knownSum, padSum, selSum, formsOut) :=
    foldRange blocks.size
      (fun (kAcc, pAcc, sAcc, curForms) b =>
        match blocks[b]? with
        | none => (kAcc, pAcc, sAcc, curForms)
        | some blk =>
          let kappa := blk.kappa
          let zetaLo := point.extract 0 kappa
          let zetaHi := point.extract kappa mu
          let sel := (lay.offsets.getD b 0) >>> kappa
          let eqHi := eqEval (selectorPoint sel (mu - kappa)) zetaHi
          let sAcc' := eadd sAcc eqHi
          if b < frameworkCount then
            let fp := frameworkFps.getD b zero
            let kAcc' := eadd kAcc (emul eqHi (eadd sideBeta fp))
            (kAcc', pAcc, sAcc', curForms)
          else
            match blk.owner with
            | none => (kAcc, pAcc, sAcc', curForms)
            | some t =>
              let base := tableBase t
              let nCols := tableWidth t
              let blockForm0 : BusForm := ⟨Array.replicate nCols zero, #[], sideBeta⟩
              let blockForm :=
                foldRange blk.coords.size
                  (fun f i =>
                    let c := blk.coords.getD i (cConst 0)
                    let wi := weights.getD i zero
                    accumulateCoord base wi f c)
                  blockForm0
              let prevForm := curForms.getD t.val (emptyBusForm nCols)
              let nextForm := addBusForm prevForm (scaleBusForm blockForm eqHi)
              let padRow := tablePadding t
              let padEval := evalBusForm blockForm (padRow.map embed)
              let wPad := paddingWeight zetaLo blk.rows
              let pTerm := emul (emul eqHi wPad) (eadd padEval one)
              (kAcc, eadd pAcc pTerm, sAcc', curForms.setIfInBounds t.val nextForm))
      (zero, zero, zero, formsInit)
  let onesPadding := eadd selSum one
  let total := eadd (eadd treeValue knownSum) (eadd onesPadding padSum)
  (formsOut, total)

structure BusVerifyResult where
  claims : Array ColumnClaim
  bytecodePoint : Array E
  point : Array E
  forms0 : Array BusForm
  forms1 : Array BusForm
  forms2 : Array BusForm
  totals : Array E
  s : VerifierState

def verifyBusBalance (bc : PreparedBytecode) (lay : PublicLayout)
    (s : VerifierState) : Option BusVerifyResult := do
  let mu := lay.pushLayout.mu
  let (alphas, s) := verifierSamples s busBits
  let weights := eqKernel alphas
  let (beta, s) := Spec.Transcript.verifierSample s
  let (_, point, treeValues, s) ← verifyGkrGrandProducts mu s
  if decide (point.size < lay.logMem) || decide (point.size < lay.logBytecode) then
    none
  else
    let memoryLow := point.extract 0 lay.logMem
    let bytecodeLow := point.extract 0 lay.logBytecode
    let (memory, s) ← Spec.Transcript.nextScalars 3 s
    let (memoryFinal, s) ← Spec.Transcript.nextScalar s
    let (bytecodeFinalVal, s) ← Spec.Transcript.nextScalar s
    let claims : Array ColumnClaim :=
      #[⟨memLo, memoryLow, memory.getD 0 zero⟩,
        ⟨memHi, memoryLow, memory.getD 1 zero⟩,
        ⟨memTop, memoryLow, memory.getD 2 zero⟩,
        ⟨memFinal, memoryLow, memoryFinal⟩,
        ⟨bytecodeFinal, bytecodeLow, bytecodeFinalVal⟩]
    let memoryIndex := indexMle memoryLow
    let bytecodeIndex := indexMle bytecodeLow
    let bytecodePoint := bytecodeLow ++ alphas
    if decide (bc.table.size ≠ 1 <<< bytecodePoint.size) then
      none
    else
      let bytecodeValue := Spec.Pcs.Whir.multilinearEval bc.table bytecodePoint
      let mkFingerprints (pcVal memCount bcCount : E) : Array E :=
        #[dot (weights.extract 0 3) #[embed sepState, pcVal, embed (Spec.Xmss.gpow 0)],
          dot (weights.extract 0 6)
            #[embed sepMem, memoryIndex, memCount,
              memory.getD 0 zero, memory.getD 1 zero, memory.getD 2 zero],
          eadd (dot (weights.extract 0 3) #[embed sepBytecode, bytecodeIndex, bcCount]) bytecodeValue]
      let finalPc := embed (Spec.Xmss.gpow ((1 <<< lay.logBytecode) - 1))
      let fpsPush := mkFingerprints (embed (Spec.Xmss.gpow 0)) one one
      let fpsPull := mkFingerprints finalPc memoryFinal bytecodeFinalVal
      let (forms0, total0) :=
        verifySideBlocks lay.push lay.pushLayout mu point 3 fpsPush weights beta (treeValues.getD 0 zero)
      let (forms1, total1) :=
        verifySideBlocks lay.pull lay.pullLayout mu point 3 fpsPull weights beta (treeValues.getD 1 zero)
      let (forms2, total2) :=
        verifySideBlocks lay.count { lay.countLayout with mu := mu } mu point 0 #[] #[one] zero
          (treeValues.getD 2 zero)
      some ⟨claims, bytecodePoint, point, forms0, forms1, forms2, #[total0, total1, total2], s⟩

def verifyTableSumcheck (taus : Array Nat) (forms0 forms1 forms2 : Array BusForm)
    (constraintPowers formPowers equalityPoint : Array E) (target : E)
    (s : VerifierState) : Option (Array (Array E × Array E) × VerifierState) := do
  let nRounds := taus.foldl max 0
  let (challenges, claim, s) ← sumcheckPlain s 3 nRounds target
  let point := challenges.reverse
  let weightsInit := Array.replicate nTables one
  let weights :=
    foldRange point.size
      (fun ws varIdx =>
        let ch := point.getD varIdx zero
        let eqFactor := eadd (eadd one (equalityPoint.getD varIdx zero)) ch
        foldRange nTables
          (fun cur t =>
            let h := taus.getD t 0
            let factor := if h > varIdx then eqFactor else ch
            cur.setIfInBounds t (emul (cur.getD t one) factor))
          ws)
      weightsInit
  let (rows, s) ←
    (Array.range nTables).foldlM
      (fun (acc, curS) t =>
        if h : t < nTables then do
          let width := tableWidth ⟨t, h⟩
          let height := taus.getD t 0
          let (evals, nextS) ← Spec.Transcript.nextScalars width curS
          some (acc.push (point.extract 0 height, evals), nextS)
        else
          some (acc, curS))
      (#[], s)
  let p0 := constraintPowers.getD 0 zero
  let p1 := constraintPowers.getD 1 zero
  let terminal :=
    foldRange nTables
      (fun acc t =>
        let evals := (rows.getD t (#[], #[])).2
        let summand :=
          if t = opJump then
            let cond := evals.getD 5 zero
            let inv := evals.getD 12 zero
            let flag := evals.getD 13 zero
            let c0 := eadd flag (emul cond inv)
            let c1 := emul cond (eadd flag one)
            eadd (emul p0 c0) (emul p1 c1)
          else
            zero
        let fv0 := evalBusForm (forms0.getD t (emptyBusForm 0)) evals
        let fv1 := evalBusForm (forms1.getD t (emptyBusForm 0)) evals
        let fv2 := evalBusForm (forms2.getD t (emptyBusForm 0)) evals
        let formTerm := dot formPowers #[fv0, fv1, fv2]
        eadd acc (emul (weights.getD t zero) (eadd summand formTerm)))
      zero
  if Spec.Vm.wordBEq terminal claim then
    some (rows, s)
  else
    none

def verifyKeccakLayer (logSteps step : Nat) (claim : Spec.KeccakGkr.GkrClaim)
    (s : VerifierState) : Option (Spec.KeccakGkr.GkrClaim × VerifierState) := do
  let packVars := logSteps - Spec.KeccakGkr.packBits
  let segs := keccakRounds / keccakDepth
  let (product, s) ← Spec.Transcript.nextScalars Spec.KeccakGkr.productBits s
  let projected :=
    foldRange Spec.KeccakGkr.productBits
      (fun acc c =>
        let functional :=
          foldRange Spec.KeccakGkr.packSize
            (fun fAcc i =>
              let mask := Spec.KeccakGkr.rmfeProject.getD i 0
              if decide (((mask >>> UInt64.ofNat c) &&& 1) = 1) then
                eadd fAcc (claim.mu.getD i zero)
              else
                fAcc)
            zero
        eadd acc (emul functional (product.getD c zero)))
      zero
  let segEq := eqKernel (claim.point.extract packVars claim.point.size)
  let iota :=
    foldRange segs
      (fun acc seg =>
        let rc := Spec.Keccak.rc.getD (keccakDepth * (seg + 1) - step - 1) 0
        let wSum :=
          foldRange Spec.KeccakGkr.wordBits
            (fun zAcc z =>
              if decide (((rc >>> UInt64.ofNat z) &&& 1) = 1) then
                eadd zAcc (claim.weights.getD z zero)
              else
                zAcc)
            zero
        eadd acc (emul (segEq.getD seg zero) wSum))
      zero
  let muSum := Spec.KeccakGkr.sumSlice claim.mu
  if !Spec.Vm.wordBEq (eadd projected (emul iota muSum)) claim.value then
    none
  else
    let (seed, s) := Spec.Transcript.verifierSample s
    let mu := Spec.KeccakGkr.instanceWeights seed
    let kappa := Spec.KeccakGkr.sumSlice mu
    let value0 := polyEval product seed
    let (point, value1, scale, s) ←
      (Array.range claim.point.size).foldlM
        (fun (pts, curVal, curScale, curS) idx => do
          let r := claim.point.getD idx zero
          let (msg, s1) ← Spec.Transcript.sumcheckRoundPoly curS 2 curVal (some r)
          let (ch, s2) := Spec.Transcript.verifierSample s1
          let factor := eadd (eadd one r) ch
          some (pts.push ch, emul factor (polyEval msg ch), emul curScale factor, s2))
        (#[], value0, one, s)
    let (localPt, value2, s) ← sumcheckPlain s 3 Spec.KeccakGkr.localBits value1
    let (t, s) ← Spec.Transcript.nextScalars 3 s
    let eqLocal := eqKernel localPt
    let wDot := dot (eqLocal.extract 0 Spec.KeccakGkr.bitCount) claim.weights
    let t0 := t.getD 0 zero
    let t1 := t.getD 1 zero
    let t2 := t.getD 2 zero
    let chiVal := eadd (emul kappa t0) (emul (eadd kappa t1) t2)
    if !Spec.Vm.wordBEq (emul (emul scale wDot) chiVal) value2 then
      none
    else
      let (beta, s) := Spec.Transcript.verifierSample s
      let rawWeights :=
        (Array.range Spec.KeccakGkr.bitCount).map fun j =>
          eadd (eqLocal.getD j zero)
            (emul beta
              (eadd (eqLocal.getD (Spec.KeccakGkr.along j 4) zero)
                (emul beta (eqLocal.getD (Spec.KeccakGkr.along j 3) zero))))
      let nextVal := eadd t0 (emul beta (eadd t1 (emul beta t2)))
      some (⟨nextVal, mu, point, Spec.KeccakGkr.linearTranspose rawWeights⟩, s)

def slotWeights (logSteps : Nat) (claim : Spec.KeccakGkr.GkrClaim) (first count : Nat) :
    Array (Array E) :=
  let packVars := logSteps - Spec.KeccakGkr.packBits
  let segEq := eqKernel (claim.point.extract packVars claim.point.size)
  let sBits := log2Ceil (stateLanes * (keccakRounds / keccakDepth))
  let slots := 1 <<< sBits
  foldRange count
    (fun rows seg =>
      foldRange Spec.KeccakGkr.bitCount
        (fun cur j =>
          let slot := stateLanes * (first + seg) + j / Spec.KeccakGkr.wordBits
          let row := cur.getD slot (Array.replicate Spec.KeccakGkr.wordBits zero)
          cur.setIfInBounds slot
            (row.setIfInBounds (j % Spec.KeccakGkr.wordBits)
              (emul (segEq.getD seg zero) (claim.weights.getD j zero))))
        rows)
    (Array.replicate slots (Array.replicate Spec.KeccakGkr.wordBits zero))

def openSlot (logSteps : Nat) (claim : Spec.KeccakGkr.GkrClaim) (first count : Nat)
    (value : E) (s : VerifierState) : Option (Array E × Array E × E × VerifierState) := do
  let sBits := log2Ceil (stateLanes * (keccakRounds / keccakDepth))
  let (slot, outVal, s) ← sumcheckPlain s 2 sBits value
  let rows0 := slotWeights logSteps claim first count
  let folded :=
    foldRange slot.size
      (fun rows idx =>
        let ch := slot.getD idx zero
        let half := rows.size / 2
        (Array.range half).map fun i =>
          let r0 := rows.getD (2 * i) (Array.replicate Spec.KeccakGkr.wordBits zero)
          let r1 := rows.getD (2 * i + 1) (Array.replicate Spec.KeccakGkr.wordBits zero)
          (Array.range Spec.KeccakGkr.wordBits).map fun z =>
            let a := r0.getD z zero
            let b := r1.getD z zero
            eadd a (emul ch (eadd a b)))
      rows0
  some (slot, folded.getD 0 (Array.replicate Spec.KeccakGkr.wordBits zero), outVal, s)

def verifyKeccak (logSteps : Nat) (inst output : Array E) (s : VerifierState) :
    Option (Spec.KeccakGkr.Openings × VerifierState) := do
  if decide (inst.size ≠ logSteps) || decide (output.size ≠ stateLanes) ||
      decide (logSteps < Spec.KeccakGkr.packBits) then
    none
  else
    let segs := keccakRounds / keccakDepth
    let segBits := log2Ceil segs
    let (segment, s) := verifierSamples s segBits
    let point := inst.extract Spec.KeccakGkr.packBits inst.size ++ segment
    let (laneCh, s) := verifierSamples s Spec.KeccakGkr.laneBits
    let lanes := eqKernel laneCh
    let weights :=
      (Array.range Spec.KeccakGkr.bitCount).map fun j =>
        mulBase (lanes.getD (j / Spec.KeccakGkr.wordBits) zero)
          ((1 : UInt64) <<< UInt64.ofNat (j % Spec.KeccakGkr.wordBits))
    let last := emul ((eqKernel segment).getD (segs - 1) zero) (dot (lanes.extract 0 stateLanes) output)
    let (committed, s) ←
      if segs > 1 then Spec.Transcript.nextScalar s else some (zero, s)
    let first : Spec.KeccakGkr.GkrClaim :=
      { value := eadd committed last
        mu := eqKernel (inst.extract 0 Spec.KeccakGkr.packBits)
        point := point
        weights := weights }
    let (claim, s) ←
      (Array.range keccakDepth).foldlM
        (fun (cur, curS) step => verifyKeccakLayer logSteps step cur curS)
        (first, s)
    let (outputs, s) ←
      if segs > 1 then do
        let (slot, rowWeights, val, s1) ← openSlot logSteps first 1 (segs - 1) committed s
        let (word, s2) ← Spec.Transcript.nextScalar s1
        if !Spec.Vm.wordBEq (emul (rowWeights.getD 0 zero) word) val then
          none
        else
          some (some (Spec.KeccakGkr.WordOpening.mk (inst ++ slot) word), s2)
      else
        some (none, s)
    let (low, val1, s) ← sumcheckPlain s 2 Spec.KeccakGkr.packBits claim.value
    let (slot, rowWeights, val2, s) ← openSlot logSteps claim 0 segs val1 s
    let (slices, s) ← Spec.Transcript.nextScalars Spec.KeccakGkr.wordBits s
    let muEval ← multilinearEvalE claim.mu low
    if !Spec.Vm.wordBEq (emul muEval (dot rowWeights slices)) val2 then
      none
    else
      let packVars := logSteps - Spec.KeccakGkr.packBits
      let inPoint := low ++ claim.point.extract 0 packVars ++ slot
      some (⟨outputs, ⟨inPoint, slices⟩⟩, s)

structure ExecutionSummary where
  logMemory : Nat
  tableRows : Array Nat
  logInvRate : Nat
  bytecodePoint : Array E
  merklePaths : Array Spec.Merkle.MerklePath

def toPlacedClaims (placements : Array (Option Placement)) (claims : Array ColumnClaim) :
    Array Spec.Pcs.Whir.PlacedClaim :=
  foldRange claims.size
    (fun acc idx =>
      match claims[idx]? with
      | none => acc
      | some c =>
        match placements[c.col]?.join with
        | none => acc
        | some p => acc.push ⟨⟨p.variables, p.index⟩, c.point, c.value⟩)
    #[]

def verifyExecution (bc : PreparedBytecode) (publicInput : ByteArray)
    (proof : Spec.Aggregate.Wire.VmProof) : Option ExecutionSummary := do
  if decide (publicInput.size ≠ 32) then
    none
  else
    let replay : ReplayProof := ⟨proof.stream, proof.merkle⟩
    let s := Spec.Transcript.verifierNew replay bc.iv publicInput
    let (announced, s) ← Spec.Transcript.nextScalars (2 + nTables) s
    if !(announced.all fun v => decide (v.c1 = 0 ∧ v.c2 = 0)) then
      none
    else
      let logMemory := (announced.getD 0 zero).c0.toNat
      let tableRows := (Array.range nTables).map fun i => (announced.getD (1 + i) zero).c0.toNat
      let logInvRate := (announced.getD (1 + nTables) zero).c0.toNat
      if !validateSizes logMemory bc.logBytecode logInvRate tableRows then
        none
      else
        let lay := buildPublicLayout logMemory bc.logBytecode tableRows
        if !(decide (minStackedLog ≤ lay.shape.mu ∧ lay.shape.mu ≤ maxStackedLog)) then
          none
        else
          let (halves, s) ← Spec.Transcript.nextScalars 2 s
          let root ← Spec.Merkle.fromHalves (halves.getD 0 zero) (halves.getD 1 zero)
          let bus ← verifyBusBalance bc lay s
          let (xi, s) := Spec.Transcript.verifierSample bus.s
          let xiPowers := powers xi (xiFormBase + 3)
          let constraintPowers := xiPowers.extract 0 xiFormBase
          let formPowers := xiPowers.extract xiFormBase (xiFormBase + 3)
          let target := dot formPowers bus.totals
          let (evaluations, s) ←
            verifyTableSumcheck lay.taus bus.forms0 bus.forms1 bus.forms2
              constraintPowers formPowers bus.point target s
          let claimsWithTables :=
            foldRange nTables
              (fun acc t =>
                if h : t < nTables then
                  let base := tableBase ⟨t, h⟩
                  let (pt, vals) := evaluations.getD t (#[], #[])
                  foldRange vals.size
                    (fun cur loc => cur.push ⟨base + loc, pt, vals.getD loc zero⟩)
                    acc
                else
                  acc)
              bus.claims
          let (publicChallenge, s) := Spec.Transcript.verifierSample s
          let (first, second) := Spec.Merkle.hashToScalars publicInput
          let memVars := (lay.placements[memLo]?.join.map Placement.variables).getD lay.logMem
          let publicPoint := (Array.replicate memVars zero).setIfInBounds 0 publicChallenge
          let piClaims : Array ColumnClaim :=
            #[⟨memLo, publicPoint, Spec.Bus.interpK first.c0 second.c0 publicChallenge⟩,
              ⟨memHi, publicPoint, Spec.Bus.interpK first.c1 second.c1 publicChallenge⟩,
              ⟨memTop, publicPoint, Spec.Bus.interpK first.c2 second.c2 publicChallenge⟩]
          let claimsWithPi := claimsWithTables ++ piClaims
          let (keccakPt, keccakVals) := evaluations.getD opKeccak (#[], #[])
          let keccakOutVals := keccakVals.extract keccakOut (keccakOut + stateLanes)
          let keccakLogSteps := lay.taus.getD opKeccak 0
          let (openings, s) ← verifyKeccak keccakLogSteps keccakPt keccakOutVals s
          let allClaims :=
            match openings.outputs with
            | some out => claimsWithPi.push ⟨qKeccak, out.point, out.value⟩
            | none => claimsWithPi
          let qkPlace ← lay.placements[qKeccak]?.join
          let qkStack : Spec.Pcs.StackOpen.Placement := ⟨qkPlace.variables, qkPlace.index⟩
          let placedClaims := toPlacedClaims lay.placements allClaims
          let s ←
            Spec.Pcs.Whir.verifyRingSwitchAndStacked s root lay.shape.mu lay.placed logInvRate
              qkStack openings.inputs.point openings.inputs.slices placedClaims
          let paths ← Spec.Transcript.finish s
          some ⟨logMemory, tableRows, logInvRate, bus.bytecodePoint, paths⟩

def statementBytes (pair : E × E) : ByteArray :=
  Spec.Xmss.writeLE pair.1.c0 8 ++ Spec.Xmss.writeLE pair.1.c1 8 ++
    Spec.Xmss.writeLE pair.2.c0 8 ++ Spec.Xmss.writeLE pair.2.c1 8

def verifyEthereumProof (guest : PreparedBytecode) (seed : E × E)
    (eth : Spec.Aggregate.Wire.EthereumProof) : Bool :=
  if !Spec.Aggregate.Wire.signerSetOk eth.claims then
    false
  else if !Spec.Aggregate.Wire.deferredMatches guest.table eth.defer then
    false
  else
    let pi := statementBytes (Spec.Aggregate.Wire.EthereumProof.statement seed eth)
    (verifyExecution guest pi eth.proof).isSome

def verifyEthereumBytes (guest : PreparedBytecode) (seed : E × E)
    (bytes : ByteArray) : Bool :=
  let dummy := zero
  match Spec.Aggregate.Wire.EthereumProof.fromBytes bytes dummy with
  | none => false
  | some raw =>
    if decide (1 <<< raw.defer.bytecodePoint.size ≠ guest.table.size) then
      false
    else
      let val := Spec.Pcs.Whir.multilinearEval guest.table raw.defer.bytecodePoint
      let eth : Spec.Aggregate.Wire.EthereumProof :=
        { raw with defer := { raw.defer with bytecodeValue := val } }
      verifyEthereumProof guest seed eth

def verifyEthereumBytesWithoutPubkeys (guest : PreparedBytecode) (seed : E × E)
    (claims : Spec.Aggregate.Wire.SignatureClaims) (bytes : ByteArray) : Bool :=
  match Spec.Aggregate.Wire.EthereumProof.fromBytesWithoutPubkeys bytes claims zero with
  | none => false
  | some raw =>
    if decide (1 <<< raw.defer.bytecodePoint.size ≠ guest.table.size) then
      false
    else
      let val := Spec.Pcs.Whir.multilinearEval guest.table raw.defer.bytecodePoint
      let eth : Spec.Aggregate.Wire.EthereumProof :=
        { raw with defer := { raw.defer with bytecodeValue := val } }
      verifyEthereumProof guest seed eth

def verifyVmWireBytes (bc : PreparedBytecode) (publicInput : ByteArray)
    (bytes : ByteArray) : Bool :=
  match Spec.Aggregate.Wire.Cursor.proof ⟨bytes, 0⟩ with
  | none => false
  | some (proof, cursor) =>
    if decide (cursor.pos ≠ bytes.size) then
      false
    else
      (verifyExecution bc publicInput proof).isSome

end LeanVmXmss.Spec.Aggregate.Verify
