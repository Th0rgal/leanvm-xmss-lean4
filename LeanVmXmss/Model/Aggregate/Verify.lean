import Spec.Aggregate.Verify
import Model.Aggregate.Wire
import Model.Bus.Scalar
import Model.KeccakGkr.Scalar
import Model.Pcs.Whir

namespace LeanVmXmss.Model.Aggregate.Verify

open Spec.Field (K E zero one embed)
open Spec.Layout
open Spec.Bus (BusForm ProdTerm ColumnClaim emptyBusForm accumulateCoord selectorPoint)
open Spec.Transcript (VerifierState ReplayProof)
open Spec.Aggregate.Verify (PreparedBytecode ExecutionSummary BusVerifyResult gkrLayerSchedule toPlacedClaims statementBytes)
open Model.Field (eadd nativeKaratsuba)
open Model.Bus (nativeMulBase paddingWeight indexMle polyEval eqEval interpK)
open Model.Pcs.Ntt (foldRange)

def prepareBytecodeFast (program : Array Spec.Vm.Op) : Option PreparedBytecode :=
  if program.size < 2 || decide ((program.size &&& (program.size - 1)) ≠ 0) then
    none
  else
    let logBytecode := Spec.Witness.log2FloorPow2 program.size
    let cols := Model.Layout.bytecodeColumnsFast program
    let table := Model.Layout.stackBytecodeColumnsFast logBytecode cols
    let iv := Model.Layout.fiatShamirIvFast table
    some ⟨logBytecode, table, iv⟩

def dot (a b : Array E) : E :=
  Model.Pcs.Whir.dot a b

def powers (x : E) (n : Nat) : Array E :=
  Model.Pcs.Whir.powers x n

def eqKernel (point : Array E) : Array E :=
  Model.Pcs.Whir.eqKernel point

def verifierSamples (s : VerifierState) (n : Nat) : Array E × VerifierState :=
  Model.Pcs.Whir.verifierSamples s n

def multilinearEvalE (values point : Array E) : Option E :=
  if decide (values.size = 1 <<< point.size) then
    some <|
      (Array.range point.size).foldl
        (fun cur k =>
          let r := point.getD k zero
          let half := cur.size / 2
          (Array.range half).map fun i =>
            let lo := cur.getD (2 * i) zero
            eadd lo (nativeKaratsuba r (eadd lo (cur.getD (2 * i + 1) zero))))
        values |>.getD 0 zero
  else
    none

def evalBytecodeFast (bc : PreparedBytecode) (point : Array E) : Option E :=
  if decide (bc.table.size ≠ 1 <<< point.size) then
    none
  else
    some (Model.Pcs.Whir.multilinearEval bc.table point)

def sumcheckRoundPolyFast (s : VerifierState) (degree : Nat) (claimedSum : E)
    (eqFactor : Option E := none) : Option (Array E × VerifierState) := do
  if degree < 1 then none else
    match eqFactor with
    | none =>
      let (c0, s) ← Spec.Transcript.nextScalar s
      let (tail, s) ← Spec.Transcript.nextScalars (degree - 1) s
      let c1 := eadd claimedSum (tail.foldl eadd zero)
      some (#[c0, c1] ++ tail, s)
    | some r =>
      let (tail, s) ← Spec.Transcript.nextScalars degree s
      let c0 := eadd claimedSum (nativeKaratsuba r (tail.foldl eadd zero))
      some (#[c0] ++ tail, s)

def sumcheckPlain (s : VerifierState) (degree rounds : Nat) (claim : E) :
    Option (Array E × E × VerifierState) :=
  (Array.range rounds).foldlM
    (fun (pts, curClaim, curS) _ => do
      let (coeffs, s1) ← sumcheckRoundPolyFast curS degree curClaim none
      let (ch, s2) := Spec.Transcript.verifierSample s1
      some (pts.push ch, polyEval coeffs ch, s2))
    (#[], claim, s)

def sumcheckWithEq (s : VerifierState) (degree : Nat) (claim : E) (equalities : Array E) :
    Option (Array E × E × VerifierState) :=
  (Array.range equalities.size).foldlM
    (fun (pts, curClaim, curS) idx => do
      let r := equalities.getD idx zero
      let (coeffs, s1) ← sumcheckRoundPolyFast curS degree curClaim (some r)
      let (ch, s2) := Spec.Transcript.verifierSample s1
      some (pts.push ch, polyEval coeffs ch, s2))
    (#[], claim, s)

def prodArray (xs : Array E) : E :=
  xs.foldl nativeKaratsuba one

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

def scaleBusFormFast (form : BusForm) (factor : E) : BusForm :=
  { coeffs := form.coeffs.map (nativeKaratsuba factor)
    prods := form.prods.map (fun p => ⟨p.colA, p.colB, nativeKaratsuba factor p.coeff⟩)
    constant := nativeKaratsuba factor form.constant }

def evalBusForm (form : BusForm) (evals : Array E) : E :=
  let lin :=
    foldRange form.coeffs.size
      (fun acc i => eadd acc (nativeKaratsuba (form.coeffs.getD i zero) (evals.getD i zero)))
      form.constant
  foldRange form.prods.size
    (fun acc idx =>
      match form.prods[idx]? with
      | none => acc
      | some p =>
        let va := evals.getD p.colA zero
        let vb := evals.getD p.colB zero
        eadd acc (nativeKaratsuba p.coeff (nativeKaratsuba va vb)))
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
            let kAcc' := eadd kAcc (nativeKaratsuba eqHi (eadd sideBeta fp))
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
              let nextForm := Spec.Bus.addBusForm prevForm (scaleBusFormFast blockForm eqHi)
              let padRow := tablePadding t
              let padEval := evalBusForm blockForm (padRow.map embed)
              let wPad := paddingWeight zetaLo blk.rows
              let pTerm := nativeKaratsuba (nativeKaratsuba eqHi wPad) (eadd padEval one)
              (kAcc, eadd pAcc pTerm, sAcc', curForms.setIfInBounds t.val nextForm))
      (zero, zero, zero, formsInit)
  let onesPadding := eadd selSum one
  let total := eadd (eadd treeValue knownSum) (eadd onesPadding padSum)
  (formsOut, total)

def verifyBusBalance (bc : PreparedBytecode) (lay : Model.Layout.PublicLayout)
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
    let bytecodeValue ← evalBytecodeFast bc bytecodePoint
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
            cur.setIfInBounds t (nativeKaratsuba (cur.getD t one) factor))
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
            let c0 := eadd flag (nativeKaratsuba cond inv)
            let c1 := nativeKaratsuba cond (eadd flag one)
            eadd (nativeKaratsuba p0 c0) (nativeKaratsuba p1 c1)
          else
            zero
        let fv0 := evalBusForm (forms0.getD t (emptyBusForm 0)) evals
        let fv1 := evalBusForm (forms1.getD t (emptyBusForm 0)) evals
        let fv2 := evalBusForm (forms2.getD t (emptyBusForm 0)) evals
        let formTerm := dot formPowers #[fv0, fv1, fv2]
        eadd acc (nativeKaratsuba (weights.getD t zero) (eadd summand formTerm)))
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
        eadd acc (nativeKaratsuba functional (product.getD c zero)))
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
        eadd acc (nativeKaratsuba (segEq.getD seg zero) wSum))
      zero
  let muSum := Model.KeccakGkr.sumSlice claim.mu
  if !Spec.Vm.wordBEq (eadd projected (nativeKaratsuba iota muSum)) claim.value then
    none
  else
    let (seed, s) := Spec.Transcript.verifierSample s
    let mu := Model.KeccakGkr.instanceWeights seed
    let kappa := Model.KeccakGkr.sumSlice mu
    let value0 := polyEval product seed
    let (point, value1, scale, s) ←
      (Array.range claim.point.size).foldlM
        (fun (pts, curVal, curScale, curS) idx => do
          let r := claim.point.getD idx zero
          let (msg, s1) ← sumcheckRoundPolyFast curS 2 curVal (some r)
          let (ch, s2) := Spec.Transcript.verifierSample s1
          let factor := eadd (eadd one r) ch
          some (pts.push ch, nativeKaratsuba factor (polyEval msg ch), nativeKaratsuba curScale factor, s2))
        (#[], value0, one, s)
    let (localPt, value2, s) ← sumcheckPlain s 3 Spec.KeccakGkr.localBits value1
    let (t, s) ← Spec.Transcript.nextScalars 3 s
    let eqLocal := eqKernel localPt
    let wDot := dot (eqLocal.extract 0 Spec.KeccakGkr.bitCount) claim.weights
    let t0 := t.getD 0 zero
    let t1 := t.getD 1 zero
    let t2 := t.getD 2 zero
    let chiVal := eadd (nativeKaratsuba kappa t0) (nativeKaratsuba (eadd kappa t1) t2)
    if !Spec.Vm.wordBEq (nativeKaratsuba (nativeKaratsuba scale wDot) chiVal) value2 then
      none
    else
      let (beta, s) := Spec.Transcript.verifierSample s
      let rawWeights :=
        (Array.range Spec.KeccakGkr.bitCount).map fun j =>
          eadd (eqLocal.getD j zero)
            (nativeKaratsuba beta
              (eadd (eqLocal.getD (Spec.KeccakGkr.along j 4) zero)
                (nativeKaratsuba beta (eqLocal.getD (Spec.KeccakGkr.along j 3) zero))))
      let nextVal := eadd t0 (nativeKaratsuba beta (eadd t1 (nativeKaratsuba beta t2)))
      some (⟨nextVal, mu, point, Model.KeccakGkr.linearTranspose rawWeights⟩, s)

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
              (nativeKaratsuba (segEq.getD seg zero) (claim.weights.getD j zero))))
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
            eadd a (nativeKaratsuba ch (eadd a b)))
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
        nativeMulBase (lanes.getD (j / Spec.KeccakGkr.wordBits) zero)
          ((1 : UInt64) <<< UInt64.ofNat (j % Spec.KeccakGkr.wordBits))
    let last := nativeKaratsuba ((eqKernel segment).getD (segs - 1) zero) (dot (lanes.extract 0 stateLanes) output)
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
        if !Spec.Vm.wordBEq (nativeKaratsuba (rowWeights.getD 0 zero) word) val then
          none
        else
          some (some (Spec.KeccakGkr.WordOpening.mk (inst ++ slot) word), s2)
      else
        some (none, s)
    let (low, val1, s) ← sumcheckPlain s 2 Spec.KeccakGkr.packBits claim.value
    let (slot, rowWeights, val2, s) ← openSlot logSteps claim 0 segs val1 s
    let (slices, s) ← Spec.Transcript.nextScalars Spec.KeccakGkr.wordBits s
    let muEval ← multilinearEvalE claim.mu low
    if !Spec.Vm.wordBEq (nativeKaratsuba muEval (dot rowWeights slices)) val2 then
      none
    else
      let packVars := logSteps - Spec.KeccakGkr.packBits
      let inPoint := low ++ claim.point.extract 0 packVars ++ slot
      some (⟨outputs, ⟨inPoint, slices⟩⟩, s)

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
      if !Model.Layout.validateSizes logMemory bc.logBytecode logInvRate tableRows then
        none
      else
        let lay := Model.Layout.buildPublicLayout logMemory bc.logBytecode tableRows
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
            #[⟨memLo, publicPoint, interpK first.c0 second.c0 publicChallenge⟩,
              ⟨memHi, publicPoint, interpK first.c1 second.c1 publicChallenge⟩,
              ⟨memTop, publicPoint, interpK first.c2 second.c2 publicChallenge⟩]
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
            Model.Pcs.Whir.verifyRingSwitchAndStacked s root lay.shape.mu lay.placed logInvRate
              qkStack openings.inputs.point openings.inputs.slices placedClaims
          let paths ← Spec.Transcript.finish s
          some ⟨logMemory, tableRows, logInvRate, bus.bytecodePoint, paths⟩

def verifyEthereumProof (guest : PreparedBytecode) (seed : E × E)
    (eth : Spec.Aggregate.Wire.EthereumProof) : Bool :=
  if !Model.Aggregate.Wire.signerSetOk eth.claims then
    false
  else
    match evalBytecodeFast guest eth.defer.bytecodePoint with
    | none => false
    | some expected =>
      if !Spec.Vm.wordBEq eth.defer.bytecodeValue expected then
        false
      else
        let pi := statementBytes (Model.Aggregate.Wire.EthereumProof.statement seed eth)
        (verifyExecution guest pi eth.proof).isSome

def verifyEthereumBytes (guest : PreparedBytecode) (seed : E × E)
    (bytes : ByteArray) : Bool :=
  match Model.Aggregate.Wire.EthereumProof.fromBytes bytes zero with
  | none => false
  | some raw =>
    match evalBytecodeFast guest raw.defer.bytecodePoint with
    | none => false
    | some val =>
      let eth : Spec.Aggregate.Wire.EthereumProof :=
        { raw with defer := { raw.defer with bytecodeValue := val } }
      verifyEthereumProof guest seed eth

def verifyEthereumBytesWithoutPubkeys (guest : PreparedBytecode) (seed : E × E)
    (claims : Spec.Aggregate.Wire.SignatureClaims) (bytes : ByteArray) : Bool :=
  match Model.Aggregate.Wire.EthereumProof.fromBytesWithoutPubkeys bytes claims zero with
  | none => false
  | some raw =>
    match evalBytecodeFast guest raw.defer.bytecodePoint with
    | none => false
    | some val =>
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

end LeanVmXmss.Model.Aggregate.Verify
