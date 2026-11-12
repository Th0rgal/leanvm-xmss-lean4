import Model.Bus.Batch

namespace LeanVmXmss.Model.Bus

open Spec.Field (K E zero one)
open Spec.Layout
open Spec.Witness
open Model.Pcs.Ntt (foldRange foldRangeLoop)
open Model.Field

@[inline] def interpFlat (lo hi t : E) : E :=
  planarEadd lo (planarEmul t (planarEadd lo hi))

@[inline] def interpKFlat (lo hi : K) (t : E) : E :=
  planarEadd (Spec.Field.embed lo) (planarMulBase t (add lo hi))

def shrinkEqHighFlat (eqr : Array E) : Array E :=
  let half := eqr.size / 2
  parReduce16 2048 half
    (fun base len =>
      foldRangeLoop
        (fun acc i => acc.push (planarEadd (eqr[i]?.getD zero) (eqr[i + half]?.getD zero)))
        len base (Array.emptyWithCapacity len))
    Array.append

def shrinkEqLowFlat (eqr : Array E) : Array E :=
  let half := eqr.size / 2
  parReduce16 2048 half
    (fun base len =>
      foldRangeLoop
        (fun acc i => acc.push (planarEadd (eqr[2 * i]?.getD zero) (eqr[2 * i + 1]?.getD zero)))
        len base (Array.emptyWithCapacity len))
    Array.append

def eqTableExpandArray (cur : @& Array E) (rk : E) (half : Nat) : Array E :=
  let loPart := parReduce16 2048 half
    (fun base len =>
      foldRangeLoop
        (fun acc j =>
          let lo := cur[j]?.getD zero
          acc.push (planarEadd lo (planarEmul lo rk)))
        len base (Array.emptyWithCapacity len))
    Array.append
  let hiPart := parReduce16 2048 half
    (fun base len =>
      foldRangeLoop
        (fun acc j =>
          let lo := cur[j]?.getD zero
          acc.push (planarEmul lo rk))
        len base (Array.emptyWithCapacity len))
    Array.append
  loPart ++ hiPart

def eqTableArrayFlat (r : @& Array E) : Array E :=
  foldRange r.size
    (fun cur i => eqTableExpandArray cur (r[i]?.getD zero) (1 <<< i))
    #[one]

def eqTableFlat (r : Array E) : PlanarE :=
  encodePlanarE (eqTableArrayFlat r)

def mleEvalWithEqFlat (table : @& Array K) (eqs : @& Array E) : E :=
  parReduce16 2048 eqs.size
    (fun base len =>
      foldRangeLoop
        (fun acc z => planarEadd acc (planarMulBase (eqs[z]?.getD zero) (table[z]?.getD 0)))
        len base zero)
    planarEadd

def buildSideLeavesFlat (gpows : @& Array K) (blocks : @& Array Block) (lay : @& BusLayout)
    (cols bcCols : @& Array (Array K)) (w : @& Array E) (beta : E) : Array E :=
  let totalLen := max 1 (foldRange blocks.size
    (fun acc b => acc + (1 <<< (blocks[b]?.map Block.kappa |>.getD 0))) 0)
  let init := Array.replicate totalLen one
  foldRange blocks.size
    (fun leaves b =>
      match blocks[b]? with
      | none => leaves
      | some blk =>
        let off := lay.offsets[b]?.getD 0
        let blockVals := parReduce16 1024 blk.rows
          (fun base len =>
            foldRangeLoop
              (fun out z =>
                let val := foldRange blk.coords.size
                  (fun acc i =>
                    let c := blk.coords[i]?.getD (cConst 0)
                    let wi := w[i]?.getD zero
                    planarEadd acc (planarMulBase wi (evalCoord gpows cols bcCols z c)))
                  beta
                out.push val)
              len base (Array.emptyWithCapacity len))
          Array.append
        foldRange blk.rows
          (fun cur z => cur.setIfInBounds (off + z) (blockVals[z]?.getD one))
          leaves)
    init

def nextLevelFlat (current : @& Array E) : Array E :=
  let fullRows := current.size / 4
  let full := parReduce16 1024 fullRows
    (fun base len =>
      foldRangeLoop
        (fun acc row =>
          let c0 := current[4 * row]?.getD one
          let c1 := current[4 * row + 1]?.getD one
          let c2 := current[4 * row + 2]?.getD one
          let c3 := current[4 * row + 3]?.getD one
          acc.push (planarEmul (planarEmul c0 c1) (planarEmul c2 c3)))
        len base (Array.emptyWithCapacity len))
    Array.append
  if 4 * fullRows < current.size then
    let c0 := current[4 * fullRows]?.getD one
    let c1 := current[4 * fullRows + 1]?.getD one
    let c2 := current[4 * fullRows + 2]?.getD one
    let c3 := current[4 * fullRows + 3]?.getD one
    full.push (planarEmul (planarEmul c0 c1) (planarEmul c2 c3))
  else
    full

def buildLayersFlat (leaves : Array E) (mu : Nat) : Array (Array E) :=
  let init := (Array.replicate (mu + 1) #[]).setIfInBounds 0 leaves
  let (layers, level) := foldRange (mu / 2)
    (fun (cur, lvl) _ =>
      let next := nextLevelFlat (cur[lvl]?.getD #[])
      let lvl' := lvl + 2
      (cur.setIfInBounds lvl' next, lvl'))
    (init, 0)
  if level < mu then
    let below := layers[level]?.getD #[]
    let root :=
      if below.size ≤ 1 then below[0]?.getD one
      else planarEmul (below[0]?.getD one) (below[1]?.getD one)
    layers.setIfInBounds mu #[root]
  else
    layers

@[inline] def quarticSummandFlat (g0 s0 g1 s1 g2 s2 g3 s3 eqWeight : E) : E × E × E × E :=
  let a0 := planarEmul eqWeight g0
  let d0 := planarEmul eqWeight s0
  let right0 := planarEmul g2 g3
  let right2 := planarEmul s2 s3
  let left0 := planarEmul a0 g1
  let left2 := planarEmul d0 s1
  let leftAtOne := planarEmul (planarEadd a0 d0) (planarEadd g1 s1)
  let rightAtOne := planarEmul (planarEadd g2 s2) (planarEadd g3 s3)
  let left1 := planarEadd leftAtOne (planarEadd left0 left2)
  let right1 := planarEadd rightAtOne (planarEadd right0 right2)
  let c0 := planarEmul left0 right0
  let c4 := planarEmul left2 right2
  let middle := planarEmul left1 right1
  let atOne := planarEmul leftAtOne rightAtOne
  let crossEven := planarEmul (planarEadd left0 left2) (planarEadd right0 right2)
  let crossHigh := planarEmul (planarEadd left1 left2) (planarEadd right1 right2)
  (planarEadd c0 atOne, planarEadd (planarEadd crossEven c0) (planarEadd c4 middle),
    planarEadd crossHigh (planarEadd middle c4), c4)

@[inline] def addMsg4Flat (a b : E × E × E × E) : E × E × E × E :=
  (planarEadd a.1 b.1, planarEadd a.2.1 b.2.1,
   planarEadd a.2.2.1 b.2.2.1, planarEadd a.2.2.2 b.2.2.2)

def treeRoundMessageFlat (values eqWeights : @& Array E) : E × E × E × E :=
  let storedRows := values.size / 4
  let fullPairs := storedRows / 2
  let msg := parReduce16 512 fullPairs
    (fun base len =>
      foldRangeLoop
        (fun acc pair =>
          let lo := 8 * pair
          let hi := lo + 4
          let g0 := values[lo]?.getD one
          let g1 := values[lo + 1]?.getD one
          let g2 := values[lo + 2]?.getD one
          let g3 := values[lo + 3]?.getD one
          let s0 := planarEadd g0 (values[hi]?.getD one)
          let s1 := planarEadd g1 (values[hi + 1]?.getD one)
          let s2 := planarEadd g2 (values[hi + 2]?.getD one)
          let s3 := planarEadd g3 (values[hi + 3]?.getD one)
          let w := eqWeights[pair]?.getD zero
          addMsg4Flat acc (quarticSummandFlat g0 s0 g1 s1 g2 s2 g3 s3 w))
        len base (zero, zero, zero, zero))
    addMsg4Flat
  if storedRows % 2 = 1 then
    let lo := 8 * fullPairs
    let g0 := values[lo]?.getD one
    let g1 := values[lo + 1]?.getD one
    let g2 := values[lo + 2]?.getD one
    let g3 := values[lo + 3]?.getD one
    let w := eqWeights[fullPairs]?.getD zero
    addMsg4Flat msg (quarticSummandFlat g0 (planarEadd g0 one) g1 (planarEadd g1 one)
      g2 (planarEadd g2 one) g3 (planarEadd g3 one) w)
  else
    msg

def foldTreeFlat (values : @& Array E) (challenge : E) : Array E :=
  let storedRows := values.size / 4
  let fullRows := storedRows / 2
  let folded := parReduce16 512 fullRows
    (fun base len =>
      foldRangeLoop
        (fun acc row =>
          let lo := 8 * row
          let v0 := values[lo]?.getD one
          let v1 := values[lo + 1]?.getD one
          let v2 := values[lo + 2]?.getD one
          let v3 := values[lo + 3]?.getD one
          let h0 := values[lo + 4]?.getD one
          let h1 := values[lo + 5]?.getD one
          let h2 := values[lo + 6]?.getD one
          let h3 := values[lo + 7]?.getD one
          let acc := acc.push (interpFlat v0 h0 challenge)
          let acc := acc.push (interpFlat v1 h1 challenge)
          let acc := acc.push (interpFlat v2 h2 challenge)
          acc.push (interpFlat v3 h3 challenge))
        len base (Array.emptyWithCapacity (4 * len)))
    Array.append
  if storedRows % 2 = 1 then
    let lo := 8 * fullRows
    let v0 := values[lo]?.getD one
    let v1 := values[lo + 1]?.getD one
    let v2 := values[lo + 2]?.getD one
    let v3 := values[lo + 3]?.getD one
    let folded := folded.push (interpFlat v0 one challenge)
    let folded := folded.push (interpFlat v1 one challenge)
    let folded := folded.push (interpFlat v2 one challenge)
    folded.push (interpFlat v3 one challenge)
  else
    folded

def combineMsg4Flat (lambda : E) (m0 m1 m2 : E × E × E × E) : Array E :=
  let c0 := planarEadd m0.1 (planarEmul lambda (planarEadd m1.1 (planarEmul lambda m2.1)))
  let c2 := planarEadd m0.2.1 (planarEmul lambda (planarEadd m1.2.1 (planarEmul lambda m2.2.1)))
  let c3 := planarEadd m0.2.2.1
    (planarEmul lambda (planarEadd m1.2.2.1 (planarEmul lambda m2.2.2.1)))
  let c4 := planarEadd m0.2.2.2
    (planarEmul lambda (planarEadd m1.2.2.2 (planarEmul lambda m2.2.2.2)))
  let c1 := planarEadd (planarEadd c0 c2) (planarEadd c3 c4)
  #[c1, c2, c3, c4]

def treeRoundFoldFlat (lambda : E) (point : @& Array E) (roundCount : Nat)
    (t0 t1 t2 : Array E) (curPs : ProverState) :
    Array E × Array E × Array E × Array E × ProverState :=
  let eqW0 := eqTableArrayFlat (point.extract 1 point.size)
  let (_, s0, s1, s2, rp, pState) := foldRange roundCount
    (fun (eqW, s0, s1, s2, rp, pState) _ =>
      let m0 := treeRoundMessageFlat s0 eqW
      let m1 := treeRoundMessageFlat s1 eqW
      let m2 := treeRoundMessageFlat s2 eqW
      let coeffs := combineMsg4Flat lambda m0 m1 m2
      let pState := addScalars pState coeffs
      let (ch, pState) := sampleChallenge pState
      (shrinkEqLowFlat eqW, foldTreeFlat s0 ch, foldTreeFlat s1 ch, foldTreeFlat s2 ch,
        rp.push ch, pState))
    (eqW0, t0, t1, t2, Array.emptyWithCapacity roundCount, curPs)
  (s0, s1, s2, rp, pState)

def proveProductTripleFlat (leaves0 leaves1 leaves2 : Array E) (mu : Nat)
    (ps : ProverState) : ProductTriple × ProverState :=
  let t1 := Task.spawn (fun _ => buildLayersFlat leaves1 mu)
  let t2 := Task.spawn (fun _ => buildLayersFlat leaves2 mu)
  let layers0 := buildLayersFlat leaves0 mu
  let layers1 := t1.get
  let layers2 := t2.get
  let r0 := (layers0[mu]?.getD #[])[0]?.getD one
  let r1 := (layers1[mu]?.getD #[])[0]?.getD one
  let r2 := (layers2[mu]?.getD #[])[0]?.getD one
  let ps := addScalar (addScalar ps r0) r2
  let steps := (mu + 1) / 2
  let loop := Nat.rec
    (motive := fun _ => Nat → Array E → Array E → ProverState →
      Array E × Array E × ProverState)
    (fun _ point values curPs => (point, values, curPs))
    (fun _ prev layer point values curPs =>
      if layer = 0 then (point, values, curPs)
      else
        let (lambda, curPs) := sampleChallenge curPs
        if layer % 2 = 1 then
          let b0 := layers0[layer - 1]?.getD #[]
          let b1 := layers1[layer - 1]?.getD #[]
          let b2 := layers2[layer - 1]?.getD #[]
          let l0 := b0[0]?.getD one
          let h0 := if b0.size ≥ 2 then b0[1]?.getD one else one
          let l1 := b1[0]?.getD one
          let h1 := if b1.size ≥ 2 then b1[1]?.getD one else one
          let l2 := b2[0]?.getD one
          let h2 := if b2.size ≥ 2 then b2[1]?.getD one else one
          let curPs := addScalars curPs #[l0, h0, l1, h1, l2, h2]
          let (ch, curPs) := sampleChallenge curPs
          let nextVals := #[interpFlat l0 h0 ch, interpFlat l1 h1 ch, interpFlat l2 h2 ch]
          prev (layer - 1) #[ch] nextVals curPs
        else
          let roundCount := mu - layer
          let t0 := padFourMultiple (layers0[layer - 2]?.getD #[])
          let t1 := padFourMultiple (layers1[layer - 2]?.getD #[])
          let t2 := padFourMultiple (layers2[layer - 2]?.getD #[])
          let (t0, t1, t2, roundPoint, curPs) :=
            treeRoundFoldFlat lambda point roundCount t0 t1 t2 curPs
          let ch0 := treeChildren t0
          let ch1 := treeChildren t1
          let ch2 := treeChildren t2
          let curPs := addScalars (addScalars (addScalars curPs ch0) ch1) ch2
          let (lowCh, curPs) := sampleChallenge curPs
          let (highCh, curPs) := sampleChallenge curPs
          let evalQuad (ch : Array E) : E :=
            interpFlat (interpFlat (ch[0]?.getD one) (ch[1]?.getD one) lowCh)
              (interpFlat (ch[2]?.getD one) (ch[3]?.getD one) lowCh) highCh
          let nextVals := #[evalQuad ch0, evalQuad ch1, evalQuad ch2]
          let nextPoint := #[lowCh, highCh] ++ roundPoint
          prev (layer - 2) nextPoint nextVals curPs)
    steps
  let (point, values, ps') := loop mu #[] #[r0, r1, r2] ps
  (⟨point, values⟩, ps')

def decomposeNoneCoordsFlat (gpows : @& Array K) (blk : @& Block)
    (cols bcCols : @& Array (Array K)) (zetaLo w eqZetaLo : @& Array E)
    (curClaims : Array ColumnClaim) (curPs : ProverState) :
    E × Array ColumnClaim × ProverState :=
  foldRange blk.coords.size
    (fun (inAcc, cAcc, pAcc) i =>
      let wi := w[i]?.getD zero
      match blk.coords[i]?.getD (cConst 0) with
      | .atom (.const v) =>
        (planarEadd inAcc (planarMulBase wi v), cAcc, pAcc)
      | .index =>
        (planarEadd inAcc (planarEmul wi (indexMle zetaLo)), cAcc, pAcc)
      | .publicCol slot =>
        let val := mleEvalWithEqFlat (bcCols[slot]?.getD #[]) eqZetaLo
        (planarEadd inAcc (planarEmul wi val), cAcc, pAcc)
      | .atom (.col colIdx) =>
        match findKnownClaim cAcc colIdx zetaLo with
        | some v => (planarEadd inAcc (planarEmul wi v), cAcc, pAcc)
        | none =>
          let v := mleEvalWithEqFlat (cols[colIdx]?.getD #[]) eqZetaLo
          let pAcc' := addScalar pAcc v
          let cAcc' := cAcc.push ⟨colIdx, zetaLo, v⟩
          (planarEadd inAcc (planarEmul wi v), cAcc', pAcc')
      | .atom (.gcol colIdx k) =>
        let (v, cAcc', pAcc') :=
          match findKnownClaim cAcc colIdx zetaLo with
          | some v => (v, cAcc, pAcc)
          | none =>
            let v := mleEvalWithEqFlat (cols[colIdx]?.getD #[]) eqZetaLo
            (v, cAcc.push ⟨colIdx, zetaLo, v⟩, addScalar pAcc v)
        let gv := planarMulBase v (Model.Layout.gAt gpows k)
        (planarEadd inAcc (planarEmul wi gv), cAcc', pAcc')
      | _ => (inAcc, cAcc, pAcc))
    (zero, curClaims, curPs)

def decomposeSideFoldFlat (gpows : @& Array K) (blocks : @& Array Block) (lay : @& BusLayout)
    (cols bcCols : @& Array (Array K)) (zeta w : @& Array E) (beta : E)
    (forms : Array BusForm) (claims : Array ColumnClaim)
    (ps : ProverState) : E × E × Array BusForm × Array ColumnClaim × ProverState :=
  let mu := lay.mu
  foldRange blocks.size
    (fun (acc, selSum, curForms, curClaims, curPs) b =>
      match blocks[b]? with
      | none => (acc, selSum, curForms, curClaims, curPs)
      | some blk =>
        let kappa := blk.kappa
        let zetaLo := zeta.extract 0 kappa
        let zetaHi := zeta.extract kappa mu
        let sel := (lay.offsets[b]?.getD 0) >>> kappa
        let selBits := selectorPoint sel (mu - kappa)
        let eqHi := eqEval selBits zetaHi
        let selSum' := planarEadd selSum eqHi
        match blk.owner with
        | some t =>
          let base := tableBase t
          let form0 := curForms[t.val]?.getD (emptyBusForm (tableWidth t))
          let ⟨coeffs0, prods0, const0⟩ := form0
          let form1 : BusForm := ⟨coeffs0, prods0, planarEadd const0 (planarEmul eqHi beta)⟩
          let form2 := foldRange blk.coords.size
            (fun f i =>
              let c := blk.coords[i]?.getD (cConst 0)
              let wi := w[i]?.getD zero
              accumulateCoord gpows base (planarEmul eqHi wi) f c)
            form1
          let phiPad := foldRange blk.padding.size
            (fun pAcc i =>
              let v := blk.padding[i]?.getD 0
              let wi := w[i]?.getD zero
              planarEadd pAcc (planarMulBase wi v))
            beta
          let padTerm := planarEmul (planarEmul eqHi (paddingWeight zetaLo blk.rows))
            (planarEadd one phiPad)
          (planarEadd acc padTerm, selSum', curForms.setIfInBounds t.val form2, curClaims, curPs)
        | none =>
          let eqZetaLo := eqTableArrayFlat zetaLo
          let (inner, nextClaims, nextPs) :=
            decomposeNoneCoordsFlat gpows blk cols bcCols zetaLo w eqZetaLo curClaims curPs
          let blockVal := planarEmul eqHi (planarEadd beta inner)
          (planarEadd acc blockVal, selSum', curForms, nextClaims, nextPs))
    (zero, zero, forms, claims, ps)

def decomposeSideFlat (gpows : @& Array K) (blocks : @& Array Block) (lay : @& BusLayout)
    (cols bcCols : @& Array (Array K)) (zeta w : @& Array E) (beta : E)
    (forms : Array BusForm) (claims : Array ColumnClaim)
    (ps : ProverState) : E × Array BusForm × Array ColumnClaim × ProverState :=
  let (acc, selSum, forms, claims, ps) :=
    decomposeSideFoldFlat gpows blocks lay cols bcCols zeta w beta forms claims ps
  (planarEadd acc (planarEadd one selSum), forms, claims, ps)

def computeTableSigmasFlat (cols : @& Array (Array K)) (taus : @& Array Nat)
    (forms0 forms1 forms2 : @& Array BusForm) (zeta : @& Array E) :
    Array E × Array E × Array E :=
  let init0 := Array.emptyWithCapacity nTables
  let init1 := Array.emptyWithCapacity nTables
  let init2 := Array.emptyWithCapacity nTables
  foldRange nTables
    (fun (s0, s1, s2) t =>
      if h : t < nTables then
        let tf : Fin nTables := ⟨t, h⟩
        let base := tableBase tf
        let nCols := tableWidth tf
        let tau := taus[t]?.getD 0
        let zetaTau := zeta.extract 0 tau
        let eqs := eqTableArrayFlat zetaTau
        let colEvals := parReduce16 2 nCols
          (fun b l =>
            foldRangeLoop
              (fun acc c => acc.push (mleEvalWithEqFlat (cols[base + c]?.getD #[]) eqs))
              l b (Array.emptyWithCapacity l))
          Array.append
        let f0 := forms0[t]?.getD (emptyBusForm nCols)
        let f1 := forms1[t]?.getD (emptyBusForm nCols)
        let f2 := forms2[t]?.getD (emptyBusForm nCols)
        let collectPairs (pairs : Array (Nat × Nat)) (f : BusForm) : Array (Nat × Nat) :=
          foldRange f.prods.size
            (fun cur idx =>
              match f.prods[idx]? with
              | none => cur
              | some p => if hasPair cur p.colA p.colB then cur else cur.push (p.colA, p.colB))
            pairs
        let pairs := collectPairs (collectPairs (collectPairs #[] f0) f1) f2
        let prodSums := parReduce16 2 pairs.size
          (fun b l =>
            foldRangeLoop
              (fun acc idx =>
                match pairs[idx]? with
                | none => acc
                | some (a, bCol) =>
                  let colA := cols[base + a]?.getD #[]
                  let colB := cols[base + bCol]?.getD #[]
                  let sum := parReduce16 2048 eqs.size
                    (fun zb zl =>
                      foldRangeLoop
                        (fun s z =>
                          let prodK := nativeMul (colA[z]?.getD 0) (colB[z]?.getD 0)
                          planarEadd s (planarMulBase (eqs[z]?.getD zero) prodK))
                        zl zb zero)
                    planarEadd
                  acc.push (a, bCol, sum))
              l b (Array.emptyWithCapacity l))
          Array.append
        (s0.push (evalBusFormSigma f0 colEvals prodSums),
          s1.push (evalBusFormSigma f1 colEvals prodSums),
          s2.push (evalBusFormSigma f2 colEvals prodSums))
      else
        (s0, s1, s2))
    (init0, init1, init2)

def proveBalanceFlat (gpows : Array K) (lay : Model.Layout.PublicLayout)
    (cols bcCols : Array (Array K)) (ps : ProverState) : BusProof × ProverState :=
  let (alphas, ps) := sampleVec ps busBits
  let w := fingerprintWeights alphas
  let cw := countWeights
  let (beta, ps) := sampleChallenge ps
  let mu := lay.pushLayout.mu
  let countLay : BusLayout := { lay.countLayout with mu := mu }
  let t1 := Task.spawn (fun _ => buildSideLeavesFlat gpows lay.pull lay.pullLayout cols bcCols w beta)
  let t2 := Task.spawn (fun _ => buildSideLeavesFlat gpows lay.count countLay cols bcCols cw zero)
  let leaves0 := buildSideLeavesFlat gpows lay.push lay.pushLayout cols bcCols w beta
  let leaves1 := t1.get
  let leaves2 := t2.get
  let (gkr, ps) := proveProductTripleFlat leaves0 leaves1 leaves2 mu ps
  let zeta := gkr.point
  let (_, forms0, claims, ps) := decomposeSideFlat gpows lay.push lay.pushLayout cols bcCols
    zeta w beta initTableForms #[] ps
  let (_, forms1, claims, ps) := decomposeSideFlat gpows lay.pull lay.pullLayout cols bcCols
    zeta w beta initTableForms claims ps
  let (_, forms2, claims, ps) := decomposeSideFlat gpows lay.count countLay cols bcCols
    zeta cw zero initTableForms claims ps
  let (sigmas0, sigmas1, sigmas2) :=
    computeTableSigmasFlat cols lay.taus forms0 forms1 forms2 zeta
  (⟨claims, zeta, forms0, forms1, forms2, sigmas0, sigmas1, sigmas2⟩, ps)

@[inline] def evalLinKFlat (terms : @& Array (Nat × E)) (cols : @& Array (Array K))
    (base row : Nat) : E :=
  foldRange terms.size
    (fun acc idx =>
      match terms[idx]? with
      | none => acc
      | some (c, w) =>
        planarEadd acc (planarMulBase w ((cols[base + c]?.getD #[])[row]?.getD 0)))
    zero

@[inline] def evalLinSumKFlat (terms : @& Array (Nat × E)) (cols : @& Array (Array K))
    (base i half : Nat) : E :=
  foldRange terms.size
    (fun acc idx =>
      match terms[idx]? with
      | none => acc
      | some (c, w) =>
        let col := cols[base + c]?.getD #[]
        let s := add (col[i]?.getD 0) (col[i + half]?.getD 0)
        planarEadd acc (planarMulBase w s))
    zero

def tableMessageKFlat (gf : @& GroupedForm) (cols : @& Array (Array K))
    (base : Nat) (eqr : @& Array E) (half : Nat) (atOne : Bool) : E × E :=
  let (endAcc, slopeAcc) := parReduce16 512 half
    (fun rowBase rowLen =>
      foldRangeLoop
        (fun (eAcc, sAcc) i =>
          let endIdx := if atOne then i + half else i
          let linEnd := evalLinKFlat gf.lin cols base endIdx
          let (ep, sl) := foldRange gf.groups.size
            (fun (epG, slG) g =>
              match gf.groups[g]? with
              | none => (epG, slG)
              | some (left, right) =>
                let leftCol := cols[base + left]?.getD #[]
                let leftEnd := leftCol[endIdx]?.getD 0
                let leftSum := add (leftCol[i]?.getD 0) (leftCol[i + half]?.getD 0)
                let rightEnd := evalLinKFlat right cols base endIdx
                let rightSum := evalLinSumKFlat right cols base i half
                (planarEadd epG (planarMulBase rightEnd leftEnd),
                  planarEadd slG (planarMulBase rightSum leftSum)))
            (linEnd, zero)
          let eqw := eqr[i]?.getD zero
          (planarEadd eAcc (planarEmul eqw ep), planarEadd sAcc (planarEmul eqw sl)))
        rowLen rowBase (zero, zero))
    (fun (a0, a1) (b0, b1) => (planarEadd a0 b0, planarEadd a1 b1))
  (planarEadd endAcc gf.constant, slopeAcc)

def joinTableStateFlat (gf : @& GroupedForm) (cols : @& Array (Array K))
    (base : Nat) (r : E) (half : Nat) : Array (Array E) :=
  let buildLinCol (terms : Array (Nat × E)) : Array E :=
    parReduce16 512 half
      (fun rowBase rowLen =>
        foldRangeLoop
          (fun col i =>
            let v := foldRange terms.size
              (fun acc idx =>
                match terms[idx]? with
                | none => acc
                | some (c, w) =>
                  let kc := cols[base + c]?.getD #[]
                  let lo := kc[i]?.getD 0
                  let hi := kc[i + half]?.getD 0
                  let wr := planarEmul w r
                  planarEadd acc (planarEadd (planarMulBase w lo) (planarMulBase wr (add lo hi))))
              zero
            col.push v)
          rowLen rowBase (Array.emptyWithCapacity rowLen))
      Array.append
  let initCols := #[buildLinCol gf.lin]
  foldRange gf.groups.size
    (fun stateCols g =>
      match gf.groups[g]? with
      | none => stateCols
      | some (left, right) =>
        let kc := cols[base + left]?.getD #[]
        let leftCol := parReduce16 512 half
          (fun rowBase rowLen =>
            foldRangeLoop
              (fun col i => col.push (interpKFlat (kc[i]?.getD 0) (kc[i + half]?.getD 0) r))
              rowLen rowBase (Array.emptyWithCapacity rowLen))
          Array.append
        let rightCol := buildLinCol right
        (stateCols.push leftCol).push rightCol)
    initCols

def tableMessageEFlat (constant : E) (state : @& Array (Array E))
    (eqr : @& Array E) (half : Nat) (atOne : Bool) : E × E :=
  let nGroups := (state.size - 1) / 2
  let linCol := state[0]?.getD #[]
  let (eSum, sSum) := parReduce16 512 half
    (fun rowBase rowLen =>
      foldRangeLoop
        (fun (eAcc, sAcc) i =>
          let endIdx := if atOne then i + half else i
          let linEnd := linCol[endIdx]?.getD zero
          let (ep, sl) := foldRange nGroups
            (fun (epG, slG) g =>
              let lCol := state[1 + 2 * g]?.getD #[]
              let rCol := state[2 + 2 * g]?.getD #[]
              let lEnd := lCol[endIdx]?.getD zero
              let rEnd := rCol[endIdx]?.getD zero
              let lSum := planarEadd (lCol[i]?.getD zero) (lCol[i + half]?.getD zero)
              let rSum := planarEadd (rCol[i]?.getD zero) (rCol[i + half]?.getD zero)
              (planarEadd epG (planarEmul lEnd rEnd), planarEadd slG (planarEmul lSum rSum)))
            (linEnd, zero)
          let eqw := eqr[i]?.getD zero
          (planarEadd eAcc (planarEmul eqw ep), planarEadd sAcc (planarEmul eqw sl)))
        rowLen rowBase (zero, zero))
    (fun (a0, a1) (b0, b1) => (planarEadd a0 b0, planarEadd a1 b1))
  (planarEadd constant eSum, sSum)

def foldTableFlat (state : Array (Array E)) (r : E) (half : Nat) : Array (Array E) :=
  foldRange state.size
    (fun acc c =>
      let col := state[c]?.getD #[]
      let folded := parReduce16 512 half
        (fun rowBase rowLen =>
          foldRangeLoop
            (fun out i => out.push (interpFlat (col[i]?.getD zero) (col[i + half]?.getD zero) r))
            rowLen rowBase (Array.emptyWithCapacity rowLen))
        Array.append
      acc.push folded)
    (Array.emptyWithCapacity state.size)

def constraintsRoundMsgsFlat (airs : @& Array AirTable) (gForms : @& Array GroupedForm)
    (cols : @& Array (Array K)) (weights : @& Array E)
    (states : @& Array (Option (Array (Array E)))) (eqr : @& Array E)
    (m half : Nat) (atOne : Bool) : E × E :=
  foldRange airs.size
    (fun (m0, m1) t =>
      let tau := airs[t]?.map Spec.Bus.AirTable.tau |>.getD 0
      if m < tau then
        let wt := weights[t]?.getD one
        let gf := gForms[t]?.getD default
        let base := airs[t]?.map Spec.Bus.AirTable.base |>.getD 0
        let (p0, p1) :=
          match states[t]?.join with
          | some st => tableMessageEFlat gf.constant st eqr half atOne
          | none => tableMessageKFlat gf cols base eqr half atOne
        (planarEadd m0 (planarEmul wt p0), planarEadd m1 (planarEmul wt p1))
      else (m0, m1))
    (zero, zero)

def constraintsUpdateTablesFlat (airs : @& Array AirTable) (gForms : @& Array GroupedForm)
    (cols : @& Array (Array K)) (weights : Array E)
    (states : Array (Option (Array (Array E))))
    (m half : Nat) (rk eqK : E) : Array E × Array (Option (Array (Array E))) :=
  foldRange airs.size
    (fun (wAcc, sAcc) t =>
      let tau := airs[t]?.map Spec.Bus.AirTable.tau |>.getD 0
      let wt := wAcc[t]?.getD one
      if m < tau then
        let wAcc' := wAcc.setIfInBounds t (planarEmul wt eqK)
        let gf := gForms[t]?.getD default
        let base := airs[t]?.map Spec.Bus.AirTable.base |>.getD 0
        let nextSt :=
          match sAcc[t]?.join with
          | some st => some (foldTableFlat st rk half)
          | none => some (joinTableStateFlat gf cols base rk half)
        (wAcc', sAcc.setIfInBounds t nextSt)
      else
        (wAcc.setIfInBounds t (planarEmul wt rk), sAcc))
    (weights, states)

def constraintsRoundsFoldFlat (airs : @& Array AirTable) (gForms : @& Array GroupedForm)
    (cols : @& Array (Array K)) (zeta : @& Array E) (n : Nat)
    (eqr0 chi0 : Array E) (claim0 : E) (weights0 : Array E)
    (states0 : Array (Option (Array (Array E)))) (ps : ProverState) :
    Array E × Array E × E × E × (Array E × Array (Option (Array (Array E)))) × ProverState :=
  foldRange n
    (fun (eqr, chi, k, claim, weightsStates, curPs) j =>
      let (weights, states) := weightsStates
      let m := n - 1 - j
      let half := 1 <<< m
      let zm := zeta[m]?.getD zero
      let atOne := Spec.Vm.wordBEq zm zero
      let waiting := foldRange airs.size
        (fun acc t =>
          let tau := airs[t]?.map Spec.Bus.AirTable.tau |>.getD 0
          if tau ≤ m then planarEadd acc (airs[t]?.map Spec.Bus.AirTable.sigma |>.getD zero)
          else acc)
        zero
      let u := planarEmul k waiting
      let (msg0, msg1) :=
        constraintsRoundMsgsFlat airs gForms cols weights states eqr m half atOne
      let eqr' := shrinkEqHighFlat eqr
      let h := roundPolynomial msg0 msg1 zm claim u
      let curPs := addScalars curPs #[h[0]?.getD zero, h[2]?.getD zero, h[3]?.getD zero]
      let (rk, curPs) := sampleChallenge curPs
      let claim' := polyEval h rk
      let chi' := chi.setIfInBounds m rk
      let k' := planarEmul k rk
      let eqK := planarEadd (planarEadd one zm) rk
      let ws' := constraintsUpdateTablesFlat airs gForms cols weights states m half rk eqK
      (eqr', chi', k', claim', ws', curPs))
    (eqr0, chi0, one, claim0, (weights0, states0), ps)

def proveConstraintsFlat (airs : Array AirTable) (cols : Array (Array K))
    (zeta : Array E) (ps : ProverState) : Array TableClaims × ProverState :=
  let n := foldRange airs.size
    (fun acc t => max acc (airs[t]?.map Spec.Bus.AirTable.tau |>.getD 0)) 0
  let gForms := foldRange airs.size
    (fun acc t =>
      acc.push (buildGroupedForm (airs[t]?.map Spec.Bus.AirTable.form |>.getD (emptyBusForm 0))))
    (Array.emptyWithCapacity airs.size)
  let eqr0 := eqTableArrayFlat (zeta.extract 0 (n - 1))
  let chi0 := Array.replicate n zero
  let claim0 := foldRange airs.size
    (fun acc t => planarEadd acc (airs[t]?.map Spec.Bus.AirTable.sigma |>.getD zero)) zero
  let weights0 := Array.replicate airs.size one
  let states0 : Array (Option (Array (Array E))) := Array.replicate airs.size none
  let (_, chi, _, _, _, ps) :=
    constraintsRoundsFoldFlat airs gForms cols zeta n eqr0 chi0 claim0 weights0 states0 ps
  foldRange airs.size
    (fun (claimsAcc, curPs) t =>
      let tau := airs[t]?.map Spec.Bus.AirTable.tau |>.getD 0
      let base := airs[t]?.map Spec.Bus.AirTable.base |>.getD 0
      let nCols := airs[t]?.map Spec.Bus.AirTable.nCols |>.getD 0
      let chiT := chi.extract 0 tau
      let eqChiT := eqTableArrayFlat chiT
      let evals := parReduce16 2 nCols
        (fun b l =>
          foldRangeLoop
            (fun acc c => acc.push (mleEvalWithEqFlat (cols[base + c]?.getD #[]) eqChiT))
            l b (Array.emptyWithCapacity l))
        Array.append
      let curPs := addScalars curPs evals
      (claimsAcc.push ⟨chiT, evals⟩, curPs))
    (Array.emptyWithCapacity airs.size, ps)

def buildColumnsFlat (program : @& Array Spec.Vm.Op) (sized : @& SizedRun)
    (message : @& Array K) : Array (Array K) :=
  let steps := 1 <<< (sized.layout.taus[opKeccak]?.getD 0)
  let keccakRows := sized.trace.tables[opKeccak]?.getD #[]
  let zeroPerm := Model.Keccak.keccakF1600 Model.Layout.zeroState25
  let rowPerms := parReduce16 256 keccakRows.size
    (fun base len =>
      foldRangeLoop
        (fun out step =>
          let row := keccakRows[step]?.getD default
          out.push (Model.Keccak.keccakF1600 (inputState25 program sized.trace.memory row)))
        len base (Array.emptyWithCapacity len))
    Array.append
  let keccakOutCols := foldRange keccakRows.size
    (fun cols step =>
      let outState := rowPerms[step]?.getD zeroPerm
      foldRange stateLanes
        (fun cur lane =>
          cur.modify lane (fun col => col.setIfInBounds step (outState.toSpec[lane]?.getD 0)))
        cols)
    (foldRange stateLanes
      (fun acc lane => acc.push (Array.replicate steps (zeroPerm.toSpec[lane]?.getD 0)))
      (Array.emptyWithCapacity stateLanes))
  foldRange nColumns
    (fun acc col =>
      match keccakValue col with
      | some (.output lane) => acc.push (keccakOutCols[lane]?.getD #[])
      | _ =>
        match sized.layout.placements[col]?.join with
        | some place =>
          let len := 1 <<< place.variables
          acc.push (message.extract place.index (place.index + len))
        | none => acc.push #[])
    (Array.emptyWithCapacity nColumns)

def buildColumnsFlatWq (program : @& Array Spec.Vm.Op) (sized : @& SizedRun)
    (wq : @& ByteArray) (wins : @& Array (Array K)) : Array (Array K) :=
  let steps := 1 <<< (sized.layout.taus[opKeccak]?.getD 0)
  let keccakRows := sized.trace.tables[opKeccak]?.getD #[]
  let zeroPerm := Model.Keccak.keccakF1600 Model.Layout.zeroState25
  let rowPerms := parReduce16 256 keccakRows.size
    (fun base len =>
      foldRangeLoop
        (fun out step =>
          let row := keccakRows[step]?.getD default
          out.push (Model.Keccak.keccakF1600 (inputState25 program sized.trace.memory row)))
        len base (Array.emptyWithCapacity len))
    Array.append
  let keccakOutCols := foldRange keccakRows.size
    (fun cols step =>
      let outState := rowPerms[step]?.getD zeroPerm
      foldRange stateLanes
        (fun cur lane =>
          cur.modify lane (fun col => col.setIfInBounds step (outState.toSpec[lane]?.getD 0)))
        cols)
    (foldRange stateLanes
      (fun acc lane => acc.push (Array.replicate steps (zeroPerm.toSpec[lane]?.getD 0)))
      (Array.emptyWithCapacity stateLanes))
  foldRange nColumns
    (fun acc col =>
      match keccakValue col with
      | some (.output lane) => acc.push (keccakOutCols[lane]?.getD #[])
      | _ =>
        match sized.layout.placements[col]?.join with
        | some place =>
          let len := 1 <<< place.variables
          let src := wins[col]?.getD #[]
          if src.size >= len then acc.push (src.extract 0 len)
          else acc.push (Model.Witness.extractWordsWq wq place.index len)
        | none => acc.push #[])
    (Array.emptyWithCapacity nColumns)

def proveBusAndConstraintsFlat (program : Array Spec.Vm.Op) (iv : ByteArray)
    (publicInput : Array E) (bundle : WitnessBundle) : BusStageOutput :=
  let ps0 := startTranscript iv publicInput bundle.sized bundle.root
  let cols := buildColumnsFlat program bundle.sized bundle.message
  let bcCols := Model.Layout.bytecodeColumnsFast program
  let gpows := Model.Layout.gpowTable (maxBusGpowIndex program bundle.sized)
  let (bus, ps1) := proveBalanceFlat gpows bundle.sized.layout cols bcCols ps0
  let (xi, ps2) := sampleChallenge ps1
  let airs := buildAirs bundle.sized.layout.taus bus xi
  let (tableClaims, ps3) := proveConstraintsFlat airs cols bus.point ps2
  let (rPi, ps4) := sampleChallenge ps3
  let slots := finishClaims bundle.sized.layout publicInput bus.claims tableClaims rPi
  let outClaim := keccakOutputClaim tableClaims
  ⟨ps4, slots, outClaim⟩

end LeanVmXmss.Model.Bus
