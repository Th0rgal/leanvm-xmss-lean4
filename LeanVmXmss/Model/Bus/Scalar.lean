import Spec.Bus.Basic

namespace LeanVmXmss.Model.Bus

open Spec.Field (K E zero one)
open Spec.Layout
open Spec.Witness
open Model.Field
open Model.Pcs.Ntt (foldRange)
open Model.Transcript.Registers (Sponge)

instance : Inhabited Sponge := ⟨⟨Model.Layout.zeroState25, default, default, default, default, 0⟩⟩

structure ProverState where
  sponge : Sponge
  stream : Array E
  deriving Inhabited

def initProverState (iv : ByteArray) (publicInput : Array E) : ProverState :=
  { sponge := Model.Transcript.Registers.init iv (publicBytes publicInput), stream := #[] }

def addScalar (ps : ProverState) (x : E) : ProverState :=
  let ⟨sponge, stream⟩ := ps
  ⟨Model.Transcript.Registers.observe sponge x, stream.push x⟩

def addScalars (ps : ProverState) (xs : @& Array E) : ProverState :=
  foldRange xs.size (fun acc i => addScalar acc (xs[i]?.getD zero)) ps

def sampleChallenge (ps : ProverState) : E × ProverState :=
  let ⟨sponge, stream⟩ := ps
  let (ch, sponge') := Model.Transcript.Registers.sample sponge
  (ch, ⟨sponge', stream⟩)

def sampleVec (ps : ProverState) (n : Nat) : Array E × ProverState :=
  foldRange n
    (fun (acc, cur) _ =>
      let (ch, next) := sampleChallenge cur
      (acc.push ch, next))
    (Array.emptyWithCapacity n, ps)

def startTranscript (iv : ByteArray) (publicInput : Array E) (sized : @& SizedRun)
    (root : ByteArray) : ProverState :=
  let ps0 := initProverState iv publicInput
  let ps1 := addScalars ps0 (announceWords sized)
  let roots := Spec.Merkle.hashToScalars root
  addScalars ps1 #[roots.1, roots.2]

def nativeMulBase (a : E) (b : K) : E :=
  ⟨nativeMul a.c0 b, nativeMul a.c1 b, nativeMul a.c2 b⟩

def nativeEpow (x : E) (n : Nat) : E :=
  Spec.Field.powWith nativeKaratsuba one x n

def interp (lo hi t : E) : E :=
  eadd lo (nativeKaratsuba t (eadd lo hi))

def interpK (lo hi : K) (t : E) : E :=
  eadd (Spec.Field.embed lo) (nativeMulBase t (add lo hi))

def eqEval (r x : @& Array E) : E :=
  foldRange (min r.size x.size)
    (fun acc i =>
      let ri := r[i]?.getD zero
      let xi := x[i]?.getD zero
      nativeKaratsuba acc (eadd one (eadd ri xi)))
    one

def eqTable (r : @& Array E) : Array E :=
  let total := 1 <<< r.size
  let init := (Array.replicate total zero).setIfInBounds 0 one
  foldRange r.size
    (fun out i =>
      let rk := r[i]?.getD zero
      let half := 1 <<< i
      foldRange half
        (fun cur j =>
          let lo := cur[j]?.getD zero
          let p := nativeKaratsuba lo rk
          let cur1 := cur.setIfInBounds (half + j) p
          cur1.setIfInBounds j (eadd lo p))
        out)
    init

def shrinkEqHigh (eqr : Array E) : Array E :=
  Spec.Bus.shrinkEqHigh eqr

def mleEval (table : @& Array K) (point : @& Array E) : E :=
  let eqs := eqTable point
  foldRange eqs.size
    (fun acc z =>
      let eqz := eqs[z]?.getD zero
      let vz := table[z]?.getD 0
      eadd acc (nativeMulBase eqz vz))
    zero

def paddingWeight (point : @& Array E) (n : Nat) : E :=
  let bit (k : Nat) : E := Spec.Field.embed (UInt64.ofNat ((n >>> k) &&& 1))
  let low := foldRange point.size
    (fun pad k =>
      let r := point[k]?.getD zero
      let bk1 := eadd one (bit k)
      eadd (nativeKaratsuba bk1 r) (nativeKaratsuba (eadd bk1 r) pad))
    one
  nativeKaratsuba (eadd one (bit point.size)) low

def indexMle (zeta : @& Array E) : E :=
  let res := foldRange zeta.size
    (fun (acc, g2k) i =>
      let z := zeta[i]?.getD zero
      let factor := eadd one (nativeMulBase z (add 1 g2k))
      (nativeKaratsuba acc factor, nativeMul g2k g2k))
    (one, (2 : K))
  res.1

def polyEval (coeffs : @& Array E) (point : E) : E :=
  foldRange coeffs.size
    (fun acc step =>
      let c := coeffs[coeffs.size - 1 - step]?.getD zero
      eadd (nativeKaratsuba acc point) c)
    zero

def selectorPoint (sel len : Nat) : Array E :=
  Spec.Bus.selectorPoint sel len

def fingerprintWeights (alphas : @& Array E) : Array E :=
  let init := Array.replicate (1 <<< busBits) one
  foldRange busBits
    (fun w bit =>
      let a := alphas[bit]?.getD zero
      let a1 := eadd a one
      foldRange (1 <<< busBits)
        (fun cur x =>
          let factor := if ((x >>> bit) &&& 1) = 1 then a else a1
          cur.setIfInBounds x (nativeKaratsuba (cur[x]?.getD zero) factor))
        w)
    init

def countWeights : Array E :=
  fingerprintWeights (Array.replicate busBits zero)

def maxBusGpowIndex (program : @& Array Spec.Vm.Op) (sized : @& SizedRun) : Nat :=
  max (1 <<< sized.logMem) (max (1 <<< sized.logBytecode) (max (Model.Layout.maxProgramOffset program) 16))

def buildColumns (program : @& Array Spec.Vm.Op) (sized : @& SizedRun)
    (message : @& Array K) : Array (Array K) :=
  let steps := 1 <<< (sized.layout.taus[opKeccak]?.getD 0)
  let keccakRows := sized.trace.tables[opKeccak]?.getD #[]
  let zeroPerm := Model.Keccak.keccakF1600 Model.Layout.zeroState25
  let keccakOutCols := foldRange keccakRows.size
    (fun cols step =>
      let row := keccakRows[step]?.getD default
      let inState := inputState25 program sized.trace.memory row
      let outState := Model.Keccak.keccakF1600 inState
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

def evalAtom (gpows : @& Array K) (cols : @& Array (Array K)) (z : Nat) : Atom → K
  | .const v => v
  | .col i => (cols[i]?.getD #[])[z]?.getD 0
  | .gcol i k => nativeMul (Model.Layout.gAt gpows k) ((cols[i]?.getD #[])[z]?.getD 0)
  | .prod i j k =>
    nativeMul (nativeMul (Model.Layout.gAt gpows k) ((cols[i]?.getD #[])[z]?.getD 0))
      ((cols[j]?.getD #[])[z]?.getD 0)

def evalCoord (gpows : @& Array K) (cols bcCols : @& Array (Array K)) (z : Nat) : Coord → K
  | .atom a => evalAtom gpows cols z a
  | .index => Model.Layout.gAt gpows z
  | .publicCol slot => (bcCols[slot]?.getD #[])[z]?.getD 0
  | .sum terms =>
    foldRange terms.size
      (fun acc idx =>
        add acc (evalAtom gpows cols z (terms[idx]?.getD (.const 0))))
      0

def buildSideLeaves (gpows : @& Array K) (blocks : @& Array Block) (lay : @& BusLayout)
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
        foldRange blk.rows
          (fun cur z =>
            let val := foldRange blk.coords.size
              (fun acc i =>
                let c := blk.coords[i]?.getD (cConst 0)
                let wi := w[i]?.getD zero
                eadd acc (nativeMulBase wi (evalCoord gpows cols bcCols z c)))
              beta
            cur.setIfInBounds (off + z) val)
          leaves)
    init

def nextLevel (current : @& Array E) : Array E :=
  let fullRows := current.size / 4
  let outLen := (current.size + 3) / 4
  let full := foldRange fullRows
    (fun acc row =>
      let c0 := current[4 * row]?.getD one
      let c1 := current[4 * row + 1]?.getD one
      let c2 := current[4 * row + 2]?.getD one
      let c3 := current[4 * row + 3]?.getD one
      acc.push (nativeKaratsuba (nativeKaratsuba c0 c1) (nativeKaratsuba c2 c3)))
    (Array.emptyWithCapacity outLen)
  if 4 * fullRows < current.size then
    let c0 := current[4 * fullRows]?.getD one
    let c1 := current[4 * fullRows + 1]?.getD one
    let c2 := current[4 * fullRows + 2]?.getD one
    let c3 := current[4 * fullRows + 3]?.getD one
    full.push (nativeKaratsuba (nativeKaratsuba c0 c1) (nativeKaratsuba c2 c3))
  else
    full

def buildLayers (leaves : Array E) (mu : Nat) : Array (Array E) :=
  let init := (Array.replicate (mu + 1) #[]).setIfInBounds 0 leaves
  let (layers, level) := foldRange (mu / 2)
    (fun (cur, lvl) _ =>
      let next := nextLevel (cur[lvl]?.getD #[])
      let lvl' := lvl + 2
      (cur.setIfInBounds lvl' next, lvl'))
    (init, 0)
  if level < mu then
    let below := layers[level]?.getD #[]
    let root :=
      if below.size ≤ 1 then below[0]?.getD one
      else nativeKaratsuba (below[0]?.getD one) (below[1]?.getD one)
    layers.setIfInBounds mu #[root]
  else
    layers

def padFourMultiple (values : Array E) : Array E :=
  Spec.Bus.padFourMultiple values

def quarticSummand (g0 s0 g1 s1 g2 s2 g3 s3 eqWeight : E) : E × E × E × E :=
  let a0 := nativeKaratsuba eqWeight g0
  let d0 := nativeKaratsuba eqWeight s0
  let right0 := nativeKaratsuba g2 g3
  let right2 := nativeKaratsuba s2 s3
  let left0 := nativeKaratsuba a0 g1
  let left2 := nativeKaratsuba d0 s1
  let leftAtOne := nativeKaratsuba (eadd a0 d0) (eadd g1 s1)
  let rightAtOne := nativeKaratsuba (eadd g2 s2) (eadd g3 s3)
  let left1 := eadd leftAtOne (eadd left0 left2)
  let right1 := eadd rightAtOne (eadd right0 right2)
  let c0 := nativeKaratsuba left0 right0
  let c4 := nativeKaratsuba left2 right2
  let middle := nativeKaratsuba left1 right1
  let atOne := nativeKaratsuba leftAtOne rightAtOne
  let crossEven := nativeKaratsuba (eadd left0 left2) (eadd right0 right2)
  let crossHigh := nativeKaratsuba (eadd left1 left2) (eadd right1 right2)
  (eadd c0 atOne, eadd (eadd crossEven c0) (eadd c4 middle),
    eadd crossHigh (eadd middle c4), c4)

def addMsg4 (a b : E × E × E × E) : E × E × E × E :=
  Spec.Bus.addMsg4 a b

def treeRoundMessage (values : @& Array E) (eqWeights : @& Array E) : E × E × E × E :=
  let storedRows := values.size / 4
  let fullPairs := storedRows / 2
  let msg := foldRange fullPairs
    (fun acc pair =>
      let lo := 8 * pair
      let hi := lo + 4
      let g0 := values[lo]?.getD one
      let g1 := values[lo + 1]?.getD one
      let g2 := values[lo + 2]?.getD one
      let g3 := values[lo + 3]?.getD one
      let s0 := eadd g0 (values[hi]?.getD one)
      let s1 := eadd g1 (values[hi + 1]?.getD one)
      let s2 := eadd g2 (values[hi + 2]?.getD one)
      let s3 := eadd g3 (values[hi + 3]?.getD one)
      let w := eqWeights[pair]?.getD zero
      addMsg4 acc (quarticSummand g0 s0 g1 s1 g2 s2 g3 s3 w))
    (zero, zero, zero, zero)
  if storedRows % 2 = 1 then
    let lo := 8 * fullPairs
    let g0 := values[lo]?.getD one
    let g1 := values[lo + 1]?.getD one
    let g2 := values[lo + 2]?.getD one
    let g3 := values[lo + 3]?.getD one
    let w := eqWeights[fullPairs]?.getD zero
    addMsg4 msg (quarticSummand g0 (eadd g0 one) g1 (eadd g1 one)
      g2 (eadd g2 one) g3 (eadd g3 one) w)
  else
    msg

def foldTreeScalar (values : @& Array E) (challenge : E) : Array E :=
  let storedRows := values.size / 4
  let fullRows := storedRows / 2
  let outRows := (storedRows + 1) / 2
  let folded := foldRange fullRows
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
      let acc := acc.push (interp v0 h0 challenge)
      let acc := acc.push (interp v1 h1 challenge)
      let acc := acc.push (interp v2 h2 challenge)
      acc.push (interp v3 h3 challenge))
    (Array.emptyWithCapacity (4 * outRows))
  if storedRows % 2 = 1 then
    let lo := 8 * fullRows
    let v0 := values[lo]?.getD one
    let v1 := values[lo + 1]?.getD one
    let v2 := values[lo + 2]?.getD one
    let v3 := values[lo + 3]?.getD one
    let folded := folded.push (interp v0 one challenge)
    let folded := folded.push (interp v1 one challenge)
    let folded := folded.push (interp v2 one challenge)
    folded.push (interp v3 one challenge)
  else
    folded

def treeChildren (values : @& Array E) : Array E :=
  Spec.Bus.treeChildren values

def combineMsg4 (lambda : E) (m0 m1 m2 : E × E × E × E) : Array E :=
  let c0 := eadd m0.1 (nativeKaratsuba lambda (eadd m1.1 (nativeKaratsuba lambda m2.1)))
  let c2 := eadd m0.2.1 (nativeKaratsuba lambda (eadd m1.2.1 (nativeKaratsuba lambda m2.2.1)))
  let c3 := eadd m0.2.2.1 (nativeKaratsuba lambda (eadd m1.2.2.1 (nativeKaratsuba lambda m2.2.2.1)))
  let c4 := eadd m0.2.2.2 (nativeKaratsuba lambda (eadd m1.2.2.2 (nativeKaratsuba lambda m2.2.2.2)))
  let c1 := eadd (eadd c0 c2) (eadd c3 c4)
  #[c1, c2, c3, c4]

abbrev ProductTriple := Spec.Bus.ProductTriple

def shrinkEqLow (eqr : Array E) : Array E :=
  Spec.Bus.shrinkEqLow eqr

def treeRoundFold (lambda : E) (point : @& Array E) (roundCount : Nat)
    (t0 t1 t2 : Array E) (curPs : ProverState) :
    Array E × Array E × Array E × Array E × ProverState :=
  let eqW0 := eqTable (point.extract 1 point.size)
  let (_, s0, s1, s2, rp, pState) := foldRange roundCount
    (fun (eqW, s0, s1, s2, rp, pState) _ =>
      let m0 := treeRoundMessage s0 eqW
      let m1 := treeRoundMessage s1 eqW
      let m2 := treeRoundMessage s2 eqW
      let coeffs := combineMsg4 lambda m0 m1 m2
      let pState := addScalars pState coeffs
      let (ch, pState) := sampleChallenge pState
      (shrinkEqLow eqW, foldTreeScalar s0 ch, foldTreeScalar s1 ch, foldTreeScalar s2 ch,
        rp.push ch, pState))
    (eqW0, t0, t1, t2, Array.emptyWithCapacity roundCount, curPs)
  (s0, s1, s2, rp, pState)

def proveProductTriple (leaves0 leaves1 leaves2 : Array E) (mu : Nat)
    (ps : ProverState) : ProductTriple × ProverState :=
  let layers0 := buildLayers leaves0 mu
  let layers1 := buildLayers leaves1 mu
  let layers2 := buildLayers leaves2 mu
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
          let nextVals := #[interp l0 h0 ch, interp l1 h1 ch, interp l2 h2 ch]
          prev (layer - 1) #[ch] nextVals curPs
        else
          let roundCount := mu - layer
          let t0 := padFourMultiple (layers0[layer - 2]?.getD #[])
          let t1 := padFourMultiple (layers1[layer - 2]?.getD #[])
          let t2 := padFourMultiple (layers2[layer - 2]?.getD #[])
          let (t0, t1, t2, roundPoint, curPs) :=
            treeRoundFold lambda point roundCount t0 t1 t2 curPs
          let ch0 := treeChildren t0
          let ch1 := treeChildren t1
          let ch2 := treeChildren t2
          let curPs := addScalars (addScalars (addScalars curPs ch0) ch1) ch2
          let (lowCh, curPs) := sampleChallenge curPs
          let (highCh, curPs) := sampleChallenge curPs
          let evalQuad (ch : Array E) : E :=
            interp (interp (ch[0]?.getD one) (ch[1]?.getD one) lowCh)
              (interp (ch[2]?.getD one) (ch[3]?.getD one) lowCh) highCh
          let nextVals := #[evalQuad ch0, evalQuad ch1, evalQuad ch2]
          let nextPoint := #[lowCh, highCh] ++ roundPoint
          prev (layer - 2) nextPoint nextVals curPs)
    steps
  let (point, values, ps') := loop mu #[] #[r0, r1, r2] ps
  (⟨point, values⟩, ps')

abbrev ProdTerm := Spec.Bus.ProdTerm
abbrev BusForm := Spec.Bus.BusForm

def emptyBusForm (nCols : Nat) : BusForm := Spec.Bus.emptyBusForm nCols

def scaleBusForm (form : @& BusForm) (factor : E) : BusForm :=
  { coeffs := form.coeffs.map (nativeKaratsuba factor)
    prods := form.prods.map (fun p => ⟨p.colA, p.colB, nativeKaratsuba factor p.coeff⟩)
    constant := nativeKaratsuba factor form.constant }

def addBusForm (a b : BusForm) : BusForm :=
  Spec.Bus.addBusForm a b

def accumulateAtom (gpows : @& Array K) (base : Nat) (w : E) (form : BusForm) : Atom → BusForm
  | .const v =>
    let ⟨coeffs, prods, c⟩ := form
    ⟨coeffs, prods, eadd c (nativeMulBase w v)⟩
  | .col i =>
    let ⟨coeffs, prods, c⟩ := form
    let loc := i - base
    ⟨coeffs.setIfInBounds loc (eadd (coeffs[loc]?.getD zero) w), prods, c⟩
  | .gcol i k =>
    let ⟨coeffs, prods, c⟩ := form
    let loc := i - base
    let wk := nativeMulBase w (Model.Layout.gAt gpows k)
    ⟨coeffs.setIfInBounds loc (eadd (coeffs[loc]?.getD zero) wk), prods, c⟩
  | .prod i j k =>
    let ⟨coeffs, prods, c⟩ := form
    let wk := nativeMulBase w (Model.Layout.gAt gpows k)
    ⟨coeffs, prods.push ⟨i - base, j - base, wk⟩, c⟩

def accumulateCoord (gpows : @& Array K) (base : Nat) (w : E) (form : BusForm) : Coord → BusForm
  | .atom a => accumulateAtom gpows base w form a
  | .sum terms =>
    foldRange terms.size
      (fun cur idx => accumulateAtom gpows base w cur (terms[idx]?.getD (.const 0)))
      form
  | .index | .publicCol _ => form

abbrev ColumnClaim := Spec.Bus.ColumnClaim

def pointEq (a b : @& Array E) : Bool := Spec.Bus.pointEq a b

def findKnownClaim (claims : @& Array ColumnClaim) (col : Nat)
    (point : @& Array E) : Option E := Spec.Bus.findKnownClaim claims col point

def decomposeNoneCoords (gpows : @& Array K) (blk : @& Block)
    (cols bcCols : @& Array (Array K)) (zetaLo w : @& Array E)
    (curClaims : Array ColumnClaim) (curPs : ProverState) :
    E × Array ColumnClaim × ProverState :=
  foldRange blk.coords.size
    (fun (inAcc, cAcc, pAcc) i =>
      let wi := w[i]?.getD zero
      match blk.coords[i]?.getD (cConst 0) with
      | .atom (.const v) =>
        (eadd inAcc (nativeMulBase wi v), cAcc, pAcc)
      | .index =>
        (eadd inAcc (nativeKaratsuba wi (indexMle zetaLo)), cAcc, pAcc)
      | .publicCol slot =>
        let val := mleEval (bcCols[slot]?.getD #[]) zetaLo
        (eadd inAcc (nativeKaratsuba wi val), cAcc, pAcc)
      | .atom (.col colIdx) =>
        match findKnownClaim cAcc colIdx zetaLo with
        | some v => (eadd inAcc (nativeKaratsuba wi v), cAcc, pAcc)
        | none =>
          let v := mleEval (cols[colIdx]?.getD #[]) zetaLo
          let pAcc' := addScalar pAcc v
          let cAcc' := cAcc.push ⟨colIdx, zetaLo, v⟩
          (eadd inAcc (nativeKaratsuba wi v), cAcc', pAcc')
      | .atom (.gcol colIdx k) =>
        let (v, cAcc', pAcc') :=
          match findKnownClaim cAcc colIdx zetaLo with
          | some v => (v, cAcc, pAcc)
          | none =>
            let v := mleEval (cols[colIdx]?.getD #[]) zetaLo
            (v, cAcc.push ⟨colIdx, zetaLo, v⟩, addScalar pAcc v)
        let gv := nativeMulBase v (Model.Layout.gAt gpows k)
        (eadd inAcc (nativeKaratsuba wi gv), cAcc', pAcc')
      | _ => (inAcc, cAcc, pAcc))
    (zero, curClaims, curPs)

def decomposeSideFold (gpows : @& Array K) (blocks : @& Array Block) (lay : @& BusLayout)
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
        let selSum' := eadd selSum eqHi
        match blk.owner with
        | some t =>
          let base := tableBase t
          let form0 := curForms[t.val]?.getD (emptyBusForm (tableWidth t))
          let ⟨coeffs0, prods0, const0⟩ := form0
          let form1 : BusForm := ⟨coeffs0, prods0, eadd const0 (nativeKaratsuba eqHi beta)⟩
          let form2 := foldRange blk.coords.size
            (fun f i =>
              let c := blk.coords[i]?.getD (cConst 0)
              let wi := w[i]?.getD zero
              accumulateCoord gpows base (nativeKaratsuba eqHi wi) f c)
            form1
          let phiPad := foldRange blk.padding.size
            (fun pAcc i =>
              let v := blk.padding[i]?.getD 0
              let wi := w[i]?.getD zero
              eadd pAcc (nativeMulBase wi v))
            beta
          let padTerm := nativeKaratsuba (nativeKaratsuba eqHi (paddingWeight zetaLo blk.rows)) (eadd one phiPad)
          (eadd acc padTerm, selSum', curForms.setIfInBounds t.val form2, curClaims, curPs)
        | none =>
          let (inner, nextClaims, nextPs) :=
            decomposeNoneCoords gpows blk cols bcCols zetaLo w curClaims curPs
          let blockVal := nativeKaratsuba eqHi (eadd beta inner)
          (eadd acc blockVal, selSum', curForms, nextClaims, nextPs))
    (zero, zero, forms, claims, ps)

def decomposeSide (gpows : @& Array K) (blocks : @& Array Block) (lay : @& BusLayout)
    (cols bcCols : @& Array (Array K)) (zeta w : @& Array E) (beta : E)
    (forms : Array BusForm) (claims : Array ColumnClaim)
    (ps : ProverState) : E × Array BusForm × Array ColumnClaim × ProverState :=
  let (acc, selSum, forms, claims, ps) :=
    decomposeSideFold gpows blocks lay cols bcCols zeta w beta forms claims ps
  (eadd acc (eadd one selSum), forms, claims, ps)

def hasPair (pairs : @& Array (Nat × Nat)) (a b : Nat) : Bool :=
  Spec.Bus.hasPair pairs a b

def findProdSum (sums : @& Array (Nat × Nat × E)) (a b : Nat) : E :=
  Spec.Bus.findProdSum sums a b

def evalBusFormSigma (form : @& BusForm) (colEvals : @& Array E)
    (prodSums : @& Array (Nat × Nat × E)) : E :=
  let lin := foldRange form.coeffs.size
    (fun acc i =>
      eadd acc (nativeKaratsuba (form.coeffs[i]?.getD zero) (colEvals[i]?.getD zero)))
    form.constant
  foldRange form.prods.size
    (fun acc idx =>
      match form.prods[idx]? with
      | none => acc
      | some p => eadd acc (nativeKaratsuba p.coeff (findProdSum prodSums p.colA p.colB)))
    lin

def computeTableSigmas (cols : @& Array (Array K)) (taus : @& Array Nat)
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
        let eqs := eqTable zetaTau
        let colEvals := foldRange nCols
          (fun acc c =>
            let col := cols[base + c]?.getD #[]
            let sum := foldRange eqs.size
              (fun s z => eadd s (nativeMulBase (eqs[z]?.getD zero) (col[z]?.getD 0)))
              zero
            acc.push sum)
          (Array.emptyWithCapacity nCols)
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
        let prodSums := foldRange pairs.size
          (fun acc idx =>
            match pairs[idx]? with
            | none => acc
            | some (a, b) =>
              let colA := cols[base + a]?.getD #[]
              let colB := cols[base + b]?.getD #[]
              let sum := foldRange eqs.size
                (fun s z =>
                  let prodK := nativeMul (colA[z]?.getD 0) (colB[z]?.getD 0)
                  eadd s (nativeMulBase (eqs[z]?.getD zero) prodK))
                zero
              acc.push (a, b, sum))
          (Array.emptyWithCapacity pairs.size)
        (s0.push (evalBusFormSigma f0 colEvals prodSums),
          s1.push (evalBusFormSigma f1 colEvals prodSums),
          s2.push (evalBusFormSigma f2 colEvals prodSums))
      else
        (s0, s1, s2))
    (init0, init1, init2)

abbrev BusProof := Spec.Bus.BusProof

def initTableForms : Array BusForm := Spec.Bus.initTableForms

def proveBalance (gpows : @& Array K) (lay : @& Model.Layout.PublicLayout)
    (cols bcCols : @& Array (Array K)) (ps : ProverState) : BusProof × ProverState :=
  let (alphas, ps) := sampleVec ps busBits
  let w := fingerprintWeights alphas
  let cw := countWeights
  let (beta, ps) := sampleChallenge ps
  let mu := lay.pushLayout.mu
  let countLay : BusLayout := { lay.countLayout with mu := mu }
  let leaves0 := buildSideLeaves gpows lay.push lay.pushLayout cols bcCols w beta
  let leaves1 := buildSideLeaves gpows lay.pull lay.pullLayout cols bcCols w beta
  let leaves2 := buildSideLeaves gpows lay.count countLay cols bcCols cw zero
  let (gkr, ps) := proveProductTriple leaves0 leaves1 leaves2 mu ps
  let zeta := gkr.point
  let (_, forms0, claims, ps) := decomposeSide gpows lay.push lay.pushLayout cols bcCols
    zeta w beta initTableForms #[] ps
  let (_, forms1, claims, ps) := decomposeSide gpows lay.pull lay.pullLayout cols bcCols
    zeta w beta initTableForms claims ps
  let (_, forms2, claims, ps) := decomposeSide gpows lay.count countLay cols bcCols
    zeta cw zero initTableForms claims ps
  let (sigmas0, sigmas1, sigmas2) :=
    computeTableSigmas cols lay.taus forms0 forms1 forms2 zeta
  (⟨claims, zeta, forms0, forms1, forms2, sigmas0, sigmas1, sigmas2⟩, ps)

def jumpIdentityForm (p0 p1 : E) : BusForm :=
  Spec.Bus.jumpIdentityForm p0 p1

def tableIdentityForm (t : Nat) (p0 p1 : E) : BusForm :=
  Spec.Bus.tableIdentityForm t p0 p1

def powersOf (x : E) (count : Nat) : Array E :=
  foldRange count (fun acc i => acc.push (nativeEpow x i)) (Array.emptyWithCapacity count)

abbrev AirTable := Spec.Bus.AirTable

def buildAirs (taus : @& Array Nat) (bus : @& BusProof) (xi : E) : Array AirTable :=
  let pows := powersOf xi (xiFormBase + 3)
  let p0 := pows[0]?.getD one
  let p1 := pows[1]?.getD one
  let fPow0 := pows[xiFormBase]?.getD zero
  let fPow1 := pows[xiFormBase + 1]?.getD zero
  let fPow2 := pows[xiFormBase + 2]?.getD zero
  foldRange nTables
    (fun acc t =>
      if h : t < nTables then
        let tf : Fin nTables := ⟨t, h⟩
        let nCols := tableWidth tf
        let idForm := tableIdentityForm t p0 p1
        let bf0 := scaleBusForm (bus.forms0[t]?.getD (emptyBusForm nCols)) fPow0
        let bf1 := scaleBusForm (bus.forms1[t]?.getD (emptyBusForm nCols)) fPow1
        let bf2 := scaleBusForm (bus.forms2[t]?.getD (emptyBusForm nCols)) fPow2
        let form := addBusForm idForm (addBusForm (addBusForm bf0 bf1) bf2)
        let s0 := nativeKaratsuba fPow0 (bus.sigmas0[t]?.getD zero)
        let s1 := nativeKaratsuba fPow1 (bus.sigmas1[t]?.getD zero)
        let s2 := nativeKaratsuba fPow2 (bus.sigmas2[t]?.getD zero)
        let sigma := eadd (eadd s0 s1) s2
        acc.push { tau := taus[t]?.getD 0, base := tableBase tf, nCols, form, sigma }
      else acc)
    (Array.emptyWithCapacity nTables)

abbrev GroupedForm := Spec.Bus.GroupedForm

def mergeProdEdges (prods : @& Array ProdTerm) : Array (Nat × Nat × E) :=
  Spec.Bus.mergeProdEdges prods

def buildGroupedForm (form : @& BusForm) : GroupedForm :=
  Spec.Bus.buildGroupedForm form

def evalLinK (terms : @& Array (Nat × E)) (cols : @& Array (Array K))
    (base row : Nat) : E :=
  foldRange terms.size
    (fun acc idx =>
      match terms[idx]? with
      | none => acc
      | some (c, w) =>
        let v := (cols[base + c]?.getD #[])[row]?.getD 0
        eadd acc (nativeMulBase w v))
    zero

def evalLinSumK (terms : @& Array (Nat × E)) (cols : @& Array (Array K))
    (base i half : Nat) : E :=
  foldRange terms.size
    (fun acc idx =>
      match terms[idx]? with
      | none => acc
      | some (c, w) =>
        let col := cols[base + c]?.getD #[]
        let s := add (col[i]?.getD 0) (col[i + half]?.getD 0)
        eadd acc (nativeMulBase w s))
    zero

def tableMessageK (gf : @& GroupedForm) (cols : @& Array (Array K))
    (base : Nat) (eqr : @& Array E) (half : Nat) (atOne : Bool) : E × E :=
  let (endAcc, slopeAcc) := foldRange half
    (fun (eAcc, sAcc) i =>
      let endIdx := if atOne then i + half else i
      let linEnd := evalLinK gf.lin cols base endIdx
      let (ep, sl) := foldRange gf.groups.size
        (fun (epG, slG) g =>
          match gf.groups[g]? with
          | none => (epG, slG)
          | some (left, right) =>
            let leftCol := cols[base + left]?.getD #[]
            let leftEnd := leftCol[endIdx]?.getD 0
            let leftSum := add (leftCol[i]?.getD 0) (leftCol[i + half]?.getD 0)
            let rightEnd := evalLinK right cols base endIdx
            let rightSum := evalLinSumK right cols base i half
            (eadd epG (nativeMulBase rightEnd leftEnd),
              eadd slG (nativeMulBase rightSum leftSum)))
        (linEnd, zero)
      let eqw := eqr[i]?.getD zero
      (eadd eAcc (nativeKaratsuba eqw ep), eadd sAcc (nativeKaratsuba eqw sl)))
    (zero, zero)
  (eadd endAcc gf.constant, slopeAcc)

def joinTableState (gf : @& GroupedForm) (cols : @& Array (Array K))
    (base : Nat) (r : E) (half : Nat) : Array (Array E) :=
  let buildLinCol (terms : Array (Nat × E)) : Array E :=
    foldRange half
      (fun col i =>
        let v := foldRange terms.size
          (fun acc idx =>
            match terms[idx]? with
            | none => acc
            | some (c, w) =>
              let kc := cols[base + c]?.getD #[]
              let lo := kc[i]?.getD 0
              let hi := kc[i + half]?.getD 0
              let wr := nativeKaratsuba w r
              eadd acc (eadd (nativeMulBase w lo) (nativeMulBase wr (add lo hi))))
          zero
        col.push v)
      (Array.emptyWithCapacity half)
  let initCols := #[buildLinCol gf.lin]
  foldRange gf.groups.size
    (fun stateCols g =>
      match gf.groups[g]? with
      | none => stateCols
      | some (left, right) =>
        let kc := cols[base + left]?.getD #[]
        let leftCol := foldRange half
          (fun col i =>
            let lo := kc[i]?.getD 0
            let hi := kc[i + half]?.getD 0
            col.push (interpK lo hi r))
          (Array.emptyWithCapacity half)
        let rightCol := buildLinCol right
        (stateCols.push leftCol).push rightCol)
    initCols

def tableMessageE (constant : E) (state : @& Array (Array E))
    (eqr : @& Array E) (half : Nat) (atOne : Bool) : E × E :=
  let nGroups := (state.size - 1) / 2
  let linCol := state[0]?.getD #[]
  foldRange half
    (fun (eAcc, sAcc) i =>
      let endIdx := if atOne then i + half else i
      let linEnd := linCol[endIdx]?.getD zero
      let (ep, sl) := foldRange nGroups
        (fun (epG, slG) g =>
          let lCol := state[1 + 2 * g]?.getD #[]
          let rCol := state[2 + 2 * g]?.getD #[]
          let lEnd := lCol[endIdx]?.getD zero
          let rEnd := rCol[endIdx]?.getD zero
          let lSum := eadd (lCol[i]?.getD zero) (lCol[i + half]?.getD zero)
          let rSum := eadd (rCol[i]?.getD zero) (rCol[i + half]?.getD zero)
          (eadd epG (nativeKaratsuba lEnd rEnd), eadd slG (nativeKaratsuba lSum rSum)))
        (linEnd, zero)
      let eqw := eqr[i]?.getD zero
      (eadd eAcc (nativeKaratsuba eqw ep), eadd sAcc (nativeKaratsuba eqw sl)))
    (constant, zero)

def foldTableState (state : Array (Array E)) (r : E) (half : Nat) : Array (Array E) :=
  foldRange state.size
    (fun acc c =>
      let col := state[c]?.getD #[]
      let folded := foldRange half
        (fun out i =>
          out.push (interp (col[i]?.getD zero) (col[i + half]?.getD zero) r))
        (Array.emptyWithCapacity half)
      acc.push folded)
    (Array.emptyWithCapacity state.size)

def roundPolynomial (endpoint quadratic zetaM claim waiting : E) : Array E :=
  let eqZ := eadd one zetaM
  let (p0, p1) :=
    if Spec.Vm.wordBEq zetaM zero then
      (eadd claim waiting, endpoint)
    else
      (endpoint, nativeKaratsuba (eadd (eadd claim waiting) (nativeKaratsuba eqZ endpoint)) (nativeEinv zetaM))
  let h2 := eadd (eadd (nativeKaratsuba eqZ quadratic) p0) (eadd p1 quadratic)
  #[nativeKaratsuba eqZ p0, eadd (eadd claim h2) quadratic, h2, quadratic]

abbrev TableClaims := Spec.Bus.TableClaims

def constraintsRoundMsgs (airs : @& Array AirTable) (gForms : @& Array GroupedForm)
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
          | some st => tableMessageE gf.constant st eqr half atOne
          | none => tableMessageK gf cols base eqr half atOne
        (eadd m0 (nativeKaratsuba wt p0), eadd m1 (nativeKaratsuba wt p1))
      else (m0, m1))
    (zero, zero)

def constraintsUpdateTables (airs : @& Array AirTable) (gForms : @& Array GroupedForm)
    (cols : @& Array (Array K)) (weights : Array E)
    (states : Array (Option (Array (Array E))))
    (m half : Nat) (rk eqK : E) : Array E × Array (Option (Array (Array E))) :=
  foldRange airs.size
    (fun (wAcc, sAcc) t =>
      let tau := airs[t]?.map Spec.Bus.AirTable.tau |>.getD 0
      let wt := wAcc[t]?.getD one
      if m < tau then
        let wAcc' := wAcc.setIfInBounds t (nativeKaratsuba wt eqK)
        let gf := gForms[t]?.getD default
        let base := airs[t]?.map Spec.Bus.AirTable.base |>.getD 0
        let nextSt :=
          match sAcc[t]?.join with
          | some st => some (foldTableState st rk half)
          | none => some (joinTableState gf cols base rk half)
        (wAcc', sAcc.setIfInBounds t nextSt)
      else
        (wAcc.setIfInBounds t (nativeKaratsuba wt rk), sAcc))
    (weights, states)

def constraintsRoundsFold (airs : @& Array AirTable) (gForms : @& Array GroupedForm)
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
          if tau ≤ m then eadd acc (airs[t]?.map Spec.Bus.AirTable.sigma |>.getD zero)
          else acc)
        zero
      let u := nativeKaratsuba k waiting
      let (msg0, msg1) :=
        constraintsRoundMsgs airs gForms cols weights states eqr m half atOne
      let eqr' := shrinkEqHigh eqr
      let h := roundPolynomial msg0 msg1 zm claim u
      let curPs := addScalars curPs #[h[0]?.getD zero, h[2]?.getD zero, h[3]?.getD zero]
      let (rk, curPs) := sampleChallenge curPs
      let claim' := polyEval h rk
      let chi' := chi.setIfInBounds m rk
      let k' := nativeKaratsuba k rk
      let eqK := eadd (eadd one zm) rk
      let ws' := constraintsUpdateTables airs gForms cols weights states m half rk eqK
      (eqr', chi', k', claim', ws', curPs))
    (eqr0, chi0, one, claim0, (weights0, states0), ps)

def proveConstraints (airs : @& Array AirTable) (cols : @& Array (Array K))
    (zeta : @& Array E) (ps : ProverState) : Array TableClaims × ProverState :=
  let n := foldRange airs.size
    (fun acc t => max acc (airs[t]?.map Spec.Bus.AirTable.tau |>.getD 0)) 0
  let gForms := foldRange airs.size
    (fun acc t =>
      acc.push (buildGroupedForm (airs[t]?.map Spec.Bus.AirTable.form |>.getD (emptyBusForm 0))))
    (Array.emptyWithCapacity airs.size)
  let eqr0 := eqTable (zeta.extract 0 (n - 1))
  let chi0 := Array.replicate n zero
  let claim0 := foldRange airs.size
    (fun acc t => eadd acc (airs[t]?.map Spec.Bus.AirTable.sigma |>.getD zero)) zero
  let weights0 := Array.replicate airs.size one
  let states0 : Array (Option (Array (Array E))) := Array.replicate airs.size none
  let (_, chi, _, _, _, ps) :=
    constraintsRoundsFold airs gForms cols zeta n eqr0 chi0 claim0 weights0 states0 ps
  foldRange airs.size
    (fun (claimsAcc, curPs) t =>
      let tau := airs[t]?.map Spec.Bus.AirTable.tau |>.getD 0
      let base := airs[t]?.map Spec.Bus.AirTable.base |>.getD 0
      let nCols := airs[t]?.map Spec.Bus.AirTable.nCols |>.getD 0
      let chiT := chi.extract 0 tau
      let evals := foldRange nCols
        (fun acc c => acc.push (mleEval (cols[base + c]?.getD #[]) chiT))
        (Array.emptyWithCapacity nCols)
      let curPs := addScalars curPs evals
      (claimsAcc.push ⟨chiT, evals⟩, curPs))
    (Array.emptyWithCapacity airs.size, ps)

abbrev SlotClaim := Spec.Bus.SlotClaim
abbrev OutputClaim := Spec.Bus.OutputClaim

def bindPiClaims (rPi : E) (logMem : Nat) (publicInput : @& Array E) : Array ColumnClaim :=
  let a := publicInput[0]?.getD zero
  let b := publicInput[1]?.getD zero
  let point := (Array.replicate logMem zero).setIfInBounds 0 rPi
  #[⟨memLo, point, interpK a.c0 b.c0 rPi⟩,
    ⟨memHi, point, interpK a.c1 b.c1 rPi⟩,
    ⟨memTop, point, interpK a.c2 b.c2 rPi⟩]

def routeSlotClaims (placements : @& Array (Option Placement))
    (claims : @& Array ColumnClaim) : Array SlotClaim :=
  Spec.Bus.routeSlotClaims placements claims

def finishClaims (lay : @& Model.Layout.PublicLayout) (publicInput : @& Array E)
    (busClaims : Array ColumnClaim) (tableClaims : @& Array TableClaims)
    (rPi : E) : Array SlotClaim :=
  let allClaims := foldRange nTables
    (fun acc t =>
      if h : t < nTables then
        let tf : Fin nTables := ⟨t, h⟩
        let base := tableBase tf
        let width := tableWidth tf
        let tc := tableClaims[t]?.getD default
        foldRange width
          (fun cur c =>
            let col := base + c
            match keccakValue col with
            | some (.output _) => cur
            | _ => cur.push ⟨col, tc.chi, tc.evals[c]?.getD zero⟩)
          acc
      else acc)
    busClaims
  let withPi := allClaims ++ bindPiClaims rPi lay.logMem publicInput
  routeSlotClaims lay.placements withPi

def keccakOutputClaim (tableClaims : @& Array TableClaims) : OutputClaim :=
  Spec.Bus.keccakOutputClaim tableClaims

def ProverState.toSpec (ps : ProverState) : Spec.Bus.ProverState :=
  ⟨Model.Transcript.Registers.toSpec ps.sponge, ps.stream⟩

structure BusStageOutput where
  ps : ProverState
  slotClaims : Array SlotClaim
  keccakOutput : OutputClaim
  deriving Inhabited

def BusStageOutput.toSpec (o : BusStageOutput) : Spec.Bus.BusStageOutput :=
  ⟨o.ps.toSpec, o.slotClaims, o.keccakOutput⟩

def proveBusAndConstraints (program : @& Array Spec.Vm.Op) (iv : ByteArray)
    (publicInput : @& Array E) (bundle : @& WitnessBundle) : BusStageOutput :=
  let ps0 := startTranscript iv publicInput bundle.sized bundle.root
  let cols := buildColumns program bundle.sized bundle.message
  let bcCols := Model.Layout.bytecodeColumnsFast program
  let gpows := Model.Layout.gpowTable (maxBusGpowIndex program bundle.sized)
  let (bus, ps1) := proveBalance gpows bundle.sized.layout cols bcCols ps0
  let (xi, ps2) := sampleChallenge ps1
  let airs := buildAirs bundle.sized.layout.taus bus xi
  let (tableClaims, ps3) := proveConstraints airs cols bus.point ps2
  let (rPi, ps4) := sampleChallenge ps3
  let slots := finishClaims bundle.sized.layout publicInput bus.claims tableClaims rPi
  let outClaim := keccakOutputClaim tableClaims
  ⟨ps4, slots, outClaim⟩

end LeanVmXmss.Model.Bus
