import Spec.Witness.Basic

namespace LeanVmXmss.Spec.Bus

open Spec.Field (K E zero one add mul eadd emul mulBase einv epow embed)
open Spec.Layout
open Spec.Witness
open Model.Pcs.Ntt (foldRange)

instance : Inhabited E := ⟨zero⟩
instance : Inhabited Spec.Transcript.Sponge := ⟨⟨Spec.Keccak.zero, 0⟩⟩

structure ProverState where
  sponge : Spec.Transcript.Sponge
  stream : Array E
  deriving Inhabited

def initProverState (iv : ByteArray) (publicInput : Array E) : ProverState :=
  { sponge := Spec.Transcript.init iv (publicBytes publicInput), stream := #[] }

def addScalar (ps : ProverState) (x : E) : ProverState :=
  let ⟨sponge, stream⟩ := ps
  ⟨Spec.Transcript.observe sponge x, stream.push x⟩

def addScalars (ps : ProverState) (xs : @& Array E) : ProverState :=
  foldRange xs.size (fun acc i => addScalar acc (xs[i]?.getD zero)) ps

def sampleChallenge (ps : ProverState) : E × ProverState :=
  let ⟨sponge, stream⟩ := ps
  let (ch, sponge') := Spec.Transcript.challenge sponge
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

def interp (lo hi t : E) : E :=
  eadd lo (emul t (eadd lo hi))

def interpK (lo hi : K) (t : E) : E :=
  eadd (embed lo) (mulBase t (add lo hi))

def eqEval (r x : @& Array E) : E :=
  foldRange (min r.size x.size)
    (fun acc i =>
      let ri := r[i]?.getD zero
      let xi := x[i]?.getD zero
      emul acc (eadd one (eadd ri xi)))
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
          let p := emul lo rk
          let cur1 := cur.setIfInBounds (half + j) p
          cur1.setIfInBounds j (eadd lo p))
        out)
    init

def shrinkEqHigh (eqr : Array E) : Array E :=
  let half := eqr.size / 2
  foldRange half
    (fun acc i =>
      acc.push (eadd (eqr[i]?.getD zero) (eqr[i + half]?.getD zero)))
    (Array.emptyWithCapacity half)

def mleEval (table : @& Array K) (point : @& Array E) : E :=
  let eqs := eqTable point
  foldRange eqs.size
    (fun acc z =>
      let eqz := eqs[z]?.getD zero
      let vz := table[z]?.getD 0
      eadd acc (mulBase eqz vz))
    zero

def paddingWeight (point : @& Array E) (n : Nat) : E :=
  let bit (k : Nat) : E := embed (UInt64.ofNat ((n >>> k) &&& 1))
  let low := foldRange point.size
    (fun pad k =>
      let r := point[k]?.getD zero
      let bk1 := eadd one (bit k)
      eadd (emul bk1 r) (emul (eadd bk1 r) pad))
    one
  emul (eadd one (bit point.size)) low

def indexMle (zeta : @& Array E) : E :=
  let res := foldRange zeta.size
    (fun (acc, g2k) i =>
      let z := zeta[i]?.getD zero
      let factor := eadd one (mulBase z (add 1 g2k))
      (emul acc factor, mul g2k g2k))
    (one, (2 : K))
  res.1

def polyEval (coeffs : @& Array E) (point : E) : E :=
  foldRange coeffs.size
    (fun acc step =>
      let c := coeffs[coeffs.size - 1 - step]?.getD zero
      eadd (emul acc point) c)
    zero

def selectorPoint (sel len : Nat) : Array E :=
  foldRange len
    (fun acc bit => acc.push (embed (UInt64.ofNat ((sel >>> bit) &&& 1))))
    (Array.emptyWithCapacity len)

def fingerprintWeights (alphas : @& Array E) : Array E :=
  let init := Array.replicate (1 <<< busBits) one
  foldRange busBits
    (fun w bit =>
      let a := alphas[bit]?.getD zero
      let a1 := eadd a one
      foldRange (1 <<< busBits)
        (fun cur x =>
          let factor := if ((x >>> bit) &&& 1) = 1 then a else a1
          cur.setIfInBounds x (emul (cur[x]?.getD zero) factor))
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
  let zeroPerm := Spec.Keccak.permute Spec.Keccak.zero
  let keccakOutCols := foldRange keccakRows.size
    (fun cols step =>
      let row := keccakRows[step]?.getD default
      let inSpec := (inputState25 program sized.trace.memory row).toSpec
      let outSpec := Spec.Keccak.permute inSpec
      foldRange stateLanes
        (fun cur lane =>
          cur.modify lane (fun col => col.setIfInBounds step (outSpec[lane]?.getD 0)))
        cols)
    (foldRange stateLanes
      (fun acc lane => acc.push (Array.replicate steps (zeroPerm[lane]?.getD 0)))
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

def evalAtom (cols : @& Array (Array K)) (z : Nat) : Atom → K
  | .const v => v
  | .col i => (cols[i]?.getD #[])[z]?.getD 0
  | .gcol i k => mul (Spec.Xmss.gpow k) ((cols[i]?.getD #[])[z]?.getD 0)
  | .prod i j k =>
    mul (mul (Spec.Xmss.gpow k) ((cols[i]?.getD #[])[z]?.getD 0))
      ((cols[j]?.getD #[])[z]?.getD 0)

def evalCoord (cols bcCols : @& Array (Array K)) (z : Nat) : Coord → K
  | .atom a => evalAtom cols z a
  | .index => Spec.Xmss.gpow z
  | .publicCol slot => (bcCols[slot]?.getD #[])[z]?.getD 0
  | .sum terms =>
    foldRange terms.size
      (fun acc idx =>
        add acc (evalAtom cols z (terms[idx]?.getD (.const 0))))
      0

def buildSideLeaves (blocks : @& Array Block) (lay : @& BusLayout)
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
                eadd acc (mulBase wi (evalCoord cols bcCols z c)))
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
      acc.push (emul (emul c0 c1) (emul c2 c3)))
    (Array.emptyWithCapacity outLen)
  if 4 * fullRows < current.size then
    let c0 := current[4 * fullRows]?.getD one
    let c1 := current[4 * fullRows + 1]?.getD one
    let c2 := current[4 * fullRows + 2]?.getD one
    let c3 := current[4 * fullRows + 3]?.getD one
    full.push (emul (emul c0 c1) (emul c2 c3))
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
      else emul (below[0]?.getD one) (below[1]?.getD one)
    layers.setIfInBounds mu #[root]
  else
    layers

def padFourMultiple (values : Array E) : Array E :=
  let rem := max 1 values.size
  let target := 4 * ((rem + 3) / 4)
  foldRange (target - values.size) (fun acc _ => acc.push one) values

def quarticSummand (g0 s0 g1 s1 g2 s2 g3 s3 eqWeight : E) : E × E × E × E :=
  let a0 := emul eqWeight g0
  let d0 := emul eqWeight s0
  let right0 := emul g2 g3
  let right2 := emul s2 s3
  let left0 := emul a0 g1
  let left2 := emul d0 s1
  let leftAtOne := emul (eadd a0 d0) (eadd g1 s1)
  let rightAtOne := emul (eadd g2 s2) (eadd g3 s3)
  let left1 := eadd leftAtOne (eadd left0 left2)
  let right1 := eadd rightAtOne (eadd right0 right2)
  let c0 := emul left0 right0
  let c4 := emul left2 right2
  let middle := emul left1 right1
  let atOne := emul leftAtOne rightAtOne
  let crossEven := emul (eadd left0 left2) (eadd right0 right2)
  let crossHigh := emul (eadd left1 left2) (eadd right1 right2)
  (eadd c0 atOne, eadd (eadd crossEven c0) (eadd c4 middle),
    eadd crossHigh (eadd middle c4), c4)

def addMsg4 (a b : E × E × E × E) : E × E × E × E :=
  (eadd a.1 b.1, eadd a.2.1 b.2.1, eadd a.2.2.1 b.2.2.1, eadd a.2.2.2 b.2.2.2)

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
  if values.isEmpty then #[one, one, one, one]
  else
    #[values[0]?.getD one, values[1]?.getD one,
      values[2]?.getD one, values[3]?.getD one]

def combineMsg4 (lambda : E) (m0 m1 m2 : E × E × E × E) : Array E :=
  let c0 := eadd m0.1 (emul lambda (eadd m1.1 (emul lambda m2.1)))
  let c2 := eadd m0.2.1 (emul lambda (eadd m1.2.1 (emul lambda m2.2.1)))
  let c3 := eadd m0.2.2.1 (emul lambda (eadd m1.2.2.1 (emul lambda m2.2.2.1)))
  let c4 := eadd m0.2.2.2 (emul lambda (eadd m1.2.2.2 (emul lambda m2.2.2.2)))
  let c1 := eadd (eadd c0 c2) (eadd c3 c4)
  #[c1, c2, c3, c4]

structure ProductTriple where
  point : Array E
  values : Array E
  deriving Inhabited

def shrinkEqLow (eqr : Array E) : Array E :=
  let half := eqr.size / 2
  foldRange half
    (fun acc i =>
      acc.push (eadd (eqr[2 * i]?.getD zero) (eqr[2 * i + 1]?.getD zero)))
    (Array.emptyWithCapacity half)

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

structure ProdTerm where
  colA : Nat
  colB : Nat
  coeff : E
  deriving Inhabited

structure BusForm where
  coeffs : Array E
  prods : Array ProdTerm
  constant : E
  deriving Inhabited

def emptyBusForm (nCols : Nat) : BusForm :=
  { coeffs := Array.replicate nCols zero, prods := #[], constant := zero }

def scaleBusForm (form : @& BusForm) (factor : E) : BusForm :=
  { coeffs := form.coeffs.map (emul factor)
    prods := form.prods.map (fun p => ⟨p.colA, p.colB, emul factor p.coeff⟩)
    constant := emul factor form.constant }

def addBusForm (a b : BusForm) : BusForm :=
  let ⟨ca, pa, consta⟩ := a
  let coeffs := foldRange ca.size
    (fun cur i => cur.setIfInBounds i (eadd (cur[i]?.getD zero) (b.coeffs[i]?.getD zero)))
    ca
  { coeffs, prods := pa ++ b.prods, constant := eadd consta b.constant }

def accumulateAtom (base : Nat) (w : E) (form : BusForm) : Atom → BusForm
  | .const v =>
    let ⟨coeffs, prods, c⟩ := form
    ⟨coeffs, prods, eadd c (mulBase w v)⟩
  | .col i =>
    let ⟨coeffs, prods, c⟩ := form
    let loc := i - base
    ⟨coeffs.setIfInBounds loc (eadd (coeffs[loc]?.getD zero) w), prods, c⟩
  | .gcol i k =>
    let ⟨coeffs, prods, c⟩ := form
    let loc := i - base
    let wk := mulBase w (Spec.Xmss.gpow k)
    ⟨coeffs.setIfInBounds loc (eadd (coeffs[loc]?.getD zero) wk), prods, c⟩
  | .prod i j k =>
    let ⟨coeffs, prods, c⟩ := form
    let wk := mulBase w (Spec.Xmss.gpow k)
    ⟨coeffs, prods.push ⟨i - base, j - base, wk⟩, c⟩

def accumulateCoord (base : Nat) (w : E) (form : BusForm) : Coord → BusForm
  | .atom a => accumulateAtom base w form a
  | .sum terms =>
    foldRange terms.size
      (fun cur idx => accumulateAtom base w cur (terms[idx]?.getD (.const 0)))
      form
  | .index | .publicCol _ => form

structure ColumnClaim where
  col : Nat
  point : Array E
  value : E
  deriving Inhabited

def pointEq (a b : @& Array E) : Bool :=
  if a.size = b.size then
    foldRange a.size
      (fun ok i =>
        ok && Spec.Vm.wordBEq (a[i]?.getD zero) (b[i]?.getD zero))
      true
  else
    false

def findKnownClaim (claims : @& Array ColumnClaim) (col : Nat)
    (point : @& Array E) : Option E :=
  foldRange claims.size
    (fun found idx =>
      match found with
      | some _ => found
      | none =>
        match claims[idx]? with
        | none => none
        | some cl =>
          if cl.col = col && pointEq cl.point point then some cl.value else none)
    none

def decomposeNoneCoords (blk : @& Block) (cols bcCols : @& Array (Array K))
    (zetaLo w : @& Array E) (curClaims : Array ColumnClaim) (curPs : ProverState) :
    E × Array ColumnClaim × ProverState :=
  foldRange blk.coords.size
    (fun (inAcc, cAcc, pAcc) i =>
      let wi := w[i]?.getD zero
      match blk.coords[i]?.getD (cConst 0) with
      | .atom (.const v) =>
        (eadd inAcc (mulBase wi v), cAcc, pAcc)
      | .index =>
        (eadd inAcc (emul wi (indexMle zetaLo)), cAcc, pAcc)
      | .publicCol slot =>
        let val := mleEval (bcCols[slot]?.getD #[]) zetaLo
        (eadd inAcc (emul wi val), cAcc, pAcc)
      | .atom (.col colIdx) =>
        match findKnownClaim cAcc colIdx zetaLo with
        | some v => (eadd inAcc (emul wi v), cAcc, pAcc)
        | none =>
          let v := mleEval (cols[colIdx]?.getD #[]) zetaLo
          let pAcc' := addScalar pAcc v
          let cAcc' := cAcc.push ⟨colIdx, zetaLo, v⟩
          (eadd inAcc (emul wi v), cAcc', pAcc')
      | .atom (.gcol colIdx k) =>
        let (v, cAcc', pAcc') :=
          match findKnownClaim cAcc colIdx zetaLo with
          | some v => (v, cAcc, pAcc)
          | none =>
            let v := mleEval (cols[colIdx]?.getD #[]) zetaLo
            (v, cAcc.push ⟨colIdx, zetaLo, v⟩, addScalar pAcc v)
        let gv := mulBase v (Spec.Xmss.gpow k)
        (eadd inAcc (emul wi gv), cAcc', pAcc')
      | _ => (inAcc, cAcc, pAcc))
    (zero, curClaims, curPs)

def decomposeSideFold (blocks : @& Array Block) (lay : @& BusLayout)
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
          let form1 : BusForm := ⟨coeffs0, prods0, eadd const0 (emul eqHi beta)⟩
          let form2 := foldRange blk.coords.size
            (fun f i =>
              let c := blk.coords[i]?.getD (cConst 0)
              let wi := w[i]?.getD zero
              accumulateCoord base (emul eqHi wi) f c)
            form1
          let phiPad := foldRange blk.padding.size
            (fun pAcc i =>
              let v := blk.padding[i]?.getD 0
              let wi := w[i]?.getD zero
              eadd pAcc (mulBase wi v))
            beta
          let padTerm := emul (emul eqHi (paddingWeight zetaLo blk.rows)) (eadd one phiPad)
          (eadd acc padTerm, selSum', curForms.setIfInBounds t.val form2, curClaims, curPs)
        | none =>
          let (inner, nextClaims, nextPs) :=
            decomposeNoneCoords blk cols bcCols zetaLo w curClaims curPs
          let blockVal := emul eqHi (eadd beta inner)
          (eadd acc blockVal, selSum', curForms, nextClaims, nextPs))
    (zero, zero, forms, claims, ps)

def decomposeSide (blocks : @& Array Block) (lay : @& BusLayout)
    (cols bcCols : @& Array (Array K)) (zeta w : @& Array E) (beta : E)
    (forms : Array BusForm) (claims : Array ColumnClaim)
    (ps : ProverState) : E × Array BusForm × Array ColumnClaim × ProverState :=
  let (acc, selSum, forms, claims, ps) :=
    decomposeSideFold blocks lay cols bcCols zeta w beta forms claims ps
  (eadd acc (eadd one selSum), forms, claims, ps)

def hasPair (pairs : @& Array (Nat × Nat)) (a b : Nat) : Bool :=
  foldRange pairs.size
    (fun found idx =>
      match pairs[idx]? with
      | none => found
      | some p => found || decide (p.1 = a ∧ p.2 = b))
    false

def findProdSum (sums : @& Array (Nat × Nat × E)) (a b : Nat) : E :=
  foldRange sums.size
    (fun acc idx =>
      match sums[idx]? with
      | none => acc
      | some (pa, pb, s) => if pa = a ∧ pb = b then s else acc)
    zero

def evalBusFormSigma (form : @& BusForm) (colEvals : @& Array E)
    (prodSums : @& Array (Nat × Nat × E)) : E :=
  let lin := foldRange form.coeffs.size
    (fun acc i =>
      eadd acc (emul (form.coeffs[i]?.getD zero) (colEvals[i]?.getD zero)))
    form.constant
  foldRange form.prods.size
    (fun acc idx =>
      match form.prods[idx]? with
      | none => acc
      | some p => eadd acc (emul p.coeff (findProdSum prodSums p.colA p.colB)))
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
              (fun s z => eadd s (mulBase (eqs[z]?.getD zero) (col[z]?.getD 0)))
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
                  let prodK := mul (colA[z]?.getD 0) (colB[z]?.getD 0)
                  eadd s (mulBase (eqs[z]?.getD zero) prodK))
                zero
              acc.push (a, b, sum))
          (Array.emptyWithCapacity pairs.size)
        (s0.push (evalBusFormSigma f0 colEvals prodSums),
          s1.push (evalBusFormSigma f1 colEvals prodSums),
          s2.push (evalBusFormSigma f2 colEvals prodSums))
      else
        (s0, s1, s2))
    (init0, init1, init2)

structure BusProof where
  claims : Array ColumnClaim
  point : Array E
  forms0 : Array BusForm
  forms1 : Array BusForm
  forms2 : Array BusForm
  sigmas0 : Array E
  sigmas1 : Array E
  sigmas2 : Array E
  deriving Inhabited

def initTableForms : Array BusForm :=
  foldRange nTables
    (fun acc t =>
      if h : t < nTables then acc.push (emptyBusForm (tableWidth ⟨t, h⟩))
      else acc)
    (Array.emptyWithCapacity nTables)

def proveBalance (lay : @& Model.Layout.PublicLayout)
    (cols bcCols : @& Array (Array K)) (ps : ProverState) : BusProof × ProverState :=
  let (alphas, ps) := sampleVec ps busBits
  let w := fingerprintWeights alphas
  let cw := countWeights
  let (beta, ps) := sampleChallenge ps
  let mu := lay.pushLayout.mu
  let countLay : BusLayout := { lay.countLayout with mu := mu }
  let leaves0 := buildSideLeaves lay.push lay.pushLayout cols bcCols w beta
  let leaves1 := buildSideLeaves lay.pull lay.pullLayout cols bcCols w beta
  let leaves2 := buildSideLeaves lay.count countLay cols bcCols cw zero
  let (gkr, ps) := proveProductTriple leaves0 leaves1 leaves2 mu ps
  let zeta := gkr.point
  let (_, forms0, claims, ps) := decomposeSide lay.push lay.pushLayout cols bcCols
    zeta w beta initTableForms #[] ps
  let (_, forms1, claims, ps) := decomposeSide lay.pull lay.pullLayout cols bcCols
    zeta w beta initTableForms claims ps
  let (_, forms2, claims, ps) := decomposeSide lay.count countLay cols bcCols
    zeta cw zero initTableForms claims ps
  let (sigmas0, sigmas1, sigmas2) :=
    computeTableSigmas cols lay.taus forms0 forms1 forms2 zeta
  (⟨claims, zeta, forms0, forms1, forms2, sigmas0, sigmas1, sigmas2⟩, ps)

def jumpIdentityForm (p0 p1 : E) : BusForm :=
  let coeffs := ((Array.replicate jumpWidth zero).setIfInBounds 13 p0).setIfInBounds 5 p1
  let prods := #[⟨5, 12, p0⟩, ⟨5, 13, p1⟩]
  { coeffs, prods, constant := zero }

def tableIdentityForm (t : Nat) (p0 p1 : E) : BusForm :=
  if h : t < nTables then
    if t = opJump then jumpIdentityForm p0 p1
    else emptyBusForm (tableWidth ⟨t, h⟩)
  else
    emptyBusForm 0

def powersOf (x : E) (count : Nat) : Array E :=
  foldRange count (fun acc i => acc.push (epow x i)) (Array.emptyWithCapacity count)

structure AirTable where
  tau : Nat
  base : Nat
  nCols : Nat
  form : BusForm
  sigma : E
  deriving Inhabited

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
        let s0 := emul fPow0 (bus.sigmas0[t]?.getD zero)
        let s1 := emul fPow1 (bus.sigmas1[t]?.getD zero)
        let s2 := emul fPow2 (bus.sigmas2[t]?.getD zero)
        let sigma := eadd (eadd s0 s1) s2
        acc.push { tau := taus[t]?.getD 0, base := tableBase tf, nCols, form, sigma }
      else acc)
    (Array.emptyWithCapacity nTables)

structure GroupedForm where
  constant : E
  lin : Array (Nat × E)
  groups : Array (Nat × Array (Nat × E))
  deriving Inhabited

def mergeProdEdges (prods : @& Array ProdTerm) : Array (Nat × Nat × E) :=
  let raw := foldRange prods.size
    (fun edges idx =>
      match prods[idx]? with
      | none => edges
      | some p =>
        let a := min p.colA p.colB
        let b := max p.colA p.colB
        let (edges', found) := foldRange edges.size
          (fun (cur, hit) eIdx =>
            match cur[eIdx]? with
            | none => (cur, hit)
            | some (ea, eb, eqv) =>
              if ea = a ∧ eb = b then
                (cur.setIfInBounds eIdx (ea, eb, eadd eqv p.coeff), true)
              else (cur, hit))
          (edges, false)
        if found then edges' else edges'.push (a, b, p.coeff))
    #[]
  foldRange raw.size
    (fun acc idx =>
      match raw[idx]? with
      | none => acc
      | some (a, b, q) => if Spec.Vm.wordBEq q zero then acc else acc.push (a, b, q))
    #[]

def buildGroupedForm (form : @& BusForm) : GroupedForm :=
  let nCols := form.coeffs.size
  let lin := foldRange nCols
    (fun acc c =>
      let w := form.coeffs[c]?.getD zero
      if Spec.Vm.wordBEq w zero then acc else acc.push (c, w))
    #[]
  let edges0 := mergeProdEdges form.prods
  let (groups, _) := foldRange edges0.size
    (fun (grps, edges) _ =>
      if edges.isEmpty then (grps, edges)
      else
        let degs := foldRange edges.size
          (fun d idx =>
            match edges[idx]? with
            | none => d
            | some (a, b, _) =>
              let d1 := d.setIfInBounds a ((d[a]?.getD 0) + 1)
              if a = b then d1 else d1.setIfInBounds b ((d1[b]?.getD 0) + 1))
          (Array.replicate nCols 0)
        let (left, _) := foldRange nCols
          (fun (bestC, bestD) c =>
            let dc := degs[c]?.getD 0
            if bestD ≤ dc then (c, dc) else (bestC, bestD))
          (0, 0)
        let (right, rem) := foldRange edges.size
          (fun (rAcc, remAcc) idx =>
            match edges[idx]? with
            | none => (rAcc, remAcc)
            | some (a, b, q) =>
              if a = left ∨ b = left then
                let partner := if a = left then b else a
                (rAcc.push (partner, q), remAcc)
              else
                (rAcc, remAcc.push (a, b, q)))
          (#[], #[])
        (grps.push (left, right), rem))
    (#[], edges0)
  { constant := form.constant, lin, groups }

def evalLinK (terms : @& Array (Nat × E)) (cols : @& Array (Array K))
    (base row : Nat) : E :=
  foldRange terms.size
    (fun acc idx =>
      match terms[idx]? with
      | none => acc
      | some (c, w) =>
        let v := (cols[base + c]?.getD #[])[row]?.getD 0
        eadd acc (mulBase w v))
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
        eadd acc (mulBase w s))
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
            (eadd epG (mulBase rightEnd leftEnd),
              eadd slG (mulBase rightSum leftSum)))
        (linEnd, zero)
      let eqw := eqr[i]?.getD zero
      (eadd eAcc (emul eqw ep), eadd sAcc (emul eqw sl)))
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
              let wr := emul w r
              eadd acc (eadd (mulBase w lo) (mulBase wr (add lo hi))))
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
          (eadd epG (emul lEnd rEnd), eadd slG (emul lSum rSum)))
        (linEnd, zero)
      let eqw := eqr[i]?.getD zero
      (eadd eAcc (emul eqw ep), eadd sAcc (emul eqw sl)))
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
      (endpoint, emul (eadd (eadd claim waiting) (emul eqZ endpoint)) (einv zetaM))
  let h2 := eadd (eadd (emul eqZ quadratic) p0) (eadd p1 quadratic)
  #[emul eqZ p0, eadd (eadd claim h2) quadratic, h2, quadratic]

structure TableClaims where
  chi : Array E
  evals : Array E
  deriving Inhabited

def constraintsRoundMsgs (airs : @& Array AirTable) (gForms : @& Array GroupedForm)
    (cols : @& Array (Array K)) (weights : @& Array E)
    (states : @& Array (Option (Array (Array E)))) (eqr : @& Array E)
    (m half : Nat) (atOne : Bool) : E × E :=
  foldRange airs.size
    (fun (m0, m1) t =>
      let tau := airs[t]?.map AirTable.tau |>.getD 0
      if m < tau then
        let wt := weights[t]?.getD one
        let gf := gForms[t]?.getD default
        let base := airs[t]?.map AirTable.base |>.getD 0
        let (p0, p1) :=
          match states[t]?.join with
          | some st => tableMessageE gf.constant st eqr half atOne
          | none => tableMessageK gf cols base eqr half atOne
        (eadd m0 (emul wt p0), eadd m1 (emul wt p1))
      else (m0, m1))
    (zero, zero)

def constraintsUpdateTables (airs : @& Array AirTable) (gForms : @& Array GroupedForm)
    (cols : @& Array (Array K)) (weights : Array E)
    (states : Array (Option (Array (Array E))))
    (m half : Nat) (rk eqK : E) : Array E × Array (Option (Array (Array E))) :=
  foldRange airs.size
    (fun (wAcc, sAcc) t =>
      let tau := airs[t]?.map AirTable.tau |>.getD 0
      let wt := wAcc[t]?.getD one
      if m < tau then
        let wAcc' := wAcc.setIfInBounds t (emul wt eqK)
        let gf := gForms[t]?.getD default
        let base := airs[t]?.map AirTable.base |>.getD 0
        let nextSt :=
          match sAcc[t]?.join with
          | some st => some (foldTableState st rk half)
          | none => some (joinTableState gf cols base rk half)
        (wAcc', sAcc.setIfInBounds t nextSt)
      else
        (wAcc.setIfInBounds t (emul wt rk), sAcc))
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
          let tau := airs[t]?.map AirTable.tau |>.getD 0
          if tau ≤ m then eadd acc (airs[t]?.map AirTable.sigma |>.getD zero)
          else acc)
        zero
      let u := emul k waiting
      let (msg0, msg1) :=
        constraintsRoundMsgs airs gForms cols weights states eqr m half atOne
      let eqr' := shrinkEqHigh eqr
      let h := roundPolynomial msg0 msg1 zm claim u
      let curPs := addScalars curPs #[h[0]?.getD zero, h[2]?.getD zero, h[3]?.getD zero]
      let (rk, curPs) := sampleChallenge curPs
      let claim' := polyEval h rk
      let chi' := chi.setIfInBounds m rk
      let k' := emul k rk
      let eqK := eadd (eadd one zm) rk
      let ws' := constraintsUpdateTables airs gForms cols weights states m half rk eqK
      (eqr', chi', k', claim', ws', curPs))
    (eqr0, chi0, one, claim0, (weights0, states0), ps)

def proveConstraints (airs : @& Array AirTable) (cols : @& Array (Array K))
    (zeta : @& Array E) (ps : ProverState) : Array TableClaims × ProverState :=
  let n := foldRange airs.size
    (fun acc t => max acc (airs[t]?.map AirTable.tau |>.getD 0)) 0
  let gForms := foldRange airs.size
    (fun acc t =>
      acc.push (buildGroupedForm (airs[t]?.map AirTable.form |>.getD (emptyBusForm 0))))
    (Array.emptyWithCapacity airs.size)
  let eqr0 := eqTable (zeta.extract 0 (n - 1))
  let chi0 := Array.replicate n zero
  let claim0 := foldRange airs.size
    (fun acc t => eadd acc (airs[t]?.map AirTable.sigma |>.getD zero)) zero
  let weights0 := Array.replicate airs.size one
  let states0 : Array (Option (Array (Array E))) := Array.replicate airs.size none
  let (_, chi, _, _, _, ps) :=
    constraintsRoundsFold airs gForms cols zeta n eqr0 chi0 claim0 weights0 states0 ps
  foldRange airs.size
    (fun (claimsAcc, curPs) t =>
      let tau := airs[t]?.map AirTable.tau |>.getD 0
      let base := airs[t]?.map AirTable.base |>.getD 0
      let nCols := airs[t]?.map AirTable.nCols |>.getD 0
      let chiT := chi.extract 0 tau
      let evals := foldRange nCols
        (fun acc c => acc.push (mleEval (cols[base + c]?.getD #[]) chiT))
        (Array.emptyWithCapacity nCols)
      let curPs := addScalars curPs evals
      (claimsAcc.push ⟨chiT, evals⟩, curPs))
    (Array.emptyWithCapacity airs.size, ps)

structure SlotClaim where
  offset : Nat
  lowPoint : Array E
  value : E
  deriving Inhabited

structure OutputClaim where
  instancePoint : Array E
  lanes : Array E
  deriving Inhabited

def bindPiClaims (rPi : E) (logMem : Nat) (publicInput : @& Array E) : Array ColumnClaim :=
  let a := publicInput[0]?.getD zero
  let b := publicInput[1]?.getD zero
  let point := (Array.replicate logMem zero).setIfInBounds 0 rPi
  #[⟨memLo, point, interpK a.c0 b.c0 rPi⟩,
    ⟨memHi, point, interpK a.c1 b.c1 rPi⟩,
    ⟨memTop, point, interpK a.c2 b.c2 rPi⟩]

def routeSlotClaims (placements : @& Array (Option Placement))
    (claims : @& Array ColumnClaim) : Array SlotClaim :=
  foldRange claims.size
    (fun acc idx =>
      match claims[idx]? with
      | none => acc
      | some c =>
        let off := placements[c.col]?.join.map Placement.index |>.getD 0
        acc.push ⟨off, c.point, c.value⟩)
    (Array.emptyWithCapacity claims.size)

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
  let tc := tableClaims[opKeccak]?.getD default
  let lanes := foldRange stateLanes
    (fun acc l => acc.push (tc.evals[keccakOut + l]?.getD zero))
    (Array.emptyWithCapacity stateLanes)
  ⟨tc.chi, lanes⟩

structure BusStageOutput where
  ps : ProverState
  slotClaims : Array SlotClaim
  keccakOutput : OutputClaim
  deriving Inhabited

def proveBusAndConstraints (program : @& Array Spec.Vm.Op) (iv : ByteArray)
    (publicInput : @& Array E) (bundle : @& WitnessBundle) : BusStageOutput :=
  let ps0 := startTranscript iv publicInput bundle.sized bundle.root
  let cols := buildColumns program bundle.sized bundle.message
  let bcCols := bytecodeColumns program
  let (bus, ps1) := proveBalance bundle.sized.layout cols bcCols ps0
  let (xi, ps2) := sampleChallenge ps1
  let airs := buildAirs bundle.sized.layout.taus bus xi
  let (tableClaims, ps3) := proveConstraints airs cols bus.point ps2
  let (rPi, ps4) := sampleChallenge ps3
  let slots := finishClaims bundle.sized.layout publicInput bus.claims tableClaims rPi
  let outClaim := keccakOutputClaim tableClaims
  ⟨ps4, slots, outClaim⟩

end LeanVmXmss.Spec.Bus
