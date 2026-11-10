import Spec.Pcs.Whir
import Model.Pcs.StackOpen
import Model.Pcs.Commit
import Model.Layout.Scalar

namespace LeanVmXmss.Model.Pcs.Whir

open Spec.Field (K E)

def initialFolding := Spec.Pcs.Whir.initialFolding
def subsequentFolding := Spec.Pcs.Whir.subsequentFolding
def residualMaxLog := Spec.Pcs.Whir.residualMaxLog
def queryGrindingBits := Spec.Pcs.Whir.queryGrindingBits
def queriesAt := Spec.Pcs.Whir.queriesAt
def deriveConfig := Spec.Pcs.Whir.deriveConfig
def sampleWindow := Spec.Pcs.Whir.sampleWindow
def sampleQueries := Spec.Pcs.Whir.sampleQueries
def subspaceRoots := Spec.Pcs.Whir.subspaceRoots

def subspaceStepFast (root : K) (layer : Array K) : Array K :=
  layer.map fun value =>
    Spec.Field.add (Model.Field.nativeMul value value) (Model.Field.nativeMul root value)

def subspaceRootsFast (logN : Nat) : Array K :=
  (Array.range logN).foldl (fun (roots, layer) _ =>
    let next := subspaceStepFast (roots.back?.getD 1) layer
    (roots.push (next.getD 0 0), next.extract 1 next.size))
    (#[1], (Array.range logN).map fun i => (1 <<< UInt64.ofNat (i + 1))) |>.1

@[noinline] def columnWeight (roots inverses : Array K) (point : Array E) (query : Nat) : E :=
  (Array.range point.size).foldl (fun (basis, product) k =>
    let factor := Spec.Field.eadd Spec.Field.one
      (Model.Field.nativeKaratsuba (point.getD k Spec.Field.zero)
        (Spec.Field.embed (Spec.Field.add 1 (Model.Field.nativeMul basis (inverses.getD k 0)))))
    (Spec.Field.add (Model.Field.nativeMul basis basis) (Model.Field.nativeMul (roots.getD k 0) basis),
     Model.Field.nativeKaratsuba product factor))
    ((UInt64.ofNat query), Spec.Field.one) |>.2

def inducedWeight (messageLog : Nat) (queries : Array Nat) (weights point : Array E) : E :=
  let roots := subspaceRootsFast messageLog
  let inverses := roots.map Model.Field.nativeInv
  (Array.range (min queries.size weights.size)).foldl (fun total i =>
    Spec.Field.eadd total (Model.Field.nativeKaratsuba (weights.getD i Spec.Field.zero)
      (columnWeight roots inverses point (queries.getD i 0)))) Spec.Field.zero

@[noinline] def polyEval (coeffs : Array E) (point : E) : E :=
  coeffs.foldr (fun c acc => Spec.Field.eadd (Model.Field.nativeKaratsuba acc point) c) Spec.Field.zero

@[noinline] def multilinearEval (table : Array K) (point : Array E) : E :=
  if decide (table.size = 1 <<< point.size) then
    (Array.range point.size).foldl (fun cur k =>
      let r := point.getD k Spec.Field.zero
      let half := cur.size / 2
      (Array.range half).map fun i =>
        let lo := cur.getD (2 * i) Spec.Field.zero
        Spec.Field.eadd lo (Model.Field.nativeKaratsuba r
          (Spec.Field.eadd lo (cur.getD (2 * i + 1) Spec.Field.zero))))
      (table.map Spec.Field.embed) |>.getD 0 Spec.Field.zero
  else Spec.Field.zero

def terminal (residual : Array K) (folds : Array E) (weight : E) : E :=
  Model.Field.nativeKaratsuba weight (multilinearEval residual folds)

def laneDot (row weights : Array E) : E :=
  (Array.range (min row.size weights.size)).foldl (fun acc i =>
    Spec.Field.eadd acc (Model.Field.nativeKaratsuba (row.getD i Spec.Field.zero)
      (weights.getD i Spec.Field.zero))) Spec.Field.zero

@[noinline] def eqKernel (point : Array E) : Array E :=
  point.foldl (fun out r =>
    let high := out.map (fun v => Model.Field.nativeKaratsuba v r)
    out.mapIdx (fun i v => Spec.Field.eadd v (high.getD i Spec.Field.zero)) ++ high) #[Spec.Field.one]

def powers (x : E) (n : Nat) : Array E :=
  (Array.range n).foldl (fun (acc, cur) _ =>
    (acc.push cur, Model.Field.nativeKaratsuba cur x)) (#[], Spec.Field.one) |>.1

def dot (left right : Array E) : E :=
  (Array.range (min left.size right.size)).foldl (fun acc i =>
    Spec.Field.eadd acc (Model.Field.nativeKaratsuba (left.getD i Spec.Field.zero)
      (right.getD i Spec.Field.zero))) Spec.Field.zero

def ClaimWeight.eval (w : Spec.Pcs.Whir.ClaimWeight) (point : Array E) : Option E :=
  match w with
  | .ood oodPoint =>
    if decide (oodPoint.size = point.size) then some (StackOpen.eqEval oodPoint point) else none
  | .induced messageLog queries queryWeights =>
    if decide (point.size = messageLog) then some (inducedWeight messageLog queries queryWeights point) else none

def baseRowDot (row : Array K) (weights : Array E) : E :=
  (Array.range (min row.size weights.size)).foldl (fun acc i =>
    Spec.Field.eadd acc (RingSwitch.nativeMulBase (weights.getD i Spec.Field.zero)
      (row.getD (row.size - 1 - i) 0))) Spec.Field.zero

def extRow := Spec.Pcs.Whir.extRow
def levelLeafWords := Spec.Pcs.Whir.levelLeafWords
def levelRowWords := Spec.Pcs.Whir.levelRowWords
def shapeOk := Spec.Pcs.Whir.shapeOk

def addScaled (base : Array E) (scale : E) (extra : Array E) : Array E :=
  (Array.range (min base.size extra.size)).foldl
    (fun acc i => acc.setIfInBounds i
      (Spec.Field.eadd (acc.getD i Spec.Field.zero)
        (Model.Field.nativeKaratsuba scale (extra.getD i Spec.Field.zero)))) base

def verifierSamples (s : Spec.Transcript.VerifierState) (n : Nat) : Array E × Spec.Transcript.VerifierState :=
  (Array.range n).foldl (fun (acc, s) _ =>
    let (x, s) := Spec.Transcript.verifierSample s
    (acc.push x, s)) (#[], s)

abbrev LevelState := Spec.Pcs.Whir.LevelState

def verifyLevel (config : Spec.Pcs.Whir.Config) (logN placed : Nat) (ls : LevelState) (level : Nat) :
    Option LevelState := do
  let foldCount := config.folds.getD level 0
  let (quad, levelFolds, folds, s) ← (Array.range foldCount).foldlM
    (fun (quad, levelFolds, folds, s) _ => do
      let (challenge, s) := Spec.Transcript.verifierSample s
      let (quad, s) ← Spec.Transcript.sumcheckRoundPoly s 3 (polyEval quad challenge) none
      some (quad, levelFolds.push challenge, folds.push challenge, s))
    (ls.quad, #[], ls.folds, ls.state)
  let messageLog := logN - folds.size
  let finalLevel := decide (level + 1 = config.folds.size)
  let (residual, nextRoot, pending, s) ←
    if finalLevel then
      let (residual, s) ← Spec.Transcript.nextScalars (1 <<< messageLog) s
      pure (residual, ls.root, (#[] : Array (Array E × Spec.Pcs.Whir.ClaimWeight)), s)
    else
      let (halves, s) ← Spec.Transcript.nextScalars 2 s
      let next ← Spec.Merkle.fromHalves (halves.getD 0 Spec.Field.zero) (halves.getD 1 Spec.Field.zero)
      let (oodPoint, s) := verifierSamples s messageLog
      let (oodValue, s) ← Spec.Transcript.nextScalar s
      let (intro, s) ← Spec.Transcript.sumcheckRoundPoly s 3 oodValue none
      pure (#[], next, #[(intro, Spec.Pcs.Whir.ClaimWeight.ood oodPoint)], s)
  let s ← Spec.Transcript.grindCheck s queryGrindingBits
  let blockLog := messageLog + config.logInvRates.getD level 0
  let count := config.queries.getD level 0
  let perWord := if blockLog = 0 then 0 else 192 / blockLog
  if perWord = 0 then none else
    let needed := (count + perWord - 1) / perWord
    let (drawn, s) := verifierSamples s needed
    let queries := sampleQueries count blockLog drawn
    let (lam, s) := Spec.Transcript.verifierSample s
    let queryWeights := powers lam queries.size
    let leafWords := levelLeafWords level foldCount
    let rowWords := levelRowWords level foldCount messageLog placed
    let (leaves, s) ← Spec.Transcript.merkle s ls.root blockLog queries rowWords leafWords
    let laneWeights := eqKernel levelFolds
    let rowValues :=
      if level = 0 then
        leaves.map fun leaf =>
          baseRowDot (leaf.extract (leafWords - rowWords) leafWords) laneWeights
      else
        leaves.map fun leaf => laneDot (extRow leaf) laneWeights
    let (intro, s) ← Spec.Transcript.sumcheckRoundPoly s 3 (dot rowValues queryWeights) none
    let pending := pending.push (intro, Spec.Pcs.Whir.ClaimWeight.induced messageLog queries queryWeights)
    let (quad, _, glued) := pending.foldl (fun (quad, scalar, glued) item =>
      let scalar := Model.Field.nativeKaratsuba scalar lam
      (addScaled quad scalar item.1, scalar, glued.push ⟨scalar, folds.size, item.2⟩))
      (quad, Spec.Field.one, ls.glued)
    some ⟨quad, folds, glued, nextRoot, residual, s⟩

def verifyWhir (s : Spec.Transcript.VerifierState) (logN placed logInvRate : Nat) (target : E)
    (root : Spec.Merkle.Digest) (evaluateBasis : Array E → E) : Option Spec.Transcript.VerifierState := do
  let config ← deriveConfig logN logInvRate
  if config.folds.isEmpty then none else
    let (quad0, s) ← Spec.Transcript.sumcheckRoundPoly s 3 target none
    let done ← (Array.range config.folds.size).foldlM (verifyLevel config logN placed)
      ⟨quad0, #[], #[], root, #[], s⟩
    let messageLog := logN - done.folds.size
    let (_, tail, running, s) ← (Array.range messageLog).foldlM
      (fun (quad, tail, _, s) k => do
        let (challenge, s) := Spec.Transcript.verifierSample s
        let running := polyEval quad challenge
        if k + 1 < messageLog then
          let (quad, s) ← Spec.Transcript.sumcheckRoundPoly s 3 running none
          some (quad, tail.push challenge, running, s)
        else
          some (quad, tail.push challenge, running, s))
      (done.quad, #[], Spec.Field.zero, done.state)
    if !(done.residual.all fun v => decide (v.c1 = 0 ∧ v.c2 = 0)) then none else
      let residualK := done.residual.map (·.c0)
      let point := done.folds ++ tail
      let laneFolds := config.folds.getD 0 0
      let reordered := point.extract laneFolds point.size ++ point.extract 0 laneFolds
      let weight ← done.glued.foldlM (fun acc claim => do
        let w ← ClaimWeight.eval claim.weight (point.extract claim.foldStart point.size)
        some (Spec.Field.eadd acc (Model.Field.nativeKaratsuba claim.scalar w))) (evaluateBasis reordered)
      if decide (1 <<< tail.size = residualK.size) &&
          Spec.Vm.wordBEq (terminal residualK tail weight) running then
        some s
      else none

def verifyStackedOpening (s : Spec.Transcript.VerifierState) (root : Spec.Merkle.Digest)
    (stackLog placed logInvRate : Nat) (values : Array E)
    (weightsAt : Array E → Array E) : Option Spec.Transcript.VerifierState := do
  let (lam, s) := Spec.Transcript.verifierSample s
  let scales := powers lam values.size
  let target := dot scales values
  verifyWhir s stackLog placed logInvRate target root (fun point => dot scales (weightsAt point))

def verifyRingSwitchAndStacked (s : Spec.Transcript.VerifierState) (root : Spec.Merkle.Digest)
    (stackLog placed logInvRate : Nat) (qkeccak : Spec.Pcs.StackOpen.Placement)
    (ringPoint slices : Array E) (claims : Array Spec.Pcs.Whir.PlacedClaim) :
    Option Spec.Transcript.VerifierState := do
  let (challenges, s) := verifierSamples s RingSwitch.compositionShifts.size
  let coefficients := RingSwitch.frobeniusCoefficients challenges
  let images := slices.map fun v => RingSwitch.applyComposed v challenges
  let ringTarget := polyEval images ⟨2, 0, 0⟩
  let values := #[ringTarget] ++ claims.map (·.value)
  let weightsAt (x : Array E) : Array E :=
    let rw := Model.Field.nativeKaratsuba (StackOpen.eqAbove qkeccak x)
      (RingSwitch.ringWeightAt ringPoint (x.extract 0 qkeccak.variables) coefficients)
    #[rw] ++ claims.map fun c => StackOpen.place c.placement c.point x
  verifyStackedOpening s root stackLog placed logInvRate values weightsAt

def sumcheckMsgEvenOdd (f b : Array E) : E × E :=
  let pairs := min (f.size / 2) (b.size / 2)
  (Array.range pairs).foldl (fun (u0, u2) i =>
    let f0 := f.getD (2 * i) Spec.Field.zero
    let f1 := f.getD (2 * i + 1) Spec.Field.zero
    let b0 := b.getD (2 * i) Spec.Field.zero
    let b1 := b.getD (2 * i + 1) Spec.Field.zero
    (Spec.Field.eadd u0 (Model.Field.nativeKaratsuba f0 b0),
     Spec.Field.eadd u2 (Model.Field.nativeKaratsuba (Spec.Field.eadd f0 f1) (Spec.Field.eadd b0 b1))))
    (Spec.Field.zero, Spec.Field.zero)

def foldEvenOdd (xs : Array E) (r : E) : Array E :=
  (Array.range (xs.size / 2)).map fun i =>
    let lo := xs.getD (2 * i) Spec.Field.zero
    Spec.Field.eadd lo (Model.Field.nativeKaratsuba r
      (Spec.Field.eadd lo (xs.getD (2 * i + 1) Spec.Field.zero)))

def sumcheckMsgBlocks (blockLen : Nat) (f b : Array E) : E × E :=
  let nBlocks := (min f.size b.size) / blockLen
  let pairs := (nBlocks + 1) / 2
  (Array.range pairs).foldl (fun (u0, u2) p =>
    let base0 := (2 * p) * blockLen
    let base1 := (2 * p + 1) * blockLen
    if decide (2 * p + 1 < nBlocks) then
      (Array.range blockLen).foldl (fun (u0, u2) k =>
        let f0 := f.getD (base0 + k) Spec.Field.zero
        let f1 := f.getD (base1 + k) Spec.Field.zero
        let b0 := b.getD (base0 + k) Spec.Field.zero
        let b1 := b.getD (base1 + k) Spec.Field.zero
        (Spec.Field.eadd u0 (Model.Field.nativeKaratsuba f0 b0),
         Spec.Field.eadd u2 (Model.Field.nativeKaratsuba (Spec.Field.eadd f0 f1) (Spec.Field.eadd b0 b1)))) (u0, u2)
    else
      let lone := (Array.range blockLen).foldl (fun acc k =>
        Spec.Field.eadd acc (Model.Field.nativeKaratsuba (f.getD (base0 + k) Spec.Field.zero)
          (b.getD (base0 + k) Spec.Field.zero))) Spec.Field.zero
      (Spec.Field.eadd u0 lone, Spec.Field.eadd u2 lone)) (Spec.Field.zero, Spec.Field.zero)

def foldBlocks (blockLen : Nat) (xs : Array E) (r : E) : Array E :=
  let nBlocks := xs.size / blockLen
  let pairs := (nBlocks + 1) / 2
  let onePlusR := Spec.Field.eadd Spec.Field.one r
  (Array.range pairs).foldl (fun out p =>
    let base0 := (2 * p) * blockLen
    let base1 := (2 * p + 1) * blockLen
    if decide (2 * p + 1 < nBlocks) then
      (Array.range blockLen).foldl (fun out k =>
        let lo := xs.getD (base0 + k) Spec.Field.zero
        out.push (Spec.Field.eadd lo (Model.Field.nativeKaratsuba r
          (Spec.Field.eadd lo (xs.getD (base1 + k) Spec.Field.zero))))) out
    else
      (Array.range blockLen).foldl (fun out k =>
        out.push (Model.Field.nativeKaratsuba onePlusR (xs.getD (base0 + k) Spec.Field.zero))) out) #[]

def encodeExt (poly : Array E) (logNumInterleaved logInvRate : Nat) : Array K :=
  let width := 3 * (1 <<< logNumInterleaved)
  let rate := 1 <<< logInvRate
  Model.Pcs.Ntt.encode (Spec.Pcs.Commit.replicate (Spec.Pcs.Whir.extWords poly) rate) width logInvRate

def l0Rows (message : Array K) (lanes logRows logInvRate : Nat) : Array (Array K) :=
  let width := Spec.Pcs.Commit.rowWords lanes
  let code := Model.Pcs.Commit.encodeMessage message lanes logRows logInvRate
  (Array.range (code.size / width)).map fun pos =>
    (code.extract (pos * width) ((pos + 1) * width)).extract (width - lanes) width

def hashRowFast (row : Array K) (leafWords : Nat) : Spec.Merkle.Digest :=
  Spec.Merkle.toDigest (Model.Layout.keccak256Fast (Spec.Merkle.leafImage row leafWords))

def compressFast (left right : Spec.Merkle.Digest) : Spec.Merkle.Digest :=
  Spec.Merkle.toDigest (Model.Layout.keccak256Fast
    (Spec.Merkle.digestBytes left ++ Spec.Merkle.digestBytes right))

def parentLevelFast (nodes : Array Spec.Merkle.Digest) : Array Spec.Merkle.Digest :=
  (Array.range (nodes.size / 2)).map fun i =>
    compressFast (nodes.getD (2 * i) default) (nodes.getD (2 * i + 1) default)

def buildLevelsFast (depth : Nat) (leaves : Array Spec.Merkle.Digest) :
    Array (Array Spec.Merkle.Digest) :=
  ((Array.range depth).foldl (fun (tree, cur) _ =>
    let next := parentLevelFast cur
    (tree.push next, next)) (#[leaves], leaves)).1

def openRowsModel (rows : Array (Array K)) (queries : Array Nat) (depth leafWords : Nat) :
    Option Spec.Merkle.PrunedMerklePaths := do
  let indices := Spec.Merkle.sortedUnique queries
  if decide (rows.size ≠ 2 ^ depth) || !rows.all (fun row => decide (row.size ≤ leafWords)) ||
      !Spec.Merkle.validIndices depth indices then none else
    let tree := buildLevelsFast depth (rows.map fun row => hashRowFast row leafWords)
    some ⟨indices.map (fun i => rows.getD i #[]), Spec.Pcs.Whir.pruneTree depth tree indices.toList⟩

def commitExt (poly : Array E) (logNumInterleaved logInvRate : Nat) : Array (Array K) × ByteArray :=
  let width := 3 * (1 <<< logNumInterleaved)
  let rows := Spec.Pcs.Whir.extRows (encodeExt poly logNumInterleaved logInvRate) width
  let leaves := rows.map fun row => hashRowFast row width
  (rows, Spec.Merkle.digestBytes (Spec.Merkle.treeRoot
    (buildLevelsFast (rows.size.log2) leaves)))

def eqTable (point : Array E) : Array E :=
  point.foldl (fun out r =>
    let high := out.map (fun v => Model.Field.nativeKaratsuba v r)
    out.mapIdx (fun i v => Spec.Field.eadd v (high.getD i Spec.Field.zero)) ++ high) #[Spec.Field.one]

def evalAt (table point : Array E) : E :=
  if decide (table.size = 1 <<< point.size) then
    (Array.range point.size).foldl (fun cur k => foldEvenOdd cur (point.getD k Spec.Field.zero)) table
      |>.getD 0 Spec.Field.zero
  else Spec.Field.zero

def queryScalesFast (log : Nat) (query : Nat) : Array E :=
  let roots := subspaceRootsFast log
  let inverses := roots.map Model.Field.nativeInv
  ((Array.range log).foldl (fun (basis, acc) k =>
    let c := Spec.Field.embed (Spec.Field.add 1
      (Model.Field.nativeMul basis (inverses.getD k 0)))
    (Spec.Field.add (Model.Field.nativeMul basis basis)
      (Model.Field.nativeMul (roots.getD k 0) basis), acc.push c))
    ((UInt64.ofNat query), #[])).2

def booleanScale (poly : Array E) (c : E) : Array E :=
  poly ++ poly.map (fun v => Spec.Field.eadd v (Model.Field.nativeKaratsuba v c))

def inducedBasis (messageLog : Nat) (queries : Array Nat) (weights : Array E) : Array E :=
  let n := min queries.size weights.size
  (Array.range n).foldl (fun acc i =>
    let poly := (queryScalesFast messageLog (queries.getD i 0)).foldl booleanScale #[Spec.Field.one]
    let w := weights.getD i Spec.Field.zero
    (Array.range (1 <<< messageLog)).foldl (fun out j =>
      out.push (Spec.Field.eadd (acc.getD j Spec.Field.zero)
        (Model.Field.nativeKaratsuba w (poly.getD j Spec.Field.zero)))) #[]) #[]

def rowDot (row : Array K) (weights : Array E) : E := laneDot (extRow row) weights

def enforcedSum (level : Nat) (rows : Array (Array K)) (queries : Array Nat)
    (laneFolds weights : Array E) : E :=
  let kernel := eqKernel laneFolds
  let values := queries.map fun q =>
    let row := rows.getD q #[]
    if level = 0 then baseRowDot row kernel else rowDot row kernel
  dot values weights

def gluePending (basis : Array E) (claim : E) (quad : Array E) (lambda : E)
    (pending : Array Spec.Pcs.Whir.PendingClaim) : Array E × E × Array E :=
  let (_, basis, claim, quad) := pending.foldl (fun (scalar, basis, claim, quad) item =>
    let scalar := Model.Field.nativeKaratsuba scalar lambda
    (scalar, addScaled basis scalar item.basis,
     Spec.Field.eadd claim (Model.Field.nativeKaratsuba scalar item.value),
     addScaled quad scalar item.quad)) (Spec.Field.one, basis, claim, quad)
  (basis, claim, quad)

def introduceOod (f : Array E) (s : Spec.Transcript.ProverState) (nVars : Nat) :
    Spec.Pcs.Whir.PendingClaim × Spec.Transcript.ProverState :=
  let (z, s) := Spec.Pcs.Whir.proverSamples s nVars
  let basis := eqTable z
  let (u0, u2) := sumcheckMsgEvenOdd f basis
  let value := evalAt f z
  let s := Spec.Transcript.addScalar s value
  let (quad, s) := Spec.Pcs.Whir.sendRound s value u0 u2
  (⟨basis, value, quad⟩, s)

def stepFold (p : Spec.Pcs.Whir.ProverFold) : Spec.Pcs.Whir.ProverFold :=
  let (r, s) := Spec.Transcript.sample p.state
  let claim := polyEval p.quad r
  let f := foldEvenOdd p.f r
  let basis := foldEvenOdd p.basis r
  let (u0, u2) := sumcheckMsgEvenOdd f basis
  let (quad, s) := Spec.Pcs.Whir.sendRound s claim u0 u2
  ⟨f, basis, claim, quad, p.pending, p.folds.push r, s⟩

def absorbFold (p : Spec.Pcs.Whir.ProverFold) : Spec.Pcs.Whir.ProverFold :=
  let (r, s) := Spec.Transcript.sample p.state
  ⟨foldEvenOdd p.f r, foldEvenOdd p.basis r, polyEval p.quad r, p.quad, p.pending,
    p.folds.push r, s⟩

def foldTimes (p : Spec.Pcs.Whir.ProverFold) (n : Nat) : Spec.Pcs.Whir.ProverFold :=
  (Array.range n).foldl (fun p _ => stepFold p) p

def stepLaneFold (laneBlock : Nat) (last : Bool) (p : Spec.Pcs.Whir.ProverFold) :
    Spec.Pcs.Whir.ProverFold :=
  let (r, s) := Spec.Transcript.sample p.state
  let claim := polyEval p.quad r
  let f := foldBlocks laneBlock p.f r
  let basis := foldBlocks laneBlock p.basis r
  let (u0, u2) :=
    if last then sumcheckMsgEvenOdd f basis else sumcheckMsgBlocks laneBlock f basis
  let (quad, s) := Spec.Pcs.Whir.sendRound s claim u0 u2
  ⟨f, basis, claim, quad, p.pending, p.folds.push r, s⟩

def startLaneFold (laneBlock : Nat) (f basis : Array E) (target : E)
    (s : Spec.Transcript.ProverState) : Spec.Pcs.Whir.ProverFold :=
  let (u0, u2) := sumcheckMsgBlocks laneBlock f basis
  let (quad, s) := Spec.Pcs.Whir.sendRound s target u0 u2
  ⟨f, basis, target, quad, #[], #[], s⟩

def state25Of (a : Array UInt64) : Model.Keccak.State25 :=
  ⟨a.getD 0 0, a.getD 1 0, a.getD 2 0, a.getD 3 0, a.getD 4 0,
   a.getD 5 0, a.getD 6 0, a.getD 7 0, a.getD 8 0, a.getD 9 0,
   a.getD 10 0, a.getD 11 0, a.getD 12 0, a.getD 13 0, a.getD 14 0,
   a.getD 15 0, a.getD 16 0, a.getD 17 0, a.getD 18 0, a.getD 19 0,
   a.getD 20 0, a.getD 21 0, a.getD 22 0, a.getD 23 0, a.getD 24 0⟩

@[inline] def absorbNonce25 (st : Model.Keccak.State25) (pending : Nat) (n : UInt64) :
    Model.Keccak.State25 :=
  match pending with
  | 0 => { st with a00 := n, a01 := 0, a02 := 0, a03 := 4 }
  | 1 => { st with a04 := n, a05 := 0, a06 := 0, a07 := 4 }
  | 2 => { st with a08 := n, a09 := 0, a10 := 0, a11 := 4 }
  | _ => { st with a12 := n, a13 := 0, a14 := 0, a15 := 4 }

def grindWhirFast (s : Spec.Transcript.ProverState) (bits : Nat) :
    Option Spec.Transcript.ProverState :=
  if decide (s.sponge.state.size = 25 ∧ s.sponge.pending ≤ 4) then
    if bits ≥ 64 then none else
    let s0 := if s.sponge.pending == 4 then
      let out := Model.Keccak.keccakF1600 (state25Of s.sponge.state)
      (⟨(Model.Keccak.State25.mk 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
        out.a16 out.a17 out.a18 out.a19 out.a20 out.a21 out.a22 out.a23 out.a24).toSpec, 0⟩ :
        Spec.Transcript.Sponge)
      else s.sponge
    let st0 := state25Of s0.state
    let m := Spec.Transcript.mask bits
    let found :=
      if bits = 0 then some 0
      else
        Fin.foldl Spec.Pcs.Whir.grindFuel (fun acc k =>
          match acc with
          | some _ => acc
          | none =>
            let n := UInt64.ofNat k.val
            if decide ((Model.Keccak.keccakF1600 (absorbNonce25 st0 s0.pending n)).a00 &&& m = 0)
            then some n else none) none
    found.map fun n =>
      { s with sponge := (Spec.Transcript.nonceProbe s.sponge ⟨n, 0, 0⟩).2,
               stream := s.stream.push ⟨n, 0, 0⟩ }
  else
    Spec.Pcs.Whir.grindWhir s bits

def foldLanes (laneBlock foldCount : Nat) (p : Spec.Pcs.Whir.ProverFold) :
    Spec.Pcs.Whir.ProverFold :=
  (Array.range foldCount).foldl
    (fun p j => stepLaneFold laneBlock (decide (j + 1 = foldCount)) p) p

def proveLevel (config : Spec.Pcs.Whir.Config) (logN : Nat) (p : Spec.Pcs.Whir.ProverFold)
    (level : Nat) (rows : Array (Array K)) :
    Option (Spec.Pcs.Whir.ProverFold × Array (Array K)) := do
  let foldCount := config.folds.getD level 0
  let laneBlock := 1 <<< (logN - config.folds.getD 0 0)
  let p :=
    if level = 0 then foldLanes laneBlock foldCount p else foldTimes p foldCount
  let messageLog := logN - p.folds.size
  let finalLevel := decide (level + 1 = config.folds.size)
  let (p, nextRows) ←
    if finalLevel then
      let s := Spec.Transcript.addScalars p.state p.f
      pure ((⟨p.f, p.basis, p.claim, p.quad, p.pending, p.folds, s⟩ : Spec.Pcs.Whir.ProverFold), rows)
    else
      let (nextRows, root) := commitExt p.f (config.folds.getD (level + 1) 0)
        (config.logInvRates.getD (level + 1) 0)
      let s := Spec.Transcript.addRoot p.state root
      let (ood, s) := introduceOod p.f s messageLog
      pure ((⟨p.f, p.basis, p.claim, p.quad, p.pending.push ood, p.folds, s⟩ : Spec.Pcs.Whir.ProverFold), nextRows)
  let s ← grindWhirFast p.state queryGrindingBits
  let rate := config.logInvRates.getD level 0
  let blockLog := messageLog + rate
  let count := config.queries.getD level 0
  let perWord := 192 / blockLog
  if perWord = 0 then none else
    let (drawn, s) := Spec.Pcs.Whir.proverSamples s ((count + perWord - 1) / perWord)
    let queries := sampleQueries count blockLog drawn
    let (lam, s) := Spec.Transcript.sample s
    let weights := powers lam queries.size
    let phase ← openRowsModel rows queries blockLog (levelLeafWords level foldCount)
    let s := Spec.Pcs.Whir.hintPhase s phase
    let laneFolds := p.folds.extract (p.folds.size - foldCount) p.folds.size
    let enforced := enforcedSum level rows queries laneFolds weights
    let basisI := inducedBasis messageLog queries weights
    let (u0, u2) := sumcheckMsgEvenOdd p.f basisI
    let (quadI, s) := Spec.Pcs.Whir.sendRound s enforced u0 u2
    let (basis, claim, quad) := gluePending p.basis p.claim p.quad lam
      (p.pending.push ⟨basisI, enforced, quadI⟩)
    some (⟨p.f, basis, claim, quad, #[], p.folds, s⟩, nextRows)

def proveWhir (s : Spec.Transcript.ProverState) (logN logInvRate : Nat) (witness : Array K)
    (weight : Array E) (target : E) : Option Spec.Transcript.ProverState := do
  let config ← deriveConfig logN logInvRate
  if config.folds.isEmpty then none else
    let k0 := config.folds.getD 0 0
    let laneBlock := 1 <<< (logN - k0)
    if decide (witness.size = 0 ∨ witness.size % laneBlock ≠ 0) then none else
      let lanes := witness.size / laneBlock
      let rows0 := l0Rows witness lanes (logN - k0) (config.logInvRates.getD 0 0)
      let p0 := startLaneFold laneBlock (witness.map Spec.Field.embed)
        (weight.extract 0 witness.size) target s
      let (done, _) ← (Array.range config.folds.size).foldlM
        (fun (p, rows) level => proveLevel config logN p level rows) (p0, rows0)
      let resLog := logN - done.folds.size
      let done := (Array.range resLog).foldl (fun p j =>
        if decide (j + 1 < resLog) then stepFold p else absorbFold p) done
      some done.state

def proveStackedOpening (s : Spec.Transcript.ProverState) (stackLog logInvRate : Nat)
    (witness : Array K) (values : Array E) (basisTables : Array (Array E)) :
    Option Spec.Transcript.ProverState := do
  if decide (values.size ≠ basisTables.size) then none else
    let (lam, s) := Spec.Transcript.sample s
    let scales := powers lam values.size
    let target := dot scales values
    let combined := (Array.range values.size).foldl (fun acc i =>
      addScaled acc (scales.getD i Spec.Field.zero) (basisTables.getD i #[]))
      (Array.replicate witness.size Spec.Field.zero)
    proveWhir s stackLog logInvRate witness combined target

def stackedWeight (n : Nat) (lambda : E) (points : Array Spec.Pcs.StackOpen.StackClaim)
    (ring : Spec.Pcs.StackOpen.RingSwitchOpen) (ringWeights : Array (Array E)) : Array E :=
  let scales := powers lambda (ring.claims.size + points.size)
  let base := Array.replicate n Spec.Field.zero
  let placed := (Array.range points.size).foldl (fun acc i =>
    match points[i]? with
    | none => acc
    | some (.point offset low _) =>
      let w := scales.getD (ring.claims.size + i) Spec.Field.zero
      let eq := eqKernel low
      (Array.range eq.size).foldl (fun acc j =>
        let idx := offset + j
        acc.setIfInBounds idx (Spec.Field.eadd (acc.getD idx Spec.Field.zero)
          (Model.Field.nativeKaratsuba w (eq.getD j Spec.Field.zero)))) acc) base
  (Array.range ring.claims.size).foldl (fun acc i =>
    let claim := ring.claims.getD i default
    let weights := ringWeights.getD i #[]
    let eq := eqKernel claim.suffixPoint
    (Array.range eq.size).foldl (fun acc j =>
      let idx := ring.offset + j
      let word := Spec.Pcs.Whir.applyLinearMap weights (eq.getD j Spec.Field.zero)
      acc.setIfInBounds idx (Spec.Field.eadd (acc.getD idx Spec.Field.zero) word)) acc) placed

def provePcsOpen (s : Spec.Transcript.ProverState) (stackLog logInvRate : Nat) (witness : Array K)
    (points : Array Spec.Pcs.StackOpen.StackClaim) (ring : Spec.Pcs.StackOpen.RingSwitchOpen) :
    Option Spec.Transcript.ProverState := do
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
  let weight := stackedWeight witness.size lam points ring ringWeights
  proveWhir s stackLog logInvRate witness weight target

end LeanVmXmss.Model.Pcs.Whir
