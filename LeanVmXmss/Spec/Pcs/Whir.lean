import Spec.Pcs.StackOpen
import Spec.Pcs.Commit
import Spec.Merkle.Pruned
import Spec.Transcript.Replay
import Spec.Vm.Equality

namespace LeanVmXmss.Spec.Pcs.Whir

open Spec.Field (K E zero one eadd emul embed mulBase)
open Spec.Transcript (VerifierState ProverState)

def initialFolding : Nat := 6
def subsequentFolding : Nat := 4
def rsInitialReduction : Nat := 3
def rsSubsequentReduction : Nat := 1
def residualMaxLog : Nat := 5
def queryGrindingBits : Nat := 17
def minStackedLog : Nat := 15
def maxStackedLog : Nat := 28
def securityBits : Nat := 128

def queriesAt (logInvRate logN : Nat) : Array Nat :=
  let table : Array (Array (Array Nat)) := #[
    #[#[222, 55], #[223, 56, 30], #[223, 56, 31], #[223, 56, 32], #[223, 56, 32],
      #[223, 56, 32, 22], #[223, 56, 32, 22], #[224, 56, 32, 23], #[224, 56, 32, 23],
      #[224, 56, 32, 23, 17], #[224, 56, 32, 23, 17], #[224, 56, 32, 23, 18],
      #[225, 56, 32, 23, 18], #[225, 56, 32, 23, 18, 14]],
    #[#[111, 45], #[112, 45, 27], #[112, 45, 28], #[112, 45, 28], #[112, 45, 28],
      #[112, 45, 28, 20], #[112, 45, 28, 20], #[112, 45, 28, 21], #[112, 45, 28, 21],
      #[112, 45, 28, 21, 16], #[112, 45, 28, 21, 16], #[112, 45, 28, 21, 16],
      #[112, 45, 28, 21, 16], #[112, 45, 28, 21, 16, 13]],
    #[#[75, 37], #[75, 37, 24], #[75, 37, 25], #[75, 38, 25], #[75, 38, 25],
      #[75, 38, 25, 18], #[75, 38, 25, 19], #[75, 38, 25, 19], #[75, 38, 25, 19],
      #[75, 38, 25, 19, 15], #[75, 38, 25, 19, 15], #[75, 38, 25, 19, 15],
      #[75, 38, 25, 19, 15], #[75, 38, 25, 19, 15, 13]],
    #[#[56, 32], #[56, 32, 22], #[56, 32, 22], #[56, 32, 23], #[56, 32, 23],
      #[56, 32, 23, 17], #[56, 32, 23, 17], #[56, 32, 23, 18], #[56, 32, 23, 18],
      #[56, 32, 23, 18, 14], #[56, 32, 23, 18, 14], #[56, 32, 23, 18, 14],
      #[56, 32, 23, 18, 15], #[56, 32, 23, 18, 15, 12]]]
  if decide (1 ≤ logInvRate ∧ logInvRate ≤ 4 ∧ minStackedLog ≤ logN ∧ logN ≤ maxStackedLog) then
    (table.getD (logInvRate - 1) #[]).getD (logN - minStackedLog) #[]
  else #[]

structure Config where
  logInvRates : Array Nat
  folds : Array Nat
  queries : Array Nat
  deriving Inhabited, DecidableEq

def deriveConfig (logN logInvRate : Nat) : Option Config :=
  if !(decide (minStackedLog ≤ logN ∧ logN ≤ maxStackedLog ∧ 1 ≤ logInvRate ∧ logInvRate ≤ 4)) then
    none
  else
    let climbed := (Array.range (logN - initialFolding)).foldl
      (fun (state : Nat × Array Nat × Array Nat) _ =>
        let remaining := state.1
        let folds := state.2.1
        let rates := state.2.2
        if remaining > residualMaxLog then
          let reduction := if folds.size = 1 then rsInitialReduction else rsSubsequentReduction
          let fold := min subsequentFolding remaining
          (remaining - fold, folds.push fold,
            rates.push (rates.back?.getD logInvRate + folds.back?.getD initialFolding - reduction))
        else state)
      (logN - initialFolding, #[initialFolding], #[logInvRate])
    let queries := queriesAt logInvRate logN
    let folds := climbed.2.1
    if decide (queries.size = folds.size) then some ⟨climbed.2.2, folds, queries⟩ else none

def extRow (words : Array K) : Array E :=
  (Array.range (words.size / 3)).map fun i =>
    ⟨words.getD (3 * i) 0, words.getD (3 * i + 1) 0, words.getD (3 * i + 2) 0⟩

def sampleWindow (sample : E) (depth chunk : Nat) : Nat :=
  let limb := chunk * depth / 64
  let shift := chunk * depth % 64
  let bits := #[sample.c0.toNat, sample.c1.toNat, sample.c2.toNat, 0]
  let window := (bits.getD limb 0 + bits.getD (limb + 1) 0 * 2 ^ 64) >>> shift
  window &&& ((1 <<< depth) - 1)

def sampleQueries (count blockLog : Nat) (samples : Array E) : Array Nat :=
  let perWord := if blockLog = 0 then 0 else 192 / blockLog
  if perWord = 0 then #[] else
    let needed := (count + perWord - 1) / perWord
    (Array.range (min needed samples.size)).foldl (fun (produced, acc) si =>
      if produced ≥ count then (produced, acc) else
        let n := min perWord (count - produced)
        (produced + n, (Array.range n).foldl (fun acc chunk =>
          acc.push (sampleWindow (samples.getD si zero) blockLog chunk)) acc))
      (0, #[]) |>.2

def subspaceStep (root : K) (layer : Array K) : Array K :=
  layer.map fun value => Spec.Field.add (Spec.Field.square value) (Spec.Field.mul root value)

def subspaceRoots (logN : Nat) : Array K :=
  (Array.range logN).foldl (fun (roots, layer) _ =>
    let next := subspaceStep (roots.back?.getD 1) layer
    (roots.push (next.getD 0 0), next.extract 1 next.size))
    (#[1], (Array.range logN).map fun i => (1 <<< UInt64.ofNat (i + 1))) |>.1

def columnWeight (roots inverses : Array K) (point : Array E) (query : Nat) : E :=
  (Array.range point.size).foldl (fun (basis, product) k =>
    let factor := eadd one (emul (point.getD k zero)
      (embed (Spec.Field.add 1 (Spec.Field.mul basis (inverses.getD k 0)))))
    (Spec.Field.add (Spec.Field.square basis) (Spec.Field.mul (roots.getD k 0) basis),
     emul product factor))
    ((UInt64.ofNat query), one) |>.2

def inducedWeight (messageLog : Nat) (queries : Array Nat) (weights point : Array E) : E :=
  let roots := subspaceRoots messageLog
  let inverses := roots.map Spec.Field.inv
  (Array.range (min queries.size weights.size)).foldl (fun total i =>
    eadd total (emul (weights.getD i zero) (columnWeight roots inverses point (queries.getD i 0)))) zero

def polyEval (coeffs : Array E) (point : E) : E :=
  coeffs.foldr (fun c acc => eadd (emul acc point) c) zero

structure RoundPoly where
  coeffs : Array E
  deriving Inhabited

def RoundPoly.eval (p : RoundPoly) (x : E) : E := polyEval p.coeffs x

inductive ClaimWeight where
  | ood (point : Array E)
  | induced (messageLog : Nat) (queries : Array Nat) (queryWeights : Array E)

def ClaimWeight.eval (w : ClaimWeight) (point : Array E) : Option E :=
  match w with
  | .ood oodPoint =>
    if decide (oodPoint.size = point.size) then some (StackOpen.eqEval oodPoint point) else none
  | .induced messageLog queries queryWeights =>
    if decide (point.size = messageLog) then some (inducedWeight messageLog queries queryWeights point) else none

structure Glued where
  scalar : E
  foldStart : Nat
  weight : ClaimWeight

def laneDot (row weights : Array E) : E :=
  (Array.range (min row.size weights.size)).foldl (fun acc i =>
    eadd acc (emul (row.getD i zero) (weights.getD i zero))) zero

def baseRowDot (row : Array K) (weights : Array E) : E :=
  (Array.range (min row.size weights.size)).foldl (fun acc i =>
    eadd acc (mulBase (weights.getD i zero) (row.getD (row.size - 1 - i) 0))) zero

def levelLeafWords (level foldCount : Nat) : Nat :=
  if level = 0 then 1 <<< foldCount else 3 * (1 <<< foldCount)

def levelRowWords (level foldCount messageLog : Nat) (placed : Nat) : Nat :=
  if level = 0 then (placed + (1 <<< messageLog) - 1) / (1 <<< messageLog)
  else levelLeafWords level foldCount

def multilinearEvalE (values : Array E) (point : Array E) : E :=
  if decide (values.size = 1 <<< point.size) then
    (Array.range point.size).foldl (fun cur k =>
      let r := point.getD k zero
      let half := cur.size / 2
      (Array.range half).map fun i =>
        let lo := cur.getD (2 * i) zero
        eadd lo (emul r (eadd lo (cur.getD (2 * i + 1) zero))))
      values |>.getD 0 zero
  else zero

def multilinearEval (table : Array K) (point : Array E) : E :=
  multilinearEvalE (table.map embed) point

def terminal (residual : Array E) (folds : Array E) (weight : E) : E :=
  emul weight (multilinearEvalE residual folds)

def shapeOk (logN logInvRate : Nat) : Bool :=
  (deriveConfig logN logInvRate).isSome

def eqKernel (point : Array E) : Array E :=
  point.foldl (fun out r =>
    let high := out.map (fun v => emul v r)
    out.mapIdx (fun i v => eadd v (high.getD i zero)) ++ high) #[one]

def powers (x : E) (n : Nat) : Array E :=
  (Array.range n).foldl (fun (acc, cur) _ => (acc.push cur, emul cur x)) (#[], one) |>.1

def dot (left right : Array E) : E :=
  (Array.range (min left.size right.size)).foldl
    (fun acc i => eadd acc (emul (left.getD i zero) (right.getD i zero))) zero

def addScaled (base : Array E) (scale : E) (extra : Array E) : Array E :=
  (Array.range (min base.size extra.size)).foldl
    (fun acc i => acc.setIfInBounds i (eadd (acc.getD i zero) (emul scale (extra.getD i zero)))) base

def verifierSamples (s : VerifierState) (n : Nat) : Array E × VerifierState :=
  (Array.range n).foldl (fun (acc, s) _ =>
    let (x, s) := Spec.Transcript.verifierSample s
    (acc.push x, s)) (#[], s)

structure LevelState where
  quad : Array E
  folds : Array E
  glued : Array Glued
  root : Spec.Merkle.Digest
  residual : Array E
  state : VerifierState

def verifyLevel (config : Config) (logN placed : Nat) (ls : LevelState) (level : Nat) : Option LevelState := do
  let foldCount := config.folds.getD level 0
  let (quad, levelFolds, folds, s) ← (Array.range foldCount).foldlM
    (fun (quad, levelFolds, folds, s) _ => do
      let (challenge, s) := Spec.Transcript.verifierSample s
      let (quad, s) ← Spec.Transcript.sumcheckRoundPoly s 2 (polyEval quad challenge) none
      some (quad, levelFolds.push challenge, folds.push challenge, s))
    (ls.quad, #[], ls.folds, ls.state)
  let messageLog := logN - folds.size
  let finalLevel := decide (level + 1 = config.folds.size)
  let (residual, nextRoot, pending, s) ←
    if finalLevel then
      let (residual, s) ← Spec.Transcript.nextScalars (1 <<< messageLog) s
      pure (residual, ls.root, (#[] : Array (Array E × ClaimWeight)), s)
    else
      let (halves, s) ← Spec.Transcript.nextScalars 2 s
      let next ← Spec.Merkle.fromHalves (halves.getD 0 zero) (halves.getD 1 zero)
      let (oodPoint, s) := verifierSamples s messageLog
      let (oodValue, s) ← Spec.Transcript.nextScalar s
      let (intro, s) ← Spec.Transcript.sumcheckRoundPoly s 2 oodValue none
      pure (#[], next, #[(intro, ClaimWeight.ood oodPoint)], s)
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
    let (intro, s) ← Spec.Transcript.sumcheckRoundPoly s 2 (dot rowValues queryWeights) none
    let pending := pending.push (intro, ClaimWeight.induced messageLog queries queryWeights)
    let (quad, _, glued) := pending.foldl (fun (quad, scalar, glued) item =>
      let scalar := emul scalar lam
      (addScaled quad scalar item.1, scalar, glued.push ⟨scalar, folds.size, item.2⟩))
      (quad, one, ls.glued)
    some ⟨quad, folds, glued, nextRoot, residual, s⟩

def verifyWhir (s : VerifierState) (logN placed logInvRate : Nat) (target : E)
    (root : Spec.Merkle.Digest) (evaluateBasis : Array E → E) : Option VerifierState := do
  let config ← deriveConfig logN logInvRate
  if config.folds.isEmpty then none else
    let (quad0, s) ← Spec.Transcript.sumcheckRoundPoly s 2 target none
    let done ← (Array.range config.folds.size).foldlM (verifyLevel config logN placed)
      ⟨quad0, #[], #[], root, #[], s⟩
    let messageLog := logN - done.folds.size
    let (_, tail, running, s) ← (Array.range messageLog).foldlM
      (fun (quad, tail, _, s) k => do
        let (challenge, s) := Spec.Transcript.verifierSample s
        let running := polyEval quad challenge
        if k + 1 < messageLog then
          let (quad, s) ← Spec.Transcript.sumcheckRoundPoly s 2 running none
          some (quad, tail.push challenge, running, s)
        else
          some (quad, tail.push challenge, running, s))
      (done.quad, #[], zero, done.state)
    let point := done.folds ++ tail
    let laneFolds := config.folds.getD 0 0
    let reordered := point.extract laneFolds point.size ++ point.extract 0 laneFolds
    let weight ← done.glued.foldlM (fun acc claim => do
      let w ← claim.weight.eval (point.extract claim.foldStart point.size)
      some (eadd acc (emul claim.scalar w))) (evaluateBasis reordered)
    if decide (1 <<< tail.size = done.residual.size) &&
        Spec.Vm.wordBEq (terminal done.residual tail weight) running then
      some s
    else none

def verifyStackedOpening (s : VerifierState) (root : Spec.Merkle.Digest)
    (stackLog placed logInvRate : Nat) (values : Array E)
    (weightsAt : Array E → Array E) : Option VerifierState := do
  let (lam, s) := Spec.Transcript.verifierSample s
  let scales := powers lam values.size
  let target := dot scales values
  verifyWhir s stackLog placed logInvRate target root (fun point => dot scales (weightsAt point))

structure PlacedClaim where
  placement : StackOpen.Placement
  point : Array E
  value : E

def verifyRingSwitchAndStacked (s : VerifierState) (root : Spec.Merkle.Digest)
    (stackLog placed logInvRate : Nat) (qkeccak : StackOpen.Placement)
    (ringPoint slices : Array E) (claims : Array PlacedClaim) : Option VerifierState := do
  let (challenges, s) := verifierSamples s RingSwitch.compositionShifts.size
  let coefficients := RingSwitch.frobeniusCoefficients challenges
  let images := slices.map fun v => RingSwitch.applyComposed v challenges
  let ringTarget := polyEval images ⟨2, 0, 0⟩
  let values := #[ringTarget] ++ claims.map (·.value)
  let weightsAt (x : Array E) : Array E :=
    let rw := emul (StackOpen.eqAbove qkeccak x)
      (RingSwitch.ringWeightAt ringPoint (x.extract 0 qkeccak.variables) coefficients)
    #[rw] ++ claims.map fun c => StackOpen.place c.placement c.point x
  verifyStackedOpening s root stackLog placed logInvRate values weightsAt

def proverSamples (s : ProverState) (n : Nat) : Array E × ProverState :=
  (Array.range n).foldl (fun (acc, s) _ =>
    let (x, s) := Spec.Transcript.sample s
    (acc.push x, s)) (#[], s)

def sendRound (s : ProverState) (claim u0 u2 : E) : Array E × ProverState :=
  let coeffs := #[u0, eadd claim u2, u2]
  (coeffs, Spec.Transcript.addRoundPoly s coeffs false)

def sumcheckMsgEvenOdd (f b : Array E) : E × E :=
  let pairs := min (f.size / 2) (b.size / 2)
  (Array.range pairs).foldl (fun (u0, u2) i =>
    let f0 := f.getD (2 * i) zero
    let f1 := f.getD (2 * i + 1) zero
    let b0 := b.getD (2 * i) zero
    let b1 := b.getD (2 * i + 1) zero
    (eadd u0 (emul f0 b0), eadd u2 (emul (eadd f0 f1) (eadd b0 b1)))) (zero, zero)

def foldEvenOdd (xs : Array E) (r : E) : Array E :=
  (Array.range (xs.size / 2)).map fun i =>
    let lo := xs.getD (2 * i) zero
    eadd lo (emul r (eadd lo (xs.getD (2 * i + 1) zero)))

def sumcheckMsgBlocks (blockLen : Nat) (f b : Array E) : E × E :=
  let nBlocks := (min f.size b.size) / blockLen
  let pairs := (nBlocks + 1) / 2
  (Array.range pairs).foldl (fun (u0, u2) p =>
    let base0 := (2 * p) * blockLen
    let base1 := (2 * p + 1) * blockLen
    if decide (2 * p + 1 < nBlocks) then
      (Array.range blockLen).foldl (fun (u0, u2) k =>
        let f0 := f.getD (base0 + k) zero
        let f1 := f.getD (base1 + k) zero
        let b0 := b.getD (base0 + k) zero
        let b1 := b.getD (base1 + k) zero
        (eadd u0 (emul f0 b0), eadd u2 (emul (eadd f0 f1) (eadd b0 b1)))) (u0, u2)
    else
      let lone := (Array.range blockLen).foldl (fun acc k =>
        eadd acc (emul (f.getD (base0 + k) zero) (b.getD (base0 + k) zero))) zero
      (eadd u0 lone, eadd u2 lone)) (zero, zero)

def foldBlocks (blockLen : Nat) (xs : Array E) (r : E) : Array E :=
  let nBlocks := xs.size / blockLen
  let pairs := (nBlocks + 1) / 2
  let onePlusR := eadd one r
  (Array.range pairs).foldl (fun out p =>
    let base0 := (2 * p) * blockLen
    let base1 := (2 * p + 1) * blockLen
    if decide (2 * p + 1 < nBlocks) then
      (Array.range blockLen).foldl (fun out k =>
        let lo := xs.getD (base0 + k) zero
        out.push (eadd lo (emul r (eadd lo (xs.getD (base1 + k) zero))))) out
    else
      (Array.range blockLen).foldl (fun out k =>
        out.push (emul onePlusR (xs.getD (base0 + k) zero))) out) #[]

def extWords (lanes : Array E) : Array K :=
  lanes.foldl (fun out lane => out ++ #[lane.c0, lane.c1, lane.c2]) #[]

def encodeExt (poly : Array E) (logNumInterleaved logInvRate : Nat) : Array K :=
  let width := 3 * (1 <<< logNumInterleaved)
  let rate := 1 <<< logInvRate
  Spec.Pcs.Ntt.encode (Spec.Pcs.Commit.replicate (extWords poly) rate) width logInvRate

def extRows (codeword : Array K) (width : Nat) : Array (Array K) :=
  (Array.range (codeword.size / width)).map fun pos =>
    codeword.extract (pos * width) ((pos + 1) * width)

def grindFuel : Nat := 1 <<< 22

def grindWhir (s : ProverState) (bits : Nat) : Option ProverState :=
  if bits ≥ 64 then none else
  let found :=
    if bits = 0 then some 0
    else
      Fin.foldl grindFuel (fun acc k =>
        match acc with
        | some _ => acc
        | none =>
          let n := UInt64.ofNat k.val
          if Spec.Transcript.powBitsOk s.sponge ⟨n, 0, 0⟩ bits then some n else none) none
  found.map fun n =>
    { s with sponge := (Spec.Transcript.nonceProbe s.sponge ⟨n, 0, 0⟩).2,
             stream := s.stream.push ⟨n, 0, 0⟩ }

def buildLevels (depth : Nat) (leaves : Array Spec.Merkle.Digest) :
    Array (Array Spec.Merkle.Digest) :=
  ((Array.range depth).foldl (fun (tree, cur) _ =>
    let next := Spec.Merkle.parentLevel cur
    (tree.push next, next)) (#[leaves], leaves)).1

def pruneTree (depth : Nat) (tree : Array (Array Spec.Merkle.Digest)) (indices : List Nat) :
    Array Spec.Merkle.Digest :=
  ((Array.range depth).foldl (fun (acc, active) level =>
    let step := Spec.Merkle.pruneLevel (tree.getD level #[]) active
    (acc ++ step.2, step.1)) (#[], indices)).1

def openRowsFast (rows : Array (Array K)) (queries : Array Nat) (depth leafWords : Nat) :
    Option Spec.Merkle.PrunedMerklePaths := do
  let indices := Spec.Merkle.sortedUnique queries
  if decide (rows.size ≠ 2 ^ depth) || !rows.all (fun row => decide (row.size ≤ leafWords)) ||
      !Spec.Merkle.validIndices depth indices then none else
    let tree := buildLevels depth (rows.map fun row => Spec.Merkle.hashRow row leafWords)
    some ⟨indices.map (fun i => rows.getD i #[]), pruneTree depth tree indices.toList⟩

def commitExt (poly : Array E) (logNumInterleaved logInvRate : Nat) :
    Array (Array K) × ByteArray :=
  let width := 3 * (1 <<< logNumInterleaved)
  let rows := extRows (encodeExt poly logNumInterleaved logInvRate) width
  let leaves := rows.map fun row => Spec.Merkle.hashRow row width
  (rows, Spec.Merkle.digestBytes (Spec.Merkle.treeRoot (buildLevels (rows.size.log2) leaves)))

def eqTable (point : Array E) : Array E :=
  point.foldl (fun out r =>
    let high := out.map (fun v => emul v r)
    out.mapIdx (fun i v => eadd v (high.getD i zero)) ++ high) #[one]

def evalAt (table point : Array E) : E :=
  if decide (table.size = 1 <<< point.size) then
    (Array.range point.size).foldl (fun cur k =>
      foldEvenOdd cur (point.getD k zero)) table |>.getD 0 zero
  else zero

structure PendingClaim where
  basis : Array E
  value : E
  quad : Array E

def introduceOod (f : Array E) (s : ProverState) (nVars : Nat) :
    PendingClaim × ProverState :=
  let (z, s) := proverSamples s nVars
  let basis := eqTable z
  let (u0, u2) := sumcheckMsgEvenOdd f basis
  let value := evalAt f z
  let s := Spec.Transcript.addScalar s value
  let (quad, s) := sendRound s value u0 u2
  (⟨basis, value, quad⟩, s)

def gluePending (basis : Array E) (claim : E) (quad : Array E) (lambda : E)
    (pending : Array PendingClaim) : Array E × E × Array E :=
  let (_, basis, claim, quad) := pending.foldl (fun (scalar, basis, claim, quad) item =>
    let scalar := emul scalar lambda
    (scalar, addScaled basis scalar item.basis, eadd claim (emul scalar item.value),
     addScaled quad scalar item.quad)) (one, basis, claim, quad)
  (basis, claim, quad)

def queryScales (log : Nat) (query : Nat) : Array E :=
  let roots := subspaceRoots log
  let inverses := roots.map Spec.Field.inv
  ((Array.range log).foldl (fun (basis, acc) k =>
    let c := embed (Spec.Field.add 1 (Spec.Field.mul basis (inverses.getD k 0)))
    (Spec.Field.add (Spec.Field.square basis) (Spec.Field.mul (roots.getD k 0) basis),
     acc.push c)) ((UInt64.ofNat query), #[])).2

def booleanScale (poly : Array E) (c : E) : Array E :=
  poly ++ poly.map (fun v => eadd v (emul v c))

def inducedBasis (messageLog : Nat) (queries : Array Nat) (weights : Array E) : Array E :=
  let n := min queries.size weights.size
  (Array.range n).foldl (fun acc i =>
    let poly := (queryScales messageLog (queries.getD i 0)).foldl booleanScale #[one]
    let w := weights.getD i zero
    (Array.range (1 <<< messageLog)).foldl (fun out j =>
      out.push (eadd (acc.getD j zero) (emul w (poly.getD j zero)))) #[]) #[]

def rowDot (row : Array K) (weights : Array E) : E :=
  laneDot (extRow row) weights

def enforcedSum (level : Nat) (rows : Array (Array K)) (queries : Array Nat)
    (laneFolds weights : Array E) : E :=
  let kernel := eqKernel laneFolds
  let values := queries.map fun q =>
    let row := rows.getD q #[]
    if level = 0 then baseRowDot row kernel else rowDot row kernel
  dot values weights

def openRows (rows : Array (Array K)) (queries : Array Nat) (depth leafWords : Nat) :
    Option Spec.Merkle.PrunedMerklePaths :=
  openRowsFast rows queries depth leafWords

def putU64Whir (b : ByteArray) (w : UInt64) : ByteArray := b ++ Spec.Field.encodeBytesK w

def putPhaseBytes (phase : Spec.Merkle.PrunedMerklePaths) : ByteArray :=
  let b := phase.rows.foldl (fun b row =>
    row.foldl putU64Whir (putU64Whir b (UInt64.ofNat row.size)))
    (putU64Whir ByteArray.empty (UInt64.ofNat phase.rows.size))
  phase.siblings.foldl (fun b d =>
    (Array.range 32).foldl (fun b i => b.push (d[i]?.getD 0)) b)
    (putU64Whir b (UInt64.ofNat phase.siblings.size))

def hintPhase (s : ProverState) (phase : Spec.Merkle.PrunedMerklePaths) : ProverState :=
  Spec.Transcript.hintMerkle s (putPhaseBytes phase)

def l0Rows (message : Array K) (lanes logRows logInvRate : Nat) : Array (Array K) :=
  let width := Spec.Pcs.Commit.rowWords lanes
  let code := Spec.Pcs.Commit.encodeMessage message lanes logRows logInvRate
  (Array.range (code.size / width)).map fun pos =>
    (code.extract (pos * width) ((pos + 1) * width)).extract (width - lanes) width

structure ProverFold where
  f : Array E
  basis : Array E
  claim : E
  quad : Array E
  pending : Array PendingClaim
  folds : Array E
  state : ProverState

def stepFold (p : ProverFold) : ProverFold :=
  let (r, s) := Spec.Transcript.sample p.state
  let claim := polyEval p.quad r
  let f := foldEvenOdd p.f r
  let basis := foldEvenOdd p.basis r
  let (u0, u2) := sumcheckMsgEvenOdd f basis
  let (quad, s) := sendRound s claim u0 u2
  ⟨f, basis, claim, quad, p.pending, p.folds.push r, s⟩

def absorbFold (p : ProverFold) : ProverFold :=
  let (r, s) := Spec.Transcript.sample p.state
  ⟨foldEvenOdd p.f r, foldEvenOdd p.basis r, polyEval p.quad r, p.quad, p.pending,
    p.folds.push r, s⟩

def startFold (f basis : Array E) (target : E) (s : ProverState) : ProverFold :=
  let (u0, u2) := sumcheckMsgEvenOdd f basis
  let (quad, s) := sendRound s target u0 u2
  ⟨f, basis, target, quad, #[], #[], s⟩

def foldTimes (p : ProverFold) (n : Nat) : ProverFold :=
  (Array.range n).foldl (fun p _ => stepFold p) p

def stepLaneFold (laneBlock : Nat) (last : Bool) (p : ProverFold) : ProverFold :=
  let (r, s) := Spec.Transcript.sample p.state
  let claim := polyEval p.quad r
  let f := foldBlocks laneBlock p.f r
  let basis := foldBlocks laneBlock p.basis r
  let (u0, u2) :=
    if last then sumcheckMsgEvenOdd f basis else sumcheckMsgBlocks laneBlock f basis
  let (quad, s) := sendRound s claim u0 u2
  ⟨f, basis, claim, quad, p.pending, p.folds.push r, s⟩

def startLaneFold (laneBlock : Nat) (f basis : Array E) (target : E) (s : ProverState) :
    ProverFold :=
  let (u0, u2) := sumcheckMsgBlocks laneBlock f basis
  let (quad, s) := sendRound s target u0 u2
  ⟨f, basis, target, quad, #[], #[], s⟩

def proveLevel (config : Config) (logN : Nat) (p : ProverFold) (level : Nat)
    (rows : Array (Array K)) : Option (ProverFold × Array (Array K)) := do
  let foldCount := config.folds.getD level 0
  let laneBlock := 1 <<< (logN - config.folds.getD 0 0)
  let p :=
    if level = 0 then
      (Array.range foldCount).foldl
        (fun p j => stepLaneFold laneBlock (decide (j + 1 = foldCount)) p) p
    else
      foldTimes p foldCount
  let messageLog := logN - p.folds.size
  let finalLevel := decide (level + 1 = config.folds.size)
  let (p, nextRows) ←
    if finalLevel then
      let s := Spec.Transcript.addScalars p.state p.f
      pure ((⟨p.f, p.basis, p.claim, p.quad, p.pending, p.folds, s⟩ : ProverFold), rows)
    else
      let (nextRows, root) := commitExt p.f (config.folds.getD (level + 1) 0)
        (config.logInvRates.getD (level + 1) 0)
      let s := Spec.Transcript.addRoot p.state root
      let (ood, s) := introduceOod p.f s messageLog
      pure ((⟨p.f, p.basis, p.claim, p.quad, p.pending.push ood, p.folds, s⟩ : ProverFold), nextRows)
  let s ← grindWhir p.state queryGrindingBits
  let rate := config.logInvRates.getD level 0
  let blockLog := messageLog + rate
  let count := config.queries.getD level 0
  let perWord := 192 / blockLog
  if perWord = 0 then none else
    let (drawn, s) := proverSamples s ((count + perWord - 1) / perWord)
    let queries := sampleQueries count blockLog drawn
    let (lam, s) := Spec.Transcript.sample s
    let weights := powers lam queries.size
    let phase ← openRows rows queries blockLog (levelLeafWords level foldCount)
    let s := hintPhase s phase
    let laneFolds := p.folds.extract (p.folds.size - foldCount) p.folds.size
    let enforced := enforcedSum level rows queries laneFolds weights
    let basisI := inducedBasis messageLog queries weights
    let (u0, u2) := sumcheckMsgEvenOdd p.f basisI
    let (quadI, s) := sendRound s enforced u0 u2
    let (basis, claim, quad) := gluePending p.basis p.claim p.quad lam
      (p.pending.push ⟨basisI, enforced, quadI⟩)
    some (⟨p.f, basis, claim, quad, #[], p.folds, s⟩, nextRows)

def proveWhir (s : ProverState) (logN logInvRate : Nat) (witness : Array K)
    (weight : Array E) (target : E) : Option ProverState := do
  let config ← deriveConfig logN logInvRate
  if config.folds.isEmpty then none else
    let k0 := config.folds.getD 0 0
    let laneBlock := 1 <<< (logN - k0)
    if decide (witness.size = 0 ∨ witness.size % laneBlock ≠ 0) then none else
      let lanes := witness.size / laneBlock
      let rows0 := l0Rows witness lanes (logN - k0) (config.logInvRates.getD 0 0)
      let p0 := startLaneFold laneBlock (witness.map embed) (weight.extract 0 witness.size) target s
      let (done, _) ← (Array.range config.folds.size).foldlM
        (fun (p, rows) level => proveLevel config logN p level rows) (p0, rows0)
      let resLog := logN - done.folds.size
      let done := (Array.range resLog).foldl (fun p j =>
        if decide (j + 1 < resLog) then stepFold p else absorbFold p) done
      some done.state

def proveStackedOpening (s : ProverState) (stackLog logInvRate : Nat)
    (witness : Array K) (values : Array E) (basisTables : Array (Array E)) :
    Option ProverState := do
  if decide (values.size ≠ basisTables.size) then none else
    let (lam, s) := Spec.Transcript.sample s
    let scales := powers lam values.size
    let target := dot scales values
    let combined := (Array.range values.size).foldl (fun acc i =>
      addScaled acc (scales.getD i zero) (basisTables.getD i #[]))
      (Array.replicate witness.size zero)
    proveWhir s stackLog logInvRate witness combined target

def applyLinearMap (weights : Array E) (v : E) : E :=
  let s0 := (Array.range 64).foldl (fun acc b =>
    if v.c0.toNat.testBit b then eadd acc (weights.getD b zero) else acc) zero
  let s1 := (Array.range 64).foldl (fun acc b =>
    if v.c1.toNat.testBit b then eadd acc (weights.getD (64 + b) zero) else acc) s0
  (Array.range 64).foldl (fun acc b =>
    if v.c2.toNat.testBit b then eadd acc (weights.getD (128 + b) zero) else acc) s1

def stackedWeight (n : Nat) (lambda : E) (points : Array StackOpen.StackClaim)
    (ring : StackOpen.RingSwitchOpen) (ringWeights : Array (Array E)) : Array E :=
  let scales := powers lambda (ring.claims.size + points.size)
  let base := Array.replicate n zero
  let placed := (Array.range points.size).foldl (fun acc i =>
    match points[i]? with
    | none => acc
    | some (.point offset low _) =>
      let w := scales.getD (ring.claims.size + i) zero
      let eq := eqKernel low
      (Array.range eq.size).foldl (fun acc j =>
        let idx := offset + j
        acc.setIfInBounds idx (eadd (acc.getD idx zero) (emul w (eq.getD j zero)))) acc) base
  (Array.range ring.claims.size).foldl (fun acc i =>
    let claim := ring.claims.getD i default
    let weights := ringWeights.getD i #[]
    let eq := eqKernel claim.suffixPoint
    (Array.range eq.size).foldl (fun acc j =>
      let idx := ring.offset + j
      let word := applyLinearMap weights (eq.getD j zero)
      acc.setIfInBounds idx (eadd (acc.getD idx zero) word)) acc) placed

def provePcsOpen (s : ProverState) (stackLog logInvRate : Nat) (witness : Array K)
    (points : Array StackOpen.StackClaim) (ring : StackOpen.RingSwitchOpen) :
    Option ProverState := do
  let maps := (Array.range 6).foldl (fun acc _ =>
    let (c, s) := Spec.Transcript.sample acc.2
    (acc.1.push c, s)) (#[], s)
  let (lam, s) := Spec.Transcript.sample maps.2
  let coordWeights := RingSwitch.coordinateWeights maps.1
  let rsScales := powers lam ring.claims.size
  let ringWeights := (Array.range ring.claims.size).map fun i =>
    coordWeights.map (emul (rsScales.getD i zero))
  let values := (Array.range ring.claims.size).map (fun i =>
    let claim := ring.claims.getD i default
    let cols := RingSwitch.transposeSlices claim.slices
    (Array.range (min cols.size coordWeights.size)).foldl (fun acc j =>
      eadd acc (mulBase (coordWeights.getD j zero) (cols.getD j 0))) zero)
    ++ points.map StackOpen.StackClaim.value
  let target := dot (powers lam values.size) values
  let weight := stackedWeight witness.size lam points ring ringWeights
  proveWhir s stackLog logInvRate witness weight target

end LeanVmXmss.Spec.Pcs.Whir
