import Model.Pcs.Whir
import Proofs.Pcs.StackOpen
import Proofs.Pcs.Refinement
import Proofs.Layout.Basic
import Proofs.Keccak.Registers
import Proofs.Transcript.Registers

namespace LeanVmXmss.Proofs.Pcs.Whir

open Spec.Field (K E)

private theorem nativeMul_eq_mul :
    Model.Field.nativeMul = Spec.Field.mul := by
  funext a b
  exact Proofs.Pcs.nativeMul_eq_spec a b

private theorem nativeInv_eq_inv :
    Model.Field.nativeInv = Spec.Field.inv := by
  funext a
  exact Proofs.Pcs.nativeInv_eq_spec a

theorem queriesAt_refines :
    Model.Pcs.Whir.queriesAt = Spec.Pcs.Whir.queriesAt := rfl

theorem deriveConfig_refines :
    Model.Pcs.Whir.deriveConfig = Spec.Pcs.Whir.deriveConfig := rfl

theorem sampleWindow_refines :
    Model.Pcs.Whir.sampleWindow = Spec.Pcs.Whir.sampleWindow := rfl

theorem sampleQueries_refines :
    Model.Pcs.Whir.sampleQueries = Spec.Pcs.Whir.sampleQueries := rfl

theorem subspaceRoots_refines :
    Model.Pcs.Whir.subspaceRoots = Spec.Pcs.Whir.subspaceRoots := rfl

theorem columnWeight_refines (roots inverses : Array K) (point : Array E) (query : Nat) :
    Model.Pcs.Whir.columnWeight roots inverses point query =
      Spec.Pcs.Whir.columnWeight roots inverses point query := by
  simp only [Model.Pcs.Whir.columnWeight, Spec.Pcs.Whir.columnWeight,
    Spec.Field.square, nativeMul_eq_mul, RingSwitch.nativeKaratsuba_eq_emul]

theorem columnWeight_eq_spec :
    Model.Pcs.Whir.columnWeight = Spec.Pcs.Whir.columnWeight := by
  funext roots inverses point query
  exact columnWeight_refines roots inverses point query

theorem inducedWeight_refines (messageLog : Nat) (queries : Array Nat) (weights point : Array E) :
    Model.Pcs.Whir.inducedWeight messageLog queries weights point =
      Spec.Pcs.Whir.inducedWeight messageLog queries weights point := by
  have hstep : Model.Pcs.Whir.subspaceStepFast = Spec.Pcs.Whir.subspaceStep := by
    funext root layer
    simp only [Model.Pcs.Whir.subspaceStepFast, Spec.Pcs.Whir.subspaceStep, Spec.Field.square,
      nativeMul_eq_mul]
  have hroots : Model.Pcs.Whir.subspaceRootsFast messageLog =
      Spec.Pcs.Whir.subspaceRoots messageLog := by
    simp only [Model.Pcs.Whir.subspaceRootsFast, Spec.Pcs.Whir.subspaceRoots, hstep]
  simp only [Model.Pcs.Whir.inducedWeight, Spec.Pcs.Whir.inducedWeight, hroots,
    nativeInv_eq_inv, columnWeight_eq_spec, RingSwitch.nativeKaratsuba_eq_emul]

theorem polyEval_refines (coeffs : Array E) (point : E) :
    Model.Pcs.Whir.polyEval coeffs point = Spec.Pcs.Whir.polyEval coeffs point := by
  simp only [Model.Pcs.Whir.polyEval, Spec.Pcs.Whir.polyEval, RingSwitch.nativeKaratsuba_eq_emul]

theorem multilinearEval_refines (table : Array K) (point : Array E) :
    Model.Pcs.Whir.multilinearEval table point = Spec.Pcs.Whir.multilinearEval table point := by
  simp only [Model.Pcs.Whir.multilinearEval, Spec.Pcs.Whir.multilinearEval,
    RingSwitch.nativeKaratsuba_eq_emul]

theorem terminal_refines (residual : Array K) (folds : Array E) (weight : E) :
    Model.Pcs.Whir.terminal residual folds weight =
      Spec.Pcs.Whir.terminal residual folds weight := by
  simp only [Model.Pcs.Whir.terminal, Spec.Pcs.Whir.terminal, multilinearEval_refines,
    RingSwitch.nativeKaratsuba_eq_emul]

theorem baseRowDot_refines (row : Array K) (weights : Array E) :
    Model.Pcs.Whir.baseRowDot row weights = Spec.Pcs.Whir.baseRowDot row weights := by
  simp only [Model.Pcs.Whir.baseRowDot, Spec.Pcs.Whir.baseRowDot,
    RingSwitch.nativeMulBase_eq_mulBase]

theorem laneDot_refines (row weights : Array E) :
    Model.Pcs.Whir.laneDot row weights = Spec.Pcs.Whir.laneDot row weights := by
  simp only [Model.Pcs.Whir.laneDot, Spec.Pcs.Whir.laneDot, RingSwitch.nativeKaratsuba_eq_emul]

theorem eqKernel_refines (point : Array E) :
    Model.Pcs.Whir.eqKernel point = Spec.Pcs.Whir.eqKernel point := by
  simp only [Model.Pcs.Whir.eqKernel, Spec.Pcs.Whir.eqKernel, RingSwitch.nativeKaratsuba_eq_emul]

theorem powers_refines (x : E) (n : Nat) :
    Model.Pcs.Whir.powers x n = Spec.Pcs.Whir.powers x n := by
  simp only [Model.Pcs.Whir.powers, Spec.Pcs.Whir.powers, RingSwitch.nativeKaratsuba_eq_emul]

theorem dot_refines (left right : Array E) :
    Model.Pcs.Whir.dot left right = Spec.Pcs.Whir.dot left right := by
  simp only [Model.Pcs.Whir.dot, Spec.Pcs.Whir.dot, RingSwitch.nativeKaratsuba_eq_emul]

theorem claimWeight_eval_refines (w : Spec.Pcs.Whir.ClaimWeight) (point : Array E) :
    Model.Pcs.Whir.ClaimWeight.eval w point = Spec.Pcs.Whir.ClaimWeight.eval w point := by
  cases w with
  | ood oodPoint =>
    simp only [Model.Pcs.Whir.ClaimWeight.eval, Spec.Pcs.Whir.ClaimWeight.eval,
      StackOpen.eqEval_eq_spec]
  | induced messageLog queries queryWeights =>
    simp only [Model.Pcs.Whir.ClaimWeight.eval, Spec.Pcs.Whir.ClaimWeight.eval, inducedWeight_refines]

theorem shapeOk_of_derive (logN logInvRate : Nat) :
    Spec.Pcs.Whir.shapeOk logN logInvRate = (Spec.Pcs.Whir.deriveConfig logN logInvRate).isSome := rfl

theorem polyEval_eq_spec :
    Model.Pcs.Whir.polyEval = Spec.Pcs.Whir.polyEval := by
  funext coeffs point
  exact polyEval_refines coeffs point

theorem terminal_eq_spec :
    Model.Pcs.Whir.terminal = Spec.Pcs.Whir.terminal := by
  funext residual folds weight
  exact terminal_refines residual folds weight

theorem baseRowDot_eq_spec :
    Model.Pcs.Whir.baseRowDot = Spec.Pcs.Whir.baseRowDot := by
  funext row weights
  exact baseRowDot_refines row weights

theorem laneDot_eq_spec :
    Model.Pcs.Whir.laneDot = Spec.Pcs.Whir.laneDot := by
  funext row weights
  exact laneDot_refines row weights

theorem eqKernel_eq_spec :
    Model.Pcs.Whir.eqKernel = Spec.Pcs.Whir.eqKernel := by
  funext point
  exact eqKernel_refines point

theorem powers_eq_spec :
    Model.Pcs.Whir.powers = Spec.Pcs.Whir.powers := by
  funext x n
  exact powers_refines x n

theorem dot_eq_spec :
    Model.Pcs.Whir.dot = Spec.Pcs.Whir.dot := by
  funext left right
  exact dot_refines left right

theorem claimWeight_eval_eq_spec :
    Model.Pcs.Whir.ClaimWeight.eval = Spec.Pcs.Whir.ClaimWeight.eval := by
  funext w point
  exact claimWeight_eval_refines w point

theorem addScaled_refines (base : Array E) (scale : E) (extra : Array E) :
    Model.Pcs.Whir.addScaled base scale extra = Spec.Pcs.Whir.addScaled base scale extra := by
  simp only [Model.Pcs.Whir.addScaled, Spec.Pcs.Whir.addScaled, RingSwitch.nativeKaratsuba_eq_emul]

theorem addScaled_eq_spec :
    Model.Pcs.Whir.addScaled = Spec.Pcs.Whir.addScaled := by
  funext base scale extra
  exact addScaled_refines base scale extra

theorem verifierSamples_refines (s : Spec.Transcript.VerifierState) (n : Nat) :
    Model.Pcs.Whir.verifierSamples s n = Spec.Pcs.Whir.verifierSamples s n := rfl

theorem verifyLevel_refines (config : Spec.Pcs.Whir.Config) (logN placed : Nat)
    (ls : Spec.Pcs.Whir.LevelState) (level : Nat) :
    Model.Pcs.Whir.verifyLevel config logN placed ls level =
      Spec.Pcs.Whir.verifyLevel config logN placed ls level := by
  dsimp only [Model.Pcs.Whir.verifyLevel, Spec.Pcs.Whir.verifyLevel,
    Model.Pcs.Whir.queryGrindingBits, Model.Pcs.Whir.levelRowWords,
    Model.Pcs.Whir.levelLeafWords, Model.Pcs.Whir.extRow,
    Model.Pcs.Whir.verifierSamples, Spec.Pcs.Whir.verifierSamples,
    Model.Pcs.Whir.sampleQueries]
  rw [polyEval_eq_spec, powers_eq_spec, eqKernel_eq_spec, baseRowDot_eq_spec,
    laneDot_eq_spec, dot_eq_spec, RingSwitch.nativeKaratsuba_eq_emul, addScaled_eq_spec]

theorem verifyLevel_eq_spec :
    Model.Pcs.Whir.verifyLevel = Spec.Pcs.Whir.verifyLevel := by
  funext config logN placed ls level
  exact verifyLevel_refines config logN placed ls level

theorem verifyWhir_refines (s : Spec.Transcript.VerifierState) (logN placed logInvRate : Nat)
    (target : E) (root : Spec.Merkle.Digest) (evaluateBasis : Array E → E) :
    Model.Pcs.Whir.verifyWhir s logN placed logInvRate target root evaluateBasis =
      Spec.Pcs.Whir.verifyWhir s logN placed logInvRate target root evaluateBasis := by
  dsimp only [Model.Pcs.Whir.verifyWhir, Spec.Pcs.Whir.verifyWhir, Model.Pcs.Whir.deriveConfig]
  rw [verifyLevel_eq_spec, polyEval_eq_spec, claimWeight_eval_eq_spec,
    RingSwitch.nativeKaratsuba_eq_emul, terminal_eq_spec]

theorem verifyWhir_eq_spec :
    Model.Pcs.Whir.verifyWhir = Spec.Pcs.Whir.verifyWhir := by
  funext s logN placed logInvRate target root evaluateBasis
  exact verifyWhir_refines s logN placed logInvRate target root evaluateBasis

theorem verifyStackedOpening_refines (s : Spec.Transcript.VerifierState) (root : Spec.Merkle.Digest)
    (stackLog placed logInvRate : Nat) (values : Array E) (weightsAt : Array E → Array E) :
    Model.Pcs.Whir.verifyStackedOpening s root stackLog placed logInvRate values weightsAt =
      Spec.Pcs.Whir.verifyStackedOpening s root stackLog placed logInvRate values weightsAt := by
  dsimp only [Model.Pcs.Whir.verifyStackedOpening, Spec.Pcs.Whir.verifyStackedOpening]
  rw [powers_eq_spec, dot_eq_spec, verifyWhir_eq_spec]

theorem verifyStackedOpening_eq_spec :
    Model.Pcs.Whir.verifyStackedOpening = Spec.Pcs.Whir.verifyStackedOpening := by
  funext s root stackLog placed logInvRate values weightsAt
  exact verifyStackedOpening_refines s root stackLog placed logInvRate values weightsAt

private theorem stackOpen_eqAbove_eq_spec :
    Model.Pcs.StackOpen.eqAbove = Spec.Pcs.StackOpen.eqAbove := by
  funext p full
  exact StackOpen.eqAbove_refines p full

private theorem stackOpen_place_eq_spec :
    Model.Pcs.StackOpen.place = Spec.Pcs.StackOpen.place := by
  funext p low full
  exact StackOpen.place_refines p low full

private theorem ringSwitch_frobeniusCoefficients_eq_spec :
    Model.Pcs.RingSwitch.frobeniusCoefficients = Spec.Pcs.RingSwitch.frobeniusCoefficients := by
  funext challenges
  exact RingSwitch.frobeniusCoefficients_refines challenges

theorem verifyRingSwitchAndStacked_refines (s : Spec.Transcript.VerifierState)
    (root : Spec.Merkle.Digest) (stackLog placed logInvRate : Nat)
    (qkeccak : Spec.Pcs.StackOpen.Placement) (ringPoint slices : Array E)
    (claims : Array Spec.Pcs.Whir.PlacedClaim) :
    Model.Pcs.Whir.verifyRingSwitchAndStacked s root stackLog placed logInvRate qkeccak ringPoint slices claims =
      Spec.Pcs.Whir.verifyRingSwitchAndStacked s root stackLog placed logInvRate qkeccak ringPoint slices claims := by
  dsimp only [Model.Pcs.Whir.verifyRingSwitchAndStacked, Spec.Pcs.Whir.verifyRingSwitchAndStacked,
    Model.Pcs.Whir.verifierSamples, Spec.Pcs.Whir.verifierSamples,
    Model.Pcs.RingSwitch.compositionShifts]
  rw [ringSwitch_frobeniusCoefficients_eq_spec, RingSwitch.applyComposed_eq_spec,
    polyEval_eq_spec, RingSwitch.nativeKaratsuba_eq_emul, stackOpen_eqAbove_eq_spec,
    RingSwitch.ringWeightAt_eq_spec, stackOpen_place_eq_spec, verifyStackedOpening_eq_spec]

private theorem subspaceStepFast_eq :
    Model.Pcs.Whir.subspaceStepFast = Spec.Pcs.Whir.subspaceStep := by
  funext root layer
  simp only [Model.Pcs.Whir.subspaceStepFast, Spec.Pcs.Whir.subspaceStep, Spec.Field.square,
    nativeMul_eq_mul]

private theorem subspaceRootsFast_eq :
    Model.Pcs.Whir.subspaceRootsFast = Spec.Pcs.Whir.subspaceRoots := by
  funext logN
  simp only [Model.Pcs.Whir.subspaceRootsFast, Spec.Pcs.Whir.subspaceRoots, subspaceStepFast_eq]

private theorem queryScalesFast_eq :
    Model.Pcs.Whir.queryScalesFast = Spec.Pcs.Whir.queryScales := by
  funext log query
  simp only [Model.Pcs.Whir.queryScalesFast, Spec.Pcs.Whir.queryScales, subspaceRootsFast_eq,
    nativeInv_eq_inv, Spec.Field.square, nativeMul_eq_mul]

private theorem booleanScale_eq :
    Model.Pcs.Whir.booleanScale = Spec.Pcs.Whir.booleanScale := by
  funext poly c
  simp only [Model.Pcs.Whir.booleanScale, Spec.Pcs.Whir.booleanScale,
    RingSwitch.nativeKaratsuba_eq_emul]

private theorem inducedBasis_eq :
    Model.Pcs.Whir.inducedBasis = Spec.Pcs.Whir.inducedBasis := by
  funext messageLog queries weights
  simp only [Model.Pcs.Whir.inducedBasis, Spec.Pcs.Whir.inducedBasis, queryScalesFast_eq,
    booleanScale_eq, RingSwitch.nativeKaratsuba_eq_emul]

private theorem sumcheckMsgEvenOdd_eq :
    Model.Pcs.Whir.sumcheckMsgEvenOdd = Spec.Pcs.Whir.sumcheckMsgEvenOdd := by
  funext f b
  simp only [Model.Pcs.Whir.sumcheckMsgEvenOdd, Spec.Pcs.Whir.sumcheckMsgEvenOdd,
    RingSwitch.nativeKaratsuba_eq_emul]

private theorem sumcheckMsgBlocks_eq :
    Model.Pcs.Whir.sumcheckMsgBlocks = Spec.Pcs.Whir.sumcheckMsgBlocks := by
  funext blockLen f b
  simp only [Model.Pcs.Whir.sumcheckMsgBlocks, Spec.Pcs.Whir.sumcheckMsgBlocks,
    RingSwitch.nativeKaratsuba_eq_emul]

private theorem foldEvenOdd_eq :
    Model.Pcs.Whir.foldEvenOdd = Spec.Pcs.Whir.foldEvenOdd := by
  funext xs r
  simp only [Model.Pcs.Whir.foldEvenOdd, Spec.Pcs.Whir.foldEvenOdd, RingSwitch.nativeKaratsuba_eq_emul]

private theorem foldBlocks_eq :
    Model.Pcs.Whir.foldBlocks = Spec.Pcs.Whir.foldBlocks := by
  funext blockLen xs r
  simp only [Model.Pcs.Whir.foldBlocks, Spec.Pcs.Whir.foldBlocks, RingSwitch.nativeKaratsuba_eq_emul]

private theorem eqTable_eq :
    Model.Pcs.Whir.eqTable = Spec.Pcs.Whir.eqTable := by
  funext point
  simp only [Model.Pcs.Whir.eqTable, Spec.Pcs.Whir.eqTable, RingSwitch.nativeKaratsuba_eq_emul]

private theorem evalAt_eq :
    Model.Pcs.Whir.evalAt = Spec.Pcs.Whir.evalAt := by
  funext table point
  simp only [Model.Pcs.Whir.evalAt, Spec.Pcs.Whir.evalAt, foldEvenOdd_eq]

private theorem introduceOod_eq :
    Model.Pcs.Whir.introduceOod = Spec.Pcs.Whir.introduceOod := by
  funext f s nVars
  simp only [Model.Pcs.Whir.introduceOod, Spec.Pcs.Whir.introduceOod, eqTable_eq,
    sumcheckMsgEvenOdd_eq, evalAt_eq]

private theorem gluePending_eq :
    Model.Pcs.Whir.gluePending = Spec.Pcs.Whir.gluePending := by
  funext basis claim quad lambda pending
  simp only [Model.Pcs.Whir.gluePending, Spec.Pcs.Whir.gluePending,
    RingSwitch.nativeKaratsuba_eq_emul, addScaled_eq_spec]

private theorem rowDot_eq :
    Model.Pcs.Whir.rowDot = Spec.Pcs.Whir.rowDot := by
  funext row weights
  simp only [Model.Pcs.Whir.rowDot, Spec.Pcs.Whir.rowDot, laneDot_eq_spec, Model.Pcs.Whir.extRow]

private theorem enforcedSum_eq :
    Model.Pcs.Whir.enforcedSum = Spec.Pcs.Whir.enforcedSum := by
  funext level rows queries laneFolds weights
  simp only [Model.Pcs.Whir.enforcedSum, Spec.Pcs.Whir.enforcedSum, eqKernel_eq_spec,
    baseRowDot_eq_spec, rowDot_eq, dot_eq_spec]

private theorem stepFold_eq :
    Model.Pcs.Whir.stepFold = Spec.Pcs.Whir.stepFold := by
  funext p
  simp only [Model.Pcs.Whir.stepFold, Spec.Pcs.Whir.stepFold, polyEval_eq_spec, foldEvenOdd_eq,
    sumcheckMsgEvenOdd_eq]

private theorem absorbFold_eq :
    Model.Pcs.Whir.absorbFold = Spec.Pcs.Whir.absorbFold := by
  funext p
  simp only [Model.Pcs.Whir.absorbFold, Spec.Pcs.Whir.absorbFold, foldEvenOdd_eq, polyEval_eq_spec]

private theorem stepLaneFold_eq :
    Model.Pcs.Whir.stepLaneFold = Spec.Pcs.Whir.stepLaneFold := by
  funext laneBlock last p
  simp only [Model.Pcs.Whir.stepLaneFold, Spec.Pcs.Whir.stepLaneFold, polyEval_eq_spec,
    foldBlocks_eq, sumcheckMsgEvenOdd_eq, sumcheckMsgBlocks_eq]

private theorem startLaneFold_eq :
    Model.Pcs.Whir.startLaneFold = Spec.Pcs.Whir.startLaneFold := by
  funext laneBlock f basis target s
  simp only [Model.Pcs.Whir.startLaneFold, Spec.Pcs.Whir.startLaneFold, sumcheckMsgBlocks_eq]

private theorem foldTimes_eq :
    Model.Pcs.Whir.foldTimes = Spec.Pcs.Whir.foldTimes := by
  funext p n
  simp only [Model.Pcs.Whir.foldTimes, Spec.Pcs.Whir.foldTimes, stepFold_eq]

private theorem foldLanes_eq (laneBlock foldCount : Nat) (p : Spec.Pcs.Whir.ProverFold) :
    Model.Pcs.Whir.foldLanes laneBlock foldCount p =
      (Array.range foldCount).foldl
        (fun p j => Spec.Pcs.Whir.stepLaneFold laneBlock (decide (j + 1 = foldCount)) p) p := by
  simp only [Model.Pcs.Whir.foldLanes, stepLaneFold_eq]

private theorem encodeExt_eq :
    Model.Pcs.Whir.encodeExt = Spec.Pcs.Whir.encodeExt := by
  funext poly logNumInterleaved logInvRate
  simp only [Model.Pcs.Whir.encodeExt, Spec.Pcs.Whir.encodeExt, Proofs.Pcs.encode_refines]

private theorem hashRowFast_eq (row : Array K) (leafWords : Nat) :
    Model.Pcs.Whir.hashRowFast row leafWords = Spec.Merkle.hashRow row leafWords := by
  simp only [Model.Pcs.Whir.hashRowFast, Spec.Merkle.hashRow, Spec.Merkle.hashLeaf,
    Proofs.Layout.keccak256Fast_refines_spec]

private theorem compressFast_eq :
    Model.Pcs.Whir.compressFast = Spec.Merkle.compress := by
  funext left right
  simp only [Model.Pcs.Whir.compressFast, Spec.Merkle.compress, Spec.Merkle.hashLeaf,
    Proofs.Layout.keccak256Fast_refines_spec]

private theorem cond_pos {α : Type} {c : Prop} [Decidable c] (h : c) (t e : α) :
    (if c then t else e) = t := by
  cases ‹Decidable c› with
  | isTrue _ => rfl
  | isFalse hn => exact absurd h hn

private theorem cond_neg {α : Type} {c : Prop} [Decidable c] (h : ¬ c) (t e : α) :
    (if c then t else e) = e := by
  cases ‹Decidable c› with
  | isTrue hp => exact absurd hp h
  | isFalse _ => rfl

private theorem digest_getD_eq_getElem_bang (nodes : Array Spec.Merkle.Digest) (k : Nat) :
    nodes.getD k default = nodes[k]! :=
  Decidable.byCases
    (fun h : k < nodes.size => by
      simp only [Array.getD, h, dite_true]
      exact (getElem!_pos nodes k h).symm)
    (fun h : ¬ k < nodes.size => by
      simp only [Array.getD, h, dite_false]
      exact (getElem!_neg nodes k h).symm)

private theorem parentLevelFast_eq :
    Model.Pcs.Whir.parentLevelFast = Spec.Merkle.parentLevel := by
  funext nodes
  simp only [Model.Pcs.Whir.parentLevelFast, Spec.Merkle.parentLevel, compressFast_eq,
    digest_getD_eq_getElem_bang]

private theorem buildLevelsFast_eq :
    Model.Pcs.Whir.buildLevelsFast = Spec.Pcs.Whir.buildLevels := by
  funext depth leaves
  simp only [Model.Pcs.Whir.buildLevelsFast, Spec.Pcs.Whir.buildLevels, parentLevelFast_eq]

private theorem openRowsModel_eq :
    Model.Pcs.Whir.openRowsModel = Spec.Pcs.Whir.openRowsFast := by
  funext rows queries depth leafWords
  simp only [Model.Pcs.Whir.openRowsModel, Spec.Pcs.Whir.openRowsFast, buildLevelsFast_eq,
    hashRowFast_eq]

private theorem commitExt_eq :
    Model.Pcs.Whir.commitExt = Spec.Pcs.Whir.commitExt := by
  funext poly logNumInterleaved logInvRate
  simp only [Model.Pcs.Whir.commitExt, Spec.Pcs.Whir.commitExt, encodeExt_eq, buildLevelsFast_eq,
    hashRowFast_eq]

private theorem l0Rows_eq :
    Model.Pcs.Whir.l0Rows = Spec.Pcs.Whir.l0Rows := by
  funext message lanes logRows logInvRate
  simp only [Model.Pcs.Whir.l0Rows, Spec.Pcs.Whir.l0Rows, Model.Pcs.Commit.encodeMessage,
    Spec.Pcs.Commit.encodeMessage, Model.Pcs.Commit.replicate, Model.Pcs.Commit.transpose,
    Model.Pcs.Commit.rowWords, Proofs.Pcs.encode_refines]

private theorem state25Of_toSpec (a : Array UInt64) (h : a.size = 25) :
    (Model.Pcs.Whir.state25Of a).toSpec = a := by
  apply Array.ext
  · simp [Model.Pcs.Whir.state25Of, Model.Keccak.State25.toSpec, h]
  · intro i hi hj
    have bound : i < 25 := by simpa [Model.Pcs.Whir.state25Of, Model.Keccak.State25.toSpec] using hi
    have choices : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
        i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨
        i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 := by omega
    rcases choices with c | c | c | c | c | c | c | c | c | c | c | c |
        c | c | c | c | c | c | c | c | c | c | c | c | c <;>
      subst i <;> simp [Model.Pcs.Whir.state25Of, Model.Keccak.State25.toSpec, Array.getD, hj]

private def grindS0 (sp : Spec.Transcript.Sponge) : Spec.Transcript.Sponge :=
  if sp.pending == 4 then (Spec.Transcript.duplex sp).2 else sp

private theorem grindFast_s0 (sp : Spec.Transcript.Sponge) (hsz : sp.state.size = 25) :
    (if sp.pending == 4 then
      let out := Model.Keccak.keccakF1600 (Model.Pcs.Whir.state25Of sp.state)
      (⟨(Model.Keccak.State25.mk 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
        out.a16 out.a17 out.a18 out.a19 out.a20 out.a21 out.a22 out.a23 out.a24).toSpec, 0⟩ :
        Spec.Transcript.Sponge)
    else sp) = grindS0 sp := by
  unfold grindS0
  refine Decidable.byCases (p := sp.pending = 4) (fun h4 => ?_) (fun h4 => ?_)
  · have hperm := Proofs.Keccak.registers_permutation_refines_spec
      (Model.Pcs.Whir.state25Of sp.state)
    rw [Proofs.Keccak.spec_rounds_eq_permute] at hperm
    rw [state25Of_toSpec sp.state hsz] at hperm
    rw [show (sp.pending == 4) = true from beq_iff_eq.mpr h4, cond_pos rfl, cond_pos rfl,
      Spec.Transcript.duplex, ← hperm]
    apply Proofs.Transcript.Registers.sponge_ext
    · generalize Model.Keccak.keccakF1600 (Model.Pcs.Whir.state25Of sp.state) = out
      apply Array.ext
      · simp [Model.Keccak.State25.toSpec, -Array.getElem_range, Proofs.Keccak.range_twenty_five]
      · intro i hi hj
        have bound : i < 25 := by simpa [Model.Keccak.State25.toSpec] using hi
        have choices : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
            i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨
            i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 := by omega
        rcases choices with c | c | c | c | c | c | c | c | c | c | c | c |
            c | c | c | c | c | c | c | c | c | c | c | c | c <;>
          subst i <;> simp [Model.Keccak.State25.toSpec, -Array.getElem_range,
            Proofs.Keccak.range_twenty_five]
    · rfl
  · rw [beq_false_of_ne h4, cond_neg Bool.false_ne_true, cond_neg Bool.false_ne_true]

private theorem absorbNonce25_toSpec (st : Model.Keccak.State25) (p : Nat) (n : UInt64)
    (hp : p < 4) :
    (Model.Pcs.Whir.absorbNonce25 st p n).toSpec =
      ((((st.toSpec.set! (4 * p) n).set! (4 * p + 1) 0).set! (4 * p + 2) 0).set!
        (4 * p + 3) 4) := by
  have cases_p : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 := by omega
  rcases cases_p with c | c | c | c <;> subst p <;>
    simp [Model.Pcs.Whir.absorbNonce25, Model.Keccak.State25.toSpec]

private theorem grindS0_pending (sp : Spec.Transcript.Sponge) (hp : sp.pending ≤ 4) :
    (grindS0 sp).pending < 4 := by
  unfold grindS0
  refine Decidable.byCases (p := sp.pending = 4) (fun h4 => ?_) (fun h4 => ?_)
  · rw [show (sp.pending == 4) = true from beq_iff_eq.mpr h4, cond_pos rfl,
      Spec.Transcript.duplex]
    change 0 < 4
    decide
  · rw [beq_false_of_ne h4, cond_neg Bool.false_ne_true]
    omega

private theorem grindS0_size (sp : Spec.Transcript.Sponge) (hsz : sp.state.size = 25) :
    (grindS0 sp).state.size = 25 := by
  unfold grindS0
  refine Decidable.byCases (p := sp.pending = 4) (fun h4 => ?_) (fun h4 => ?_)
  · rw [show (sp.pending == 4) = true from beq_iff_eq.mpr h4, cond_pos rfl,
      Spec.Transcript.duplex]
    simp only [Array.size_map, Array.size_range]
  · rw [beq_false_of_ne h4, cond_neg Bool.false_ne_true, hsz]

private theorem fast_probe_eq_powBitsOk (sp : Spec.Transcript.Sponge) (hsz : sp.state.size = 25)
    (hp : sp.pending ≤ 4) (bits : Nat) (n : UInt64) :
    decide ((Model.Keccak.keccakF1600
        (Model.Pcs.Whir.absorbNonce25 (Model.Pcs.Whir.state25Of (grindS0 sp).state)
          (grindS0 sp).pending n)).a00 &&& Spec.Transcript.mask bits = 0) =
      Spec.Transcript.powBitsOk sp ⟨n, 0, 0⟩ bits := by
  have hp0 := grindS0_pending sp hp
  have hsz0 := grindS0_size sp hsz
  have habs := absorbNonce25_toSpec (Model.Pcs.Whir.state25Of (grindS0 sp).state)
    (grindS0 sp).pending n hp0
  rw [state25Of_toSpec _ hsz0] at habs
  have hperm := Proofs.Keccak.registers_permutation_refines_spec
    (Model.Pcs.Whir.absorbNonce25 (Model.Pcs.Whir.state25Of (grindS0 sp).state) (grindS0 sp).pending n)
  rw [Proofs.Keccak.spec_rounds_eq_permute, habs] at hperm
  have ha0 :
      (Model.Keccak.keccakF1600
          (Model.Pcs.Whir.absorbNonce25 (Model.Pcs.Whir.state25Of (grindS0 sp).state)
            (grindS0 sp).pending n)).a00 =
        (Spec.Keccak.permute
          ((((Array.set! (grindS0 sp).state (4 * (grindS0 sp).pending) n).set!
                (4 * (grindS0 sp).pending + 1) 0).set!
              (4 * (grindS0 sp).pending + 2) 0).set!
            (4 * (grindS0 sp).pending + 3) 4))[0]! := by
    simpa [Model.Keccak.State25.toSpec] using congrArg (fun a : Spec.Keccak.State => a[0]!) hperm
  rw [ha0]
  rfl

private theorem grindWhirFast_eq (s : Spec.Transcript.ProverState) (bits : Nat) :
    Model.Pcs.Whir.grindWhirFast s bits = Spec.Pcs.Whir.grindWhir s bits := by
  cases h : decide (s.sponge.state.size = 25 ∧ s.sponge.pending ≤ 4) with
  | false =>
    rw [Model.Pcs.Whir.grindWhirFast, h, cond_neg Bool.false_ne_true]
  | true =>
    have hs : s.sponge.state.size = 25 ∧ s.sponge.pending ≤ 4 := of_decide_eq_true h
    rw [Model.Pcs.Whir.grindWhirFast, h, cond_pos rfl, Spec.Pcs.Whir.grindWhir]
    refine Decidable.byCases (p := bits ≥ 64) (fun large => ?_) (fun large => ?_)
    · rw [cond_pos large, cond_pos large]
    · rw [cond_neg large, cond_neg large]
      rw [grindFast_s0 s.sponge hs.1]
      dsimp only
      refine Decidable.byCases (p := bits = 0) (fun hz => ?_) (fun hz => ?_)
      · rw [cond_pos hz, cond_pos hz]
      · rw [cond_neg hz, cond_neg hz]
        suffices hstep :
            (fun acc (k : Fin Spec.Pcs.Whir.grindFuel) =>
              match acc with
              | some _ => acc
              | none =>
                if decide ((Model.Keccak.keccakF1600
                    (Model.Pcs.Whir.absorbNonce25
                      (Model.Pcs.Whir.state25Of (grindS0 s.sponge).state)
                      (grindS0 s.sponge).pending (UInt64.ofNat k.val))).a00 &&&
                    Spec.Transcript.mask bits = 0) = true then
                  some (UInt64.ofNat k.val)
                else none) =
            (fun acc k =>
              match acc with
              | some _ => acc
              | none =>
                if Spec.Transcript.powBitsOk s.sponge ⟨UInt64.ofNat k.val, 0, 0⟩ bits then
                  some (UInt64.ofNat k.val)
                else none) by
          exact congrArg _ (congrArg (fun g => Fin.foldl Spec.Pcs.Whir.grindFuel g none) hstep)
        funext acc k
        cases acc with
        | some _ => rfl
        | none =>
          rw [fast_probe_eq_powBitsOk s.sponge hs.1 hs.2 bits (UInt64.ofNat k.val)]

private theorem proveLevel_eq :
    Model.Pcs.Whir.proveLevel = Spec.Pcs.Whir.proveLevel := by
  funext config logN p level rows
  simp only [Model.Pcs.Whir.proveLevel, Spec.Pcs.Whir.proveLevel, foldLanes_eq, foldTimes_eq,
    commitExt_eq, introduceOod_eq, grindWhirFast_eq, powers_eq_spec, openRowsModel_eq,
    enforcedSum_eq, inducedBasis_eq, sumcheckMsgEvenOdd_eq, gluePending_eq]
  rfl

theorem proveWhir_refines :
    Model.Pcs.Whir.proveWhir = Spec.Pcs.Whir.proveWhir := by
  funext s logN logInvRate witness weight target
  dsimp only [Model.Pcs.Whir.proveWhir, Spec.Pcs.Whir.proveWhir, Model.Pcs.Whir.deriveConfig]
  rw [l0Rows_eq, startLaneFold_eq, proveLevel_eq, stepFold_eq, absorbFold_eq]

theorem proveStackedOpening_refines :
    Model.Pcs.Whir.proveStackedOpening = Spec.Pcs.Whir.proveStackedOpening := by
  funext s stackLog logInvRate witness values basisTables
  simp only [Model.Pcs.Whir.proveStackedOpening, Spec.Pcs.Whir.proveStackedOpening, powers_eq_spec,
    dot_eq_spec, addScaled_eq_spec, proveWhir_refines]

theorem stackedWeight_refines :
    Model.Pcs.Whir.stackedWeight = Spec.Pcs.Whir.stackedWeight := by
  funext n lambda points ring ringWeights
  simp only [Model.Pcs.Whir.stackedWeight, Spec.Pcs.Whir.stackedWeight, powers_eq_spec,
    eqKernel_eq_spec, RingSwitch.nativeKaratsuba_eq_emul]
  rfl

theorem provePcsOpen_refines :
    Model.Pcs.Whir.provePcsOpen = Spec.Pcs.Whir.provePcsOpen := by
  funext s stackLog logInvRate witness points ring
  simp only [Model.Pcs.Whir.provePcsOpen, Spec.Pcs.Whir.provePcsOpen,
    RingSwitch.coordinateWeights_refines, powers_eq_spec, RingSwitch.nativeKaratsuba_eq_emul,
    RingSwitch.nativeMulBase_eq_mulBase, RingSwitch.transposeSlices_refines, dot_eq_spec,
    stackedWeight_refines, proveWhir_refines]

end LeanVmXmss.Proofs.Pcs.Whir
