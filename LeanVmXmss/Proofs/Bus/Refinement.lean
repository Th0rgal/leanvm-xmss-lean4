import Model.Bus.Scalar
import Proofs.Field.NativeKernel
import Proofs.Field.Operations
import Proofs.Layout.Basic
import Proofs.Transcript.Registers
import Proofs.Pcs.Refinement

namespace LeanVmXmss.Proofs.Bus

open Spec.Field (K E zero one)
open Spec.Layout
open Spec.Witness
open Model.Pcs.Ntt (foldRange foldRangeLoop)

set_option maxRecDepth 20000
set_option maxHeartbeats 400000

theorem nativeKaratsuba_eq_emul :
    Model.Field.nativeKaratsuba = Spec.Field.emul := by
  funext a b
  exact (Proofs.Field.nativeKaratsuba_correct a b).trans (Proofs.Field.karatsuba_refines_spec a b)

theorem nativeMul_eq_mul :
    Model.Field.nativeMul = Spec.Field.mul := by
  funext a b
  exact Proofs.Pcs.nativeMul_eq_spec a b

theorem nativeEinv_eq_einv :
    Model.Field.nativeEinv = Spec.Field.einv := by
  funext a
  exact (Proofs.Field.nativeEinv_correct a).trans (Proofs.Field.einv_refines_spec a)

theorem nativeMulBase_refines_spec (a : E) (b : K) :
    Model.Bus.nativeMulBase a b = Spec.Field.mulBase a b := by
  have hm : Model.Bus.nativeMulBase a b = Model.Field.mulBase a b := by
    simp only [Model.Bus.nativeMulBase, Model.Field.mulBase, Proofs.Field.nativeMul_correct]
  exact hm.trans (Proofs.Field.mulBase_refines_spec a b)

theorem nativeMulBase_eq_mulBase :
    Model.Bus.nativeMulBase = Spec.Field.mulBase := by
  funext a b
  exact nativeMulBase_refines_spec a b

theorem nativeEpow_refines_spec (x : E) (n : Nat) :
    Model.Bus.nativeEpow x n = Spec.Field.epow x n := by
  simp only [Model.Bus.nativeEpow, Spec.Field.epow, nativeKaratsuba_eq_emul]

theorem nativeEpow_eq_epow :
    Model.Bus.nativeEpow = Spec.Field.epow := by
  funext x n
  exact nativeEpow_refines_spec x n

private theorem add_eq_spec :
    Model.Field.add = Spec.Field.add := rfl

private theorem eadd_eq_spec :
    Model.Field.eadd = Spec.Field.eadd := rfl

theorem interp_refines_spec (lo hi t : E) :
    Model.Bus.interp lo hi t = Spec.Bus.interp lo hi t := by
  simp only [Model.Bus.interp, Spec.Bus.interp, nativeKaratsuba_eq_emul, eadd_eq_spec]

theorem interp_eq_spec : Model.Bus.interp = Spec.Bus.interp := by
  funext lo hi t
  exact interp_refines_spec lo hi t

theorem interpK_refines_spec (lo hi : K) (t : E) :
    Model.Bus.interpK lo hi t = Spec.Bus.interpK lo hi t := by
  simp only [Model.Bus.interpK, Spec.Bus.interpK, nativeMulBase_eq_mulBase,
    add_eq_spec, eadd_eq_spec]

theorem interpK_eq_spec : Model.Bus.interpK = Spec.Bus.interpK := by
  funext lo hi t
  exact interpK_refines_spec lo hi t

theorem eqEval_refines_spec (r x : Array E) :
    Model.Bus.eqEval r x = Spec.Bus.eqEval r x := by
  simp only [Model.Bus.eqEval, Spec.Bus.eqEval, nativeKaratsuba_eq_emul, eadd_eq_spec]

theorem eqEval_eq_spec : Model.Bus.eqEval = Spec.Bus.eqEval := by
  funext r x
  exact eqEval_refines_spec r x

theorem eqTable_refines_spec (r : Array E) :
    Model.Bus.eqTable r = Spec.Bus.eqTable r := by
  simp only [Model.Bus.eqTable, Spec.Bus.eqTable, nativeKaratsuba_eq_emul, eadd_eq_spec]

theorem eqTable_eq_spec : Model.Bus.eqTable = Spec.Bus.eqTable := by
  funext r
  exact eqTable_refines_spec r

theorem mleEval_refines_spec (table : Array K) (point : Array E) :
    Model.Bus.mleEval table point = Spec.Bus.mleEval table point := by
  simp only [Model.Bus.mleEval, Spec.Bus.mleEval, eqTable_eq_spec,
    nativeMulBase_eq_mulBase, eadd_eq_spec]

theorem mleEval_eq_spec : Model.Bus.mleEval = Spec.Bus.mleEval := by
  funext table point
  exact mleEval_refines_spec table point

theorem paddingWeight_refines_spec (point : Array E) (n : Nat) :
    Model.Bus.paddingWeight point n = Spec.Bus.paddingWeight point n := by
  simp only [Model.Bus.paddingWeight, Spec.Bus.paddingWeight, nativeKaratsuba_eq_emul, eadd_eq_spec]

theorem paddingWeight_eq_spec : Model.Bus.paddingWeight = Spec.Bus.paddingWeight := by
  funext point n
  exact paddingWeight_refines_spec point n

theorem indexMle_refines_spec (zeta : Array E) :
    Model.Bus.indexMle zeta = Spec.Bus.indexMle zeta := by
  simp only [Model.Bus.indexMle, Spec.Bus.indexMle, nativeKaratsuba_eq_emul,
    nativeMulBase_eq_mulBase, nativeMul_eq_mul, add_eq_spec, eadd_eq_spec]

theorem indexMle_eq_spec : Model.Bus.indexMle = Spec.Bus.indexMle := by
  funext zeta
  exact indexMle_refines_spec zeta

theorem polyEval_refines_spec (coeffs : Array E) (point : E) :
    Model.Bus.polyEval coeffs point = Spec.Bus.polyEval coeffs point := by
  simp only [Model.Bus.polyEval, Spec.Bus.polyEval, nativeKaratsuba_eq_emul, eadd_eq_spec]

theorem polyEval_eq_spec : Model.Bus.polyEval = Spec.Bus.polyEval := by
  funext coeffs point
  exact polyEval_refines_spec coeffs point

theorem fingerprintWeights_refines_spec (alphas : Array E) :
    Model.Bus.fingerprintWeights alphas = Spec.Bus.fingerprintWeights alphas := by
  simp only [Model.Bus.fingerprintWeights, Spec.Bus.fingerprintWeights,
    nativeKaratsuba_eq_emul, eadd_eq_spec]

theorem countWeights_refines_spec :
    Model.Bus.countWeights = Spec.Bus.countWeights := by
  simp only [Model.Bus.countWeights, Spec.Bus.countWeights, fingerprintWeights_refines_spec]

theorem buildColumns_refines_spec (program : Array Spec.Vm.Op) (sized : SizedRun)
    (message : Array K) :
    Model.Bus.buildColumns program sized message =
      Spec.Bus.buildColumns program sized message := by
  unfold Model.Bus.buildColumns Spec.Bus.buildColumns
  have hzero :
      (Model.Keccak.keccakF1600 Model.Layout.zeroState25).toSpec =
        Spec.Keccak.permute Spec.Keccak.zero := by
    rw [Proofs.Keccak.registers_permutation_refines_spec,
      Proofs.Keccak.spec_rounds_eq_permute, Proofs.Layout.zeroState25_toSpec]
  have hstep (s : Model.Keccak.State25) :
      (Model.Keccak.keccakF1600 s).toSpec = Spec.Keccak.permute s.toSpec := by
    rw [Proofs.Keccak.registers_permutation_refines_spec,
      Proofs.Keccak.spec_rounds_eq_permute]
  simp only [hzero, hstep]
  generalize Spec.Keccak.permute Spec.Keccak.zero = zp
  rfl

theorem evalAtom_gpowTable_eq (limit : Nat) (cols : Array (Array K)) (z : Nat) (a : Atom) :
    Model.Bus.evalAtom (Model.Layout.gpowTable limit) cols z a =
      Spec.Bus.evalAtom cols z a := by
  cases a <;>
    simp only [Model.Bus.evalAtom, Spec.Bus.evalAtom,
      Proofs.Layout.gAt_gpowTable_eq, nativeMul_eq_mul]

theorem evalCoord_gpowTable_eq (limit : Nat) (cols bcCols : Array (Array K))
    (z : Nat) (c : Coord) :
    Model.Bus.evalCoord (Model.Layout.gpowTable limit) cols bcCols z c =
      Spec.Bus.evalCoord cols bcCols z c := by
  cases c <;>
    simp only [Model.Bus.evalCoord, Spec.Bus.evalCoord,
      evalAtom_gpowTable_eq, Proofs.Layout.gAt_gpowTable_eq, add_eq_spec]

theorem buildSideLeaves_gpowTable_eq (limit : Nat) (blocks : Array Block) (lay : BusLayout)
    (cols bcCols : Array (Array K)) (w : Array E) (beta : E) :
    Model.Bus.buildSideLeaves (Model.Layout.gpowTable limit) blocks lay cols bcCols w beta =
      Spec.Bus.buildSideLeaves blocks lay cols bcCols w beta := by
  simp only [Model.Bus.buildSideLeaves, Spec.Bus.buildSideLeaves,
    evalCoord_gpowTable_eq, nativeMulBase_eq_mulBase, eadd_eq_spec]
  rfl

theorem nextLevel_refines_spec (current : Array E) :
    Model.Bus.nextLevel current = Spec.Bus.nextLevel current := by
  simp only [Model.Bus.nextLevel, Spec.Bus.nextLevel, nativeKaratsuba_eq_emul]

theorem buildLayers_refines_spec (leaves : Array E) (mu : Nat) :
    Model.Bus.buildLayers leaves mu = Spec.Bus.buildLayers leaves mu := by
  simp only [Model.Bus.buildLayers, Spec.Bus.buildLayers,
    funext nextLevel_refines_spec, nativeKaratsuba_eq_emul]

theorem quarticSummand_refines_spec (g0 s0 g1 s1 g2 s2 g3 s3 eqWeight : E) :
    Model.Bus.quarticSummand g0 s0 g1 s1 g2 s2 g3 s3 eqWeight =
      Spec.Bus.quarticSummand g0 s0 g1 s1 g2 s2 g3 s3 eqWeight := by
  simp only [Model.Bus.quarticSummand, Spec.Bus.quarticSummand,
    nativeKaratsuba_eq_emul, eadd_eq_spec]

theorem treeRoundMessage_refines_spec (values eqWeights : Array E) :
    Model.Bus.treeRoundMessage values eqWeights =
      Spec.Bus.treeRoundMessage values eqWeights := by
  simp only [Model.Bus.treeRoundMessage, Spec.Bus.treeRoundMessage,
    quarticSummand_refines_spec, Model.Bus.addMsg4, eadd_eq_spec]

theorem foldTreeScalar_refines_spec (values : Array E) (challenge : E) :
    Model.Bus.foldTreeScalar values challenge =
      Spec.Bus.foldTreeScalar values challenge := by
  simp only [Model.Bus.foldTreeScalar, Spec.Bus.foldTreeScalar, interp_eq_spec]

theorem combineMsg4_refines_spec (lambda : E) (m0 m1 m2 : E × E × E × E) :
    Model.Bus.combineMsg4 lambda m0 m1 m2 = Spec.Bus.combineMsg4 lambda m0 m1 m2 := by
  simp only [Model.Bus.combineMsg4, Spec.Bus.combineMsg4,
    nativeKaratsuba_eq_emul, eadd_eq_spec]

private theorem sponge_observe_pending (s : Model.Transcript.Registers.Sponge) (x : E) :
    (Model.Transcript.Registers.observe s x).pending ≤ 4 := by
  unfold Model.Transcript.Registers.observe Model.Transcript.Registers.absorb
  by_cases h4 : s.pending = 4
  · simp only [h4, ite_true, Proofs.Transcript.Registers.duplex_pending]
    omega
  · simp only [h4, ite_false]
    match hp : s.pending with
    | 0 => simp only []; omega
    | 1 => simp only []; omega
    | 2 => simp only []; omega
    | _ + 3 => simp only []; omega

private theorem sponge_sample_pending (s : Model.Transcript.Registers.Sponge) :
    (Model.Transcript.Registers.sample s).2.pending ≤ 4 := by
  change (Model.Transcript.Registers.duplex s).2.pending ≤ 4
  rw [Proofs.Transcript.Registers.duplex_pending]
  omega

private theorem initProverState_pending (iv : ByteArray) (publicInput : Array E) :
    (Model.Bus.initProverState iv publicInput).sponge.pending ≤ 4 := by
  have hz : (Model.Bus.initProverState iv publicInput).sponge.pending = 0 := rfl
  rw [hz]
  omega

private theorem initProverState_toSpec (iv : ByteArray) (publicInput : Array E) :
    (Model.Bus.initProverState iv publicInput).toSpec =
      Spec.Bus.initProverState iv publicInput := by
  unfold Model.Bus.initProverState Spec.Bus.initProverState Model.Bus.ProverState.toSpec
  simp only [Proofs.Transcript.Registers.init_refines]

private theorem addScalar_pending (ps : Model.Bus.ProverState) (x : E) :
    (Model.Bus.addScalar ps x).sponge.pending ≤ 4 := by
  cases ps
  exact sponge_observe_pending _ x

private theorem addScalar_toSpec (ps : Model.Bus.ProverState) (x : E)
    (h : ps.sponge.pending ≤ 4) :
    (Model.Bus.addScalar ps x).toSpec = Spec.Bus.addScalar ps.toSpec x := by
  rcases ps with ⟨sponge, stream⟩
  unfold Model.Bus.addScalar Spec.Bus.addScalar Model.Bus.ProverState.toSpec
  simp only [Proofs.Transcript.Registers.observe_refines sponge x h]

private theorem addScalars_loop_refines (xs : Array E) (rem idx : Nat)
    (ps : Model.Bus.ProverState) (h : ps.sponge.pending ≤ 4) :
    let out := foldRangeLoop (fun acc i => Model.Bus.addScalar acc (xs[i]?.getD zero)) rem idx ps
    out.sponge.pending ≤ 4 ∧
      out.toSpec =
        foldRangeLoop (fun acc i => Spec.Bus.addScalar acc (xs[i]?.getD zero)) rem idx ps.toSpec := by
  induction rem generalizing idx ps with
  | zero => exact ⟨h, rfl⟩
  | succ rem ih =>
    simp only [Proofs.Pcs.foldRangeLoop_succ]
    have h1 := addScalar_pending ps (xs[idx]?.getD zero)
    have hs := addScalar_toSpec ps (xs[idx]?.getD zero) h
    have next := ih (idx + 1) (Model.Bus.addScalar ps (xs[idx]?.getD zero)) h1
    rw [hs] at next
    exact next

private theorem addScalars_pending (ps : Model.Bus.ProverState) (xs : Array E)
    (h : ps.sponge.pending ≤ 4) :
    (Model.Bus.addScalars ps xs).sponge.pending ≤ 4 :=
  (addScalars_loop_refines xs xs.size 0 ps h).1

private theorem addScalars_toSpec (ps : Model.Bus.ProverState) (xs : Array E)
    (h : ps.sponge.pending ≤ 4) :
    (Model.Bus.addScalars ps xs).toSpec = Spec.Bus.addScalars ps.toSpec xs :=
  (addScalars_loop_refines xs xs.size 0 ps h).2

private theorem sampleChallenge_pending (ps : Model.Bus.ProverState) :
    (Model.Bus.sampleChallenge ps).2.sponge.pending ≤ 4 := by
  cases ps
  exact sponge_sample_pending _

private theorem sampleChallenge_toSpec (ps : Model.Bus.ProverState) :
    let r := Model.Bus.sampleChallenge ps
    (r.1, r.2.toSpec) = Spec.Bus.sampleChallenge ps.toSpec := by
  rcases ps with ⟨sponge, stream⟩
  unfold Model.Bus.sampleChallenge Spec.Bus.sampleChallenge Model.Bus.ProverState.toSpec
  have hs := Proofs.Transcript.Registers.sample_refines sponge
  have h1 := congrArg Prod.fst hs
  have h2 := congrArg Prod.snd hs
  dsimp at h1 h2 ⊢
  rw [h1, h2]


private def psRel (m : Model.Bus.ProverState) (s : Spec.Bus.ProverState) : Prop :=
  m.sponge.pending ≤ 4 ∧ m.toSpec = s

private theorem psRel_addScalar {m : Model.Bus.ProverState} {s : Spec.Bus.ProverState}
    (h : psRel m s) (x : E) :
    psRel (Model.Bus.addScalar m x) (Spec.Bus.addScalar s x) := by
  rcases h with ⟨hp, rfl⟩
  exact ⟨addScalar_pending m x, addScalar_toSpec m x hp⟩

private theorem psRel_addScalars {m : Model.Bus.ProverState} {s : Spec.Bus.ProverState}
    (h : psRel m s) (xs : Array E) :
    psRel (Model.Bus.addScalars m xs) (Spec.Bus.addScalars s xs) := by
  rcases h with ⟨hp, rfl⟩
  exact ⟨addScalars_pending m xs hp, addScalars_toSpec m xs hp⟩

private theorem psRel_sampleChallenge {m : Model.Bus.ProverState} {s : Spec.Bus.ProverState}
    (h : psRel m s) :
    (Model.Bus.sampleChallenge m).1 = (Spec.Bus.sampleChallenge s).1 ∧
      psRel (Model.Bus.sampleChallenge m).2 (Spec.Bus.sampleChallenge s).2 := by
  rcases h with ⟨_, rfl⟩
  have hs := sampleChallenge_toSpec m
  have h1 := congrArg Prod.fst hs
  have h2 := congrArg Prod.snd hs
  dsimp at h1 h2
  exact ⟨h1, sampleChallenge_pending m, h2⟩

private theorem foldRange_rel {α β : Type} (R : α → β → Prop)
    (f : α → Nat → α) (g : β → Nat → β)
    (hstep : ∀ a b i, R a b → R (f a i) (g b i))
    (n : Nat) (a : α) (b : β) (h0 : R a b) :
    R (foldRange n f a) (foldRange n g b) := by
  unfold foldRange
  suffices h : ∀ rem idx a b, R a b → R (foldRangeLoop f rem idx a) (foldRangeLoop g rem idx b) from
    h n 0 a b h0
  intro rem
  induction rem with
  | zero => intro idx a b hab; exact hab
  | succ rem ih =>
    intro idx a b hab
    rw [Proofs.Pcs.foldRangeLoop_succ, Proofs.Pcs.foldRangeLoop_succ]
    exact ih (idx + 1) (f a idx) (g b idx) (hstep a b idx hab)

private theorem natRec_rel {α β : Type} (R : α → β → Prop)
    (zA : α) (zB : β)
    (sA : Nat → α → α) (sB : Nat → β → β)
    (hz : R zA zB)
    (hs : ∀ n a b, R a b → R (sA n a) (sB n b))
    (steps : Nat) :
    R (Nat.rec (motive := fun _ => α) zA sA steps)
      (Nat.rec (motive := fun _ => β) zB sB steps) := by
  induction steps with
  | zero => exact hz
  | succ n ih => exact hs n _ _ ih

private theorem psRel_sampleVec {m : Model.Bus.ProverState} {s : Spec.Bus.ProverState}
    (h : psRel m s) (n : Nat) :
    (Model.Bus.sampleVec m n).1 = (Spec.Bus.sampleVec s n).1 ∧
      psRel (Model.Bus.sampleVec m n).2 (Spec.Bus.sampleVec s n).2 := by
  unfold Model.Bus.sampleVec Spec.Bus.sampleVec
  refine foldRange_rel
    (fun (x : Array E × Model.Bus.ProverState) (y : Array E × Spec.Bus.ProverState) =>
      x.1 = y.1 ∧ psRel x.2 y.2)
    _ _ ?_ n _ _ ⟨rfl, h⟩
  rintro ⟨aM, pM⟩ ⟨aS, pS⟩ _ ⟨rfl, hp⟩
  rcases psRel_sampleChallenge hp with ⟨hch, hps⟩
  dsimp only []
  rw [hch]
  exact ⟨rfl, hps⟩

theorem startTranscript_refines_spec (iv : ByteArray) (publicInput : Array E)
    (sized : SizedRun) (root : ByteArray) :
    (Model.Bus.startTranscript iv publicInput sized root).toSpec =
      Spec.Bus.startTranscript iv publicInput sized root ∧
    (Model.Bus.startTranscript iv publicInput sized root).sponge.pending ≤ 4 := by
  unfold Model.Bus.startTranscript Spec.Bus.startTranscript
  have h0 : psRel (Model.Bus.initProverState iv publicInput)
      (Spec.Bus.initProverState iv publicInput) :=
    ⟨initProverState_pending iv publicInput, initProverState_toSpec iv publicInput⟩
  have h1 := psRel_addScalars h0 (announceWords sized)
  have h2 := psRel_addScalars h1
    #[(Spec.Merkle.hashToScalars root).1, (Spec.Merkle.hashToScalars root).2]
  exact ⟨h2.2, h2.1⟩

private def innerStepRel
    (x : Array E × Array E × Array E × Array E × Array E × Model.Bus.ProverState)
    (y : Array E × Array E × Array E × Array E × Array E × Spec.Bus.ProverState) : Prop :=
  x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ x.2.2.1 = y.2.2.1 ∧ x.2.2.2.1 = y.2.2.2.1 ∧
    x.2.2.2.2.1 = y.2.2.2.2.1 ∧ psRel x.2.2.2.2.2 y.2.2.2.2.2

private def innerRel
    (x : Array E × Array E × Array E × Array E × Model.Bus.ProverState)
    (y : Array E × Array E × Array E × Array E × Spec.Bus.ProverState) : Prop :=
  x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ x.2.2.1 = y.2.2.1 ∧ x.2.2.2.1 = y.2.2.2.1 ∧
    psRel x.2.2.2.2 y.2.2.2.2

private theorem treeRoundFold_rel (lambda : E) (point : Array E) (roundCount : Nat)
    (t0 t1 t2 : Array E) (pM : Model.Bus.ProverState) (pS : Spec.Bus.ProverState)
    (hp : psRel pM pS) :
    innerRel (Model.Bus.treeRoundFold lambda point roundCount t0 t1 t2 pM)
      (Spec.Bus.treeRoundFold lambda point roundCount t0 t1 t2 pS) := by
  unfold Model.Bus.treeRoundFold Spec.Bus.treeRoundFold
  simp only [eqTable_eq_spec]
  have hStep : innerStepRel
      (foldRange roundCount
        (fun (eqW, s0, s1, s2, rp, pState) _ =>
          let m0 := Model.Bus.treeRoundMessage s0 eqW
          let m1 := Model.Bus.treeRoundMessage s1 eqW
          let m2 := Model.Bus.treeRoundMessage s2 eqW
          let coeffs := Model.Bus.combineMsg4 lambda m0 m1 m2
          let pState := Model.Bus.addScalars pState coeffs
          let (ch, pState) := Model.Bus.sampleChallenge pState
          (Model.Bus.shrinkEqLow eqW, Model.Bus.foldTreeScalar s0 ch,
            Model.Bus.foldTreeScalar s1 ch, Model.Bus.foldTreeScalar s2 ch,
            rp.push ch, pState))
        (Spec.Bus.eqTable (point.extract 1 point.size), t0, t1, t2,
          Array.emptyWithCapacity roundCount, pM))
      (foldRange roundCount
        (fun (eqW, s0, s1, s2, rp, pState) _ =>
          let m0 := Spec.Bus.treeRoundMessage s0 eqW
          let m1 := Spec.Bus.treeRoundMessage s1 eqW
          let m2 := Spec.Bus.treeRoundMessage s2 eqW
          let coeffs := Spec.Bus.combineMsg4 lambda m0 m1 m2
          let pState := Spec.Bus.addScalars pState coeffs
          let (ch, pState) := Spec.Bus.sampleChallenge pState
          (Spec.Bus.shrinkEqLow eqW, Spec.Bus.foldTreeScalar s0 ch,
            Spec.Bus.foldTreeScalar s1 ch, Spec.Bus.foldTreeScalar s2 ch,
            rp.push ch, pState))
        (Spec.Bus.eqTable (point.extract 1 point.size), t0, t1, t2,
          Array.emptyWithCapacity roundCount, pS)) := by
    refine foldRange_rel innerStepRel _ _ ?_ roundCount _ _ ⟨rfl, rfl, rfl, rfl, rfl, hp⟩
    rintro ⟨eqM, s0M, s1M, s2M, rpM, stM⟩ ⟨eqS, s0S, s1S, s2S, rpS, stS⟩ _
      ⟨rfl, rfl, rfl, rfl, rfl, hpSt⟩
    dsimp only []
    simp only [Model.Bus.shrinkEqLow, treeRoundMessage_refines_spec,
      combineMsg4_refines_spec, foldTreeScalar_refines_spec]
    rcases psRel_sampleChallenge (psRel_addScalars hpSt _) with ⟨hChR, hpSt2⟩
    rw [hChR]
    exact ⟨rfl, rfl, rfl, rfl, rfl, hpSt2⟩
  exact ⟨hStep.2.1, hStep.2.2.1, hStep.2.2.2.1, hStep.2.2.2.2.1, hStep.2.2.2.2.2⟩

private def tripleRel (m : Array E × Array E × Model.Bus.ProverState)
    (s : Array E × Array E × Spec.Bus.ProverState) : Prop :=
  m.1 = s.1 ∧ m.2.1 = s.2.1 ∧ psRel m.2.2 s.2.2

private theorem prodTripleOut_rel
    {m : Array E × Array E × Model.Bus.ProverState}
    {s : Array E × Array E × Spec.Bus.ProverState}
    (h : tripleRel m s) :
    ((⟨m.1, m.2.1⟩, m.2.2) : Spec.Bus.ProductTriple × Model.Bus.ProverState).2.sponge.pending ≤ 4 ∧
      (((⟨m.1, m.2.1⟩, m.2.2) : Spec.Bus.ProductTriple × Model.Bus.ProverState).1,
        ((⟨m.1, m.2.1⟩, m.2.2) : Spec.Bus.ProductTriple × Model.Bus.ProverState).2.toSpec) =
        ((⟨s.1, s.2.1⟩, s.2.2) : Spec.Bus.ProductTriple × Spec.Bus.ProverState) := by
  rcases h with ⟨h1, h2, hp, hs⟩
  dsimp only []
  rw [h1, h2, hs]
  exact ⟨hp, rfl⟩

private theorem proveProductTriple_refines_spec (leaves0 leaves1 leaves2 : Array E) (mu : Nat)
    (ps : Model.Bus.ProverState) (h : ps.sponge.pending ≤ 4) :
    let m := Model.Bus.proveProductTriple leaves0 leaves1 leaves2 mu ps
    let s := Spec.Bus.proveProductTriple leaves0 leaves1 leaves2 mu ps.toSpec
    m.2.sponge.pending ≤ 4 ∧ (m.1, m.2.toSpec) = s := by
  unfold Model.Bus.proveProductTriple Spec.Bus.proveProductTriple
  simp only [buildLayers_refines_spec, Model.Bus.padFourMultiple, Model.Bus.treeChildren,
    interp_eq_spec]
  generalize Spec.Bus.buildLayers leaves0 mu = layers0
  generalize Spec.Bus.buildLayers leaves1 mu = layers1
  generalize Spec.Bus.buildLayers leaves2 mu = layers2
  apply prodTripleOut_rel
  refine (natRec_rel
    (fun (fM : Nat → Array E → Array E → Model.Bus.ProverState →
        Array E × Array E × Model.Bus.ProverState)
         (fS : Nat → Array E → Array E → Spec.Bus.ProverState →
        Array E × Array E × Spec.Bus.ProverState) =>
      ∀ layer point values pM pS, psRel pM pS →
        tripleRel (fM layer point values pM) (fS layer point values pS))
    _ _ _ _
    (fun _ _ _ _ _ hp => ⟨rfl, rfl, hp⟩)
    (fun _ prevM prevS ih layer point values pM pS hp => ?_)
    ((mu + 1) / 2)) mu #[] _ _ _ (psRel_addScalar (psRel_addScalar ⟨h, rfl⟩ _) _)
  by_cases hl0 : layer = 0
  · subst hl0
    exact ⟨rfl, rfl, hp⟩
  · simp only [hl0, ↓reduceIte]
    rcases psRel_sampleChallenge hp with ⟨hLam, hpLam⟩
    rw [hLam]
    by_cases hodd : layer % 2 = 1
    · simp only [hodd, ↓reduceIte]
      rcases psRel_sampleChallenge (psRel_addScalars hpLam _) with ⟨hCh, hpCh⟩
      rw [hCh]
      exact ih _ _ _ _ _ hpCh
    · simp only [hodd, ↓reduceIte]
      have hIn := treeRoundFold_rel (Spec.Bus.sampleChallenge pS).1 point (mu - layer)
        (Spec.Bus.padFourMultiple (layers0[layer - 2]?.getD #[]))
        (Spec.Bus.padFourMultiple (layers1[layer - 2]?.getD #[]))
        (Spec.Bus.padFourMultiple (layers2[layer - 2]?.getD #[]))
        (Model.Bus.sampleChallenge pM).2 (Spec.Bus.sampleChallenge pS).2 hpLam
      rcases hMIn : Model.Bus.treeRoundFold (Spec.Bus.sampleChallenge pS).1 point (mu - layer)
        (Spec.Bus.padFourMultiple (layers0[layer - 2]?.getD #[]))
        (Spec.Bus.padFourMultiple (layers1[layer - 2]?.getD #[]))
        (Spec.Bus.padFourMultiple (layers2[layer - 2]?.getD #[]))
        (Model.Bus.sampleChallenge pM).2 with ⟨t0M, t1M, t2M, rpM, pM2⟩
      rcases hSIn : Spec.Bus.treeRoundFold (Spec.Bus.sampleChallenge pS).1 point (mu - layer)
        (Spec.Bus.padFourMultiple (layers0[layer - 2]?.getD #[]))
        (Spec.Bus.padFourMultiple (layers1[layer - 2]?.getD #[]))
        (Spec.Bus.padFourMultiple (layers2[layer - 2]?.getD #[]))
        (Spec.Bus.sampleChallenge pS).2 with ⟨t0S, t1S, t2S, rpS, pS2⟩
      rw [hMIn, hSIn] at hIn
      rcases hIn with ⟨rfl, rfl, rfl, rfl, hpAfterIn⟩
      dsimp only [] at hpAfterIn ⊢
      have hpC := psRel_addScalars (psRel_addScalars
        (psRel_addScalars hpAfterIn (Spec.Bus.treeChildren t0M))
        (Spec.Bus.treeChildren t1M)) (Spec.Bus.treeChildren t2M)
      rcases psRel_sampleChallenge hpC with ⟨hLo, hpLo⟩
      rcases psRel_sampleChallenge hpLo with ⟨hHi, hpHi⟩
      rw [hLo, hHi]
      exact ih _ _ _ _ _ hpHi


theorem scaleBusForm_refines_spec (form : Spec.Bus.BusForm) (factor : E) :
    Model.Bus.scaleBusForm form factor = Spec.Bus.scaleBusForm form factor := by
  simp only [Model.Bus.scaleBusForm, Spec.Bus.scaleBusForm, nativeKaratsuba_eq_emul]

theorem accumulateAtom_gpowTable_eq (limit base : Nat) (w : E) (form : Spec.Bus.BusForm)
    (a : Atom) :
    Model.Bus.accumulateAtom (Model.Layout.gpowTable limit) base w form a =
      Spec.Bus.accumulateAtom base w form a := by
  cases a <;>
    simp only [Model.Bus.accumulateAtom, Spec.Bus.accumulateAtom,
      Proofs.Layout.gAt_gpowTable_eq, nativeMulBase_eq_mulBase, eadd_eq_spec]

theorem accumulateCoord_gpowTable_eq (limit base : Nat) (w : E) (form : Spec.Bus.BusForm)
    (c : Coord) :
    Model.Bus.accumulateCoord (Model.Layout.gpowTable limit) base w form c =
      Spec.Bus.accumulateCoord base w form c := by
  cases c <;>
    simp only [Model.Bus.accumulateCoord, Spec.Bus.accumulateCoord,
      accumulateAtom_gpowTable_eq]

private def decompNoneRel
    (x : E × Array Spec.Bus.ColumnClaim × Model.Bus.ProverState)
    (y : E × Array Spec.Bus.ColumnClaim × Spec.Bus.ProverState) : Prop :=
  x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ psRel x.2.2 y.2.2

private theorem decomposeNoneCoords_rel (limit : Nat) (blk : Block)
    (cols bcCols : Array (Array K)) (zetaLo w : Array E)
    (curClaims : Array Spec.Bus.ColumnClaim)
    (pM : Model.Bus.ProverState) (pS : Spec.Bus.ProverState) (hp : psRel pM pS) :
    decompNoneRel
      (Model.Bus.decomposeNoneCoords (Model.Layout.gpowTable limit) blk cols bcCols zetaLo w curClaims pM)
      (Spec.Bus.decomposeNoneCoords blk cols bcCols zetaLo w curClaims pS) := by
  unfold Model.Bus.decomposeNoneCoords Spec.Bus.decomposeNoneCoords
  refine foldRange_rel decompNoneRel _ _ ?_ blk.coords.size _ _ ⟨rfl, rfl, hp⟩
  rintro ⟨iaM, caM, paM⟩ ⟨iaS, caS, paS⟩ i ⟨rfl, rfl, hpAcc⟩
  dsimp only []
  simp only [nativeMulBase_eq_mulBase, nativeKaratsuba_eq_emul, eadd_eq_spec,
    indexMle_eq_spec, mleEval_eq_spec, Model.Bus.findKnownClaim, Proofs.Layout.gAt_gpowTable_eq]
  cases hCoord : blk.coords[i]?.getD (cConst 0) with
  | atom a =>
    cases a with
    | const v => exact ⟨rfl, rfl, hpAcc⟩
    | col colIdx =>
      dsimp only []
      cases Spec.Bus.findKnownClaim caM colIdx zetaLo with
      | some v => exact ⟨rfl, rfl, hpAcc⟩
      | none => exact ⟨rfl, rfl, psRel_addScalar hpAcc _⟩
    | gcol colIdx k =>
      dsimp only []
      cases Spec.Bus.findKnownClaim caM colIdx zetaLo with
      | some v => exact ⟨rfl, rfl, hpAcc⟩
      | none => exact ⟨rfl, rfl, psRel_addScalar hpAcc _⟩
    | prod i0 j0 k0 => exact ⟨rfl, rfl, hpAcc⟩
  | index => exact ⟨rfl, rfl, hpAcc⟩
  | publicCol slot => exact ⟨rfl, rfl, hpAcc⟩
  | sum terms => exact ⟨rfl, rfl, hpAcc⟩

private def decompFoldRel
    (x : E × E × Array Spec.Bus.BusForm × Array Spec.Bus.ColumnClaim × Model.Bus.ProverState)
    (y : E × E × Array Spec.Bus.BusForm × Array Spec.Bus.ColumnClaim × Spec.Bus.ProverState) : Prop :=
  x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ x.2.2.1 = y.2.2.1 ∧ x.2.2.2.1 = y.2.2.2.1 ∧
    psRel x.2.2.2.2 y.2.2.2.2

private theorem decomposeSideFold_rel (limit : Nat) (blocks : Array Block) (lay : BusLayout)
    (cols bcCols : Array (Array K)) (zeta w : Array E) (beta : E)
    (forms : Array Spec.Bus.BusForm) (claims : Array Spec.Bus.ColumnClaim)
    (pM : Model.Bus.ProverState) (pS : Spec.Bus.ProverState) (hp : psRel pM pS) :
    decompFoldRel
      (Model.Bus.decomposeSideFold (Model.Layout.gpowTable limit) blocks lay cols bcCols
        zeta w beta forms claims pM)
      (Spec.Bus.decomposeSideFold blocks lay cols bcCols zeta w beta forms claims pS) := by
  unfold Model.Bus.decomposeSideFold Spec.Bus.decomposeSideFold
  refine foldRange_rel decompFoldRel _ _ ?_ blocks.size _ _ ⟨rfl, rfl, rfl, rfl, hp⟩
  rintro ⟨accM, selM, fM, cM, stM⟩ ⟨accS, selS, fS, cS, stS⟩ b ⟨rfl, rfl, rfl, rfl, hpSt⟩
  dsimp only []
  cases blocks[b]? with
  | none => exact ⟨rfl, rfl, rfl, rfl, hpSt⟩
  | some blk =>
    dsimp only []
    simp only [Model.Bus.selectorPoint, eqEval_eq_spec, eadd_eq_spec, Model.Bus.emptyBusForm,
      nativeKaratsuba_eq_emul, accumulateCoord_gpowTable_eq, nativeMulBase_eq_mulBase,
      paddingWeight_eq_spec]
    cases blk.owner with
    | some t =>
      dsimp only []
      cases curForm : fM[t.val]?.getD (Spec.Bus.emptyBusForm (tableWidth t))
      exact ⟨rfl, rfl, rfl, rfl, hpSt⟩
    | none =>
      dsimp only []
      have hN := decomposeNoneCoords_rel limit blk cols bcCols
        (zeta.extract 0 blk.kappa) w cM stM stS hpSt
      rcases hMN : Model.Bus.decomposeNoneCoords (Model.Layout.gpowTable limit) blk cols bcCols
        (zeta.extract 0 blk.kappa) w cM stM with ⟨inM, ncM, npM⟩
      rcases hSN : Spec.Bus.decomposeNoneCoords blk cols bcCols
        (zeta.extract 0 blk.kappa) w cM stS with ⟨inS, ncS, npS⟩
      rw [hMN, hSN] at hN
      rcases hN with ⟨rfl, rfl, hpNext⟩
      exact ⟨rfl, rfl, rfl, rfl, hpNext⟩

private def decompOutRel
    (x : E × Array Spec.Bus.BusForm × Array Spec.Bus.ColumnClaim × Model.Bus.ProverState)
    (y : E × Array Spec.Bus.BusForm × Array Spec.Bus.ColumnClaim × Spec.Bus.ProverState) : Prop :=
  x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ x.2.2.1 = y.2.2.1 ∧ psRel x.2.2.2 y.2.2.2

private theorem decomposeSide_rel (limit : Nat) (blocks : Array Block) (lay : BusLayout)
    (cols bcCols : Array (Array K)) (zeta w : Array E) (beta : E)
    (forms : Array Spec.Bus.BusForm) (claims : Array Spec.Bus.ColumnClaim)
    (pM : Model.Bus.ProverState) (pS : Spec.Bus.ProverState) (hp : psRel pM pS) :
    decompOutRel
      (Model.Bus.decomposeSide (Model.Layout.gpowTable limit) blocks lay cols bcCols
        zeta w beta forms claims pM)
      (Spec.Bus.decomposeSide blocks lay cols bcCols zeta w beta forms claims pS) := by
  unfold Model.Bus.decomposeSide Spec.Bus.decomposeSide
  have hF := decomposeSideFold_rel limit blocks lay cols bcCols zeta w beta forms claims pM pS hp
  rcases hMF : Model.Bus.decomposeSideFold (Model.Layout.gpowTable limit) blocks lay cols bcCols
    zeta w beta forms claims pM with ⟨accM, selM, fM, cM, stM⟩
  rcases hSF : Spec.Bus.decomposeSideFold blocks lay cols bcCols
    zeta w beta forms claims pS with ⟨accS, selS, fS, cS, stS⟩
  rw [hMF, hSF] at hF
  rcases hF with ⟨rfl, rfl, rfl, rfl, hpOut⟩
  exact ⟨rfl, rfl, rfl, hpOut⟩


theorem evalBusFormSigma_refines_spec (form : Spec.Bus.BusForm) (colEvals : Array E)
    (prodSums : Array (Nat × Nat × E)) :
    Model.Bus.evalBusFormSigma form colEvals prodSums =
      Spec.Bus.evalBusFormSigma form colEvals prodSums := by
  simp only [Model.Bus.evalBusFormSigma, Spec.Bus.evalBusFormSigma,
    nativeKaratsuba_eq_emul, eadd_eq_spec, Model.Bus.findProdSum]
  rfl

theorem computeTableSigmas_refines_spec (cols : Array (Array K)) (taus : Array Nat)
    (forms0 forms1 forms2 : Array Spec.Bus.BusForm) (zeta : Array E) :
    Model.Bus.computeTableSigmas cols taus forms0 forms1 forms2 zeta =
      Spec.Bus.computeTableSigmas cols taus forms0 forms1 forms2 zeta := by
  simp only [Model.Bus.computeTableSigmas, Spec.Bus.computeTableSigmas,
    eqTable_eq_spec, nativeMulBase_eq_mulBase, nativeMul_eq_mul, eadd_eq_spec,
    Model.Bus.emptyBusForm, Model.Bus.hasPair, evalBusFormSigma_refines_spec]
  rfl

private theorem proveBalance_rel (limit : Nat) (lay : Model.Layout.PublicLayout)
    (cols bcCols : Array (Array K))
    (pM : Model.Bus.ProverState) (pS : Spec.Bus.ProverState) (hp : psRel pM pS) :
    (Model.Bus.proveBalance (Model.Layout.gpowTable limit) lay cols bcCols pM).1 =
      (Spec.Bus.proveBalance lay cols bcCols pS).1 ∧
    psRel (Model.Bus.proveBalance (Model.Layout.gpowTable limit) lay cols bcCols pM).2
      (Spec.Bus.proveBalance lay cols bcCols pS).2 := by
  unfold Model.Bus.proveBalance Spec.Bus.proveBalance
  have hA := psRel_sampleVec hp busBits
  cases hMA : Model.Bus.sampleVec pM busBits with
  | mk alphasM pM1 =>
  cases hSA : Spec.Bus.sampleVec pS busBits with
  | mk alphasS pS1 =>
  rw [hMA, hSA] at hA
  rcases hA with ⟨rfl, hp1⟩
  dsimp only []
  have hB := psRel_sampleChallenge hp1
  cases hMB : Model.Bus.sampleChallenge pM1 with
  | mk betaM pM2 =>
  cases hSB : Spec.Bus.sampleChallenge pS1 with
  | mk betaS pS2 =>
  rw [hMB, hSB] at hB
  rcases hB with ⟨rfl, hp2⟩
  dsimp only [] at hp1 hp2 ⊢
  simp only [fingerprintWeights_refines_spec, countWeights_refines_spec,
    buildSideLeaves_gpowTable_eq, Model.Bus.initTableForms, computeTableSigmas_refines_spec]
  rcases hp2 with ⟨hp2Pend, rfl⟩
  have hGkr := proveProductTriple_refines_spec
    (Spec.Bus.buildSideLeaves lay.push lay.pushLayout cols bcCols
      (Spec.Bus.fingerprintWeights alphasM) betaM)
    (Spec.Bus.buildSideLeaves lay.pull lay.pullLayout cols bcCols
      (Spec.Bus.fingerprintWeights alphasM) betaM)
    (Spec.Bus.buildSideLeaves lay.count { lay.countLayout with mu := lay.pushLayout.mu }
      cols bcCols Spec.Bus.countWeights zero)
    lay.pushLayout.mu pM2 hp2Pend
  cases hMG : Model.Bus.proveProductTriple
    (Spec.Bus.buildSideLeaves lay.push lay.pushLayout cols bcCols
      (Spec.Bus.fingerprintWeights alphasM) betaM)
    (Spec.Bus.buildSideLeaves lay.pull lay.pullLayout cols bcCols
      (Spec.Bus.fingerprintWeights alphasM) betaM)
    (Spec.Bus.buildSideLeaves lay.count { lay.countLayout with mu := lay.pushLayout.mu }
      cols bcCols Spec.Bus.countWeights zero)
    lay.pushLayout.mu pM2 with
  | mk gkrM pM3 =>
  cases hSG : Spec.Bus.proveProductTriple
    (Spec.Bus.buildSideLeaves lay.push lay.pushLayout cols bcCols
      (Spec.Bus.fingerprintWeights alphasM) betaM)
    (Spec.Bus.buildSideLeaves lay.pull lay.pullLayout cols bcCols
      (Spec.Bus.fingerprintWeights alphasM) betaM)
    (Spec.Bus.buildSideLeaves lay.count { lay.countLayout with mu := lay.pushLayout.mu }
      cols bcCols Spec.Bus.countWeights zero)
    lay.pushLayout.mu pM2.toSpec with
  | mk gkrS pS3 =>
  rw [hMG, hSG] at hGkr
  dsimp only [] at hGkr ⊢
  have hG1 := congrArg Prod.fst hGkr.2
  have hG2 := congrArg Prod.snd hGkr.2
  dsimp only [] at hG1 hG2
  subst hG1
  have hp3 : psRel pM3 pS3 := ⟨hGkr.1, hG2⟩
  have hD0 := decomposeSide_rel limit lay.push lay.pushLayout cols bcCols gkrM.point
    (Spec.Bus.fingerprintWeights alphasM) betaM Spec.Bus.initTableForms #[] pM3 pS3 hp3
  cases hMD0 : Model.Bus.decomposeSide (Model.Layout.gpowTable limit) lay.push lay.pushLayout
    cols bcCols gkrM.point (Spec.Bus.fingerprintWeights alphasM) betaM
    Spec.Bus.initTableForms #[] pM3 with
  | mk v0M rest0M =>
  rcases rest0M with ⟨f0M, c0M, pM4⟩
  cases hSD0 : Spec.Bus.decomposeSide lay.push lay.pushLayout
    cols bcCols gkrM.point (Spec.Bus.fingerprintWeights alphasM) betaM
    Spec.Bus.initTableForms #[] pS3 with
  | mk v0S rest0S =>
  rcases rest0S with ⟨f0S, c0S, pS4⟩
  rw [hMD0, hSD0] at hD0
  rcases hD0 with ⟨rfl, rfl, rfl, hp4⟩
  dsimp only [] at hp4 ⊢
  have hD1 := decomposeSide_rel limit lay.pull lay.pullLayout cols bcCols gkrM.point
    (Spec.Bus.fingerprintWeights alphasM) betaM Spec.Bus.initTableForms c0M pM4 pS4 hp4
  cases hMD1 : Model.Bus.decomposeSide (Model.Layout.gpowTable limit) lay.pull lay.pullLayout
    cols bcCols gkrM.point (Spec.Bus.fingerprintWeights alphasM) betaM
    Spec.Bus.initTableForms c0M pM4 with
  | mk v1M rest1M =>
  rcases rest1M with ⟨f1M, c1M, pM5⟩
  cases hSD1 : Spec.Bus.decomposeSide lay.pull lay.pullLayout
    cols bcCols gkrM.point (Spec.Bus.fingerprintWeights alphasM) betaM
    Spec.Bus.initTableForms c0M pS4 with
  | mk v1S rest1S =>
  rcases rest1S with ⟨f1S, c1S, pS5⟩
  rw [hMD1, hSD1] at hD1
  rcases hD1 with ⟨rfl, rfl, rfl, hp5⟩
  dsimp only [] at hp5 ⊢
  have hD2 := decomposeSide_rel limit lay.count { lay.countLayout with mu := lay.pushLayout.mu }
    cols bcCols gkrM.point Spec.Bus.countWeights zero Spec.Bus.initTableForms c1M pM5 pS5 hp5
  cases hMD2 : Model.Bus.decomposeSide (Model.Layout.gpowTable limit) lay.count
    { lay.countLayout with mu := lay.pushLayout.mu } cols bcCols gkrM.point
    Spec.Bus.countWeights zero Spec.Bus.initTableForms c1M pM5 with
  | mk v2M rest2M =>
  rcases rest2M with ⟨f2M, c2M, pM6⟩
  cases hSD2 : Spec.Bus.decomposeSide lay.count
    { lay.countLayout with mu := lay.pushLayout.mu } cols bcCols gkrM.point
    Spec.Bus.countWeights zero Spec.Bus.initTableForms c1M pS5 with
  | mk v2S rest2S =>
  rcases rest2S with ⟨f2S, c2S, pS6⟩
  rw [hMD2, hSD2] at hD2
  rcases hD2 with ⟨rfl, rfl, rfl, hp6⟩
  dsimp only [] at hp6 ⊢
  cases Spec.Bus.computeTableSigmas cols lay.taus f0M f1M f2M gkrM.point
  exact ⟨rfl, hp6⟩


theorem powersOf_refines_spec (x : E) (count : Nat) :
    Model.Bus.powersOf x count = Spec.Bus.powersOf x count := by
  simp only [Model.Bus.powersOf, Spec.Bus.powersOf, nativeEpow_eq_epow]

theorem buildAirs_refines_spec (taus : Array Nat) (bus : Spec.Bus.BusProof) (xi : E) :
    Model.Bus.buildAirs taus bus xi = Spec.Bus.buildAirs taus bus xi := by
  simp only [Model.Bus.buildAirs, Spec.Bus.buildAirs, powersOf_refines_spec,
    Model.Bus.tableIdentityForm, Model.Bus.emptyBusForm, scaleBusForm_refines_spec,
    Model.Bus.addBusForm, nativeKaratsuba_eq_emul, eadd_eq_spec]

theorem tableMessageK_refines_spec (gf : Spec.Bus.GroupedForm) (cols : Array (Array K))
    (base : Nat) (eqr : Array E) (half : Nat) (atOne : Bool) :
    Model.Bus.tableMessageK gf cols base eqr half atOne =
      Spec.Bus.tableMessageK gf cols base eqr half atOne := by
  simp only [Model.Bus.tableMessageK, Spec.Bus.tableMessageK,
    Model.Bus.evalLinK, Spec.Bus.evalLinK, Model.Bus.evalLinSumK, Spec.Bus.evalLinSumK,
    nativeMulBase_eq_mulBase, nativeKaratsuba_eq_emul, add_eq_spec, eadd_eq_spec]
  rfl

theorem joinTableState_refines_spec (gf : Spec.Bus.GroupedForm) (cols : Array (Array K))
    (base : Nat) (r : E) (half : Nat) :
    Model.Bus.joinTableState gf cols base r half =
      Spec.Bus.joinTableState gf cols base r half := by
  simp only [Model.Bus.joinTableState, Spec.Bus.joinTableState,
    nativeKaratsuba_eq_emul, nativeMulBase_eq_mulBase, interpK_eq_spec,
    add_eq_spec, eadd_eq_spec]
  rfl

theorem tableMessageE_refines_spec (constant : E) (state : Array (Array E))
    (eqr : Array E) (half : Nat) (atOne : Bool) :
    Model.Bus.tableMessageE constant state eqr half atOne =
      Spec.Bus.tableMessageE constant state eqr half atOne := by
  simp only [Model.Bus.tableMessageE, Spec.Bus.tableMessageE,
    nativeKaratsuba_eq_emul, eadd_eq_spec]

theorem foldTableState_refines_spec (state : Array (Array E)) (r : E) (half : Nat) :
    Model.Bus.foldTableState state r half =
      Spec.Bus.foldTableState state r half := by
  simp only [Model.Bus.foldTableState, Spec.Bus.foldTableState, interp_eq_spec]

theorem roundPolynomial_refines_spec (endpoint quadratic zetaM claim waiting : E) :
    Model.Bus.roundPolynomial endpoint quadratic zetaM claim waiting =
      Spec.Bus.roundPolynomial endpoint quadratic zetaM claim waiting := by
  simp only [Model.Bus.roundPolynomial, Spec.Bus.roundPolynomial,
    nativeKaratsuba_eq_emul, nativeEinv_eq_einv, eadd_eq_spec]

private theorem constraintsRoundMsgs_eq (airs : Array Spec.Bus.AirTable)
    (gForms : Array Spec.Bus.GroupedForm) (cols : Array (Array K))
    (weights : Array E) (states : Array (Option (Array (Array E))))
    (eqr : Array E) (m half : Nat) (atOne : Bool) :
    Model.Bus.constraintsRoundMsgs airs gForms cols weights states eqr m half atOne =
      Spec.Bus.constraintsRoundMsgs airs gForms cols weights states eqr m half atOne := by
  simp only [Model.Bus.constraintsRoundMsgs, Spec.Bus.constraintsRoundMsgs,
    tableMessageE_refines_spec, tableMessageK_refines_spec,
    nativeKaratsuba_eq_emul, eadd_eq_spec]
  rfl

private theorem constraintsUpdateTables_eq (airs : Array Spec.Bus.AirTable)
    (gForms : Array Spec.Bus.GroupedForm) (cols : Array (Array K))
    (weights : Array E) (states : Array (Option (Array (Array E))))
    (m half : Nat) (rk eqK : E) :
    Model.Bus.constraintsUpdateTables airs gForms cols weights states m half rk eqK =
      Spec.Bus.constraintsUpdateTables airs gForms cols weights states m half rk eqK := by
  simp only [Model.Bus.constraintsUpdateTables, Spec.Bus.constraintsUpdateTables,
    foldTableState_refines_spec, joinTableState_refines_spec, nativeKaratsuba_eq_emul]
  rfl

private def conRoundRel
    (x : Array E × Array E × E × E × (Array E × Array (Option (Array (Array E)))) ×
      Model.Bus.ProverState)
    (y : Array E × Array E × E × E × (Array E × Array (Option (Array (Array E)))) ×
      Spec.Bus.ProverState) : Prop :=
  x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ x.2.2.1 = y.2.2.1 ∧ x.2.2.2.1 = y.2.2.2.1 ∧
    x.2.2.2.2.1 = y.2.2.2.2.1 ∧ psRel x.2.2.2.2.2 y.2.2.2.2.2

private theorem constraintsRoundsFold_rel (airs : Array Spec.Bus.AirTable)
    (gForms : Array Spec.Bus.GroupedForm) (cols : Array (Array K)) (zeta : Array E)
    (n : Nat) (eqr0 chi0 : Array E) (claim0 : E) (weights0 : Array E)
    (states0 : Array (Option (Array (Array E))))
    (pM : Model.Bus.ProverState) (pS : Spec.Bus.ProverState) (hp : psRel pM pS) :
    conRoundRel
      (Model.Bus.constraintsRoundsFold airs gForms cols zeta n eqr0 chi0 claim0
        weights0 states0 pM)
      (Spec.Bus.constraintsRoundsFold airs gForms cols zeta n eqr0 chi0 claim0
        weights0 states0 pS) := by
  unfold Model.Bus.constraintsRoundsFold Spec.Bus.constraintsRoundsFold
  refine foldRange_rel conRoundRel _ _ ?_ n _ _ ⟨rfl, rfl, rfl, rfl, rfl, hp⟩
  rintro ⟨eqrM, chiM, kM, clM, ⟨wM, sM⟩, stM⟩ ⟨eqrS, chiS, kS, clS, ⟨wS, sS⟩, stS⟩ j
    ⟨rfl, rfl, rfl, rfl, hws, hpSt⟩
  dsimp only [] at hws hpSt ⊢
  injection hws with hw hs
  subst hw
  subst hs
  simp only [eadd_eq_spec, nativeKaratsuba_eq_emul, constraintsRoundMsgs_eq,
    Model.Bus.shrinkEqHigh, roundPolynomial_refines_spec, polyEval_eq_spec,
    constraintsUpdateTables_eq]
  cases Spec.Bus.constraintsRoundMsgs airs gForms cols wM sM eqrM (n - 1 - j)
    (1 <<< (n - 1 - j)) (Spec.Vm.wordBEq (zeta[n - 1 - j]?.getD zero) zero)
  dsimp only []
  rcases psRel_sampleChallenge (psRel_addScalars hpSt _) with ⟨hRk, hpSt2⟩
  rw [hRk]
  exact ⟨rfl, rfl, rfl, rfl, rfl, hpSt2⟩

private theorem proveConstraints_rel (airs : Array Spec.Bus.AirTable)
    (cols : Array (Array K)) (zeta : Array E)
    (pM : Model.Bus.ProverState) (pS : Spec.Bus.ProverState) (hp : psRel pM pS) :
    (Model.Bus.proveConstraints airs cols zeta pM).1 =
      (Spec.Bus.proveConstraints airs cols zeta pS).1 ∧
    psRel (Model.Bus.proveConstraints airs cols zeta pM).2
      (Spec.Bus.proveConstraints airs cols zeta pS).2 := by
  unfold Model.Bus.proveConstraints Spec.Bus.proveConstraints
  simp only [Model.Bus.buildGroupedForm, Model.Bus.emptyBusForm, eqTable_eq_spec,
    eadd_eq_spec, mleEval_eq_spec]
  let n := foldRange airs.size
    (fun acc t => max acc (airs[t]?.map Spec.Bus.AirTable.tau |>.getD 0)) 0
  let gForms := foldRange airs.size
    (fun acc t => acc.push (Spec.Bus.buildGroupedForm
      (airs[t]?.map Spec.Bus.AirTable.form |>.getD (Spec.Bus.emptyBusForm 0))))
    (Array.emptyWithCapacity airs.size)
  let eqr0 := Spec.Bus.eqTable (zeta.extract 0 (n - 1))
  let chi0 := Array.replicate n zero
  let claim0 := foldRange airs.size
    (fun acc t => Spec.Field.eadd acc (airs[t]?.map Spec.Bus.AirTable.sigma |>.getD zero)) zero
  let weights0 := Array.replicate airs.size one
  let states0 : Array (Option (Array (Array E))) := Array.replicate airs.size none
  have hR := constraintsRoundsFold_rel airs gForms cols zeta n eqr0 chi0 claim0
    weights0 states0 pM pS hp
  rcases hMR : Model.Bus.constraintsRoundsFold airs gForms cols zeta n eqr0 chi0 claim0
    weights0 states0 pM with ⟨eqrM, chiM, kM, clM, wsM, stM⟩
  rcases hSR : Spec.Bus.constraintsRoundsFold airs gForms cols zeta n eqr0 chi0 claim0
    weights0 states0 pS with ⟨eqrS, chiS, kS, clS, wsS, stS⟩
  rw [hMR, hSR] at hR
  rcases hR with ⟨_, rfl, _, _, _, hpAfter⟩
  dsimp only [] at hpAfter ⊢
  refine foldRange_rel
    (fun (x : Array Spec.Bus.TableClaims × Model.Bus.ProverState)
         (y : Array Spec.Bus.TableClaims × Spec.Bus.ProverState) =>
      x.1 = y.1 ∧ psRel x.2 y.2)
    _ _ ?_ airs.size _ _ ⟨rfl, hpAfter⟩
  rintro ⟨cM, qM⟩ ⟨cS, qS⟩ t ⟨rfl, hpQ⟩
  dsimp only []
  exact ⟨rfl, psRel_addScalars hpQ _⟩


theorem bindPiClaims_refines_spec (rPi : E) (logMem : Nat) (publicInput : Array E) :
    Model.Bus.bindPiClaims rPi logMem publicInput =
      Spec.Bus.bindPiClaims rPi logMem publicInput := by
  simp only [Model.Bus.bindPiClaims, Spec.Bus.bindPiClaims, interpK_eq_spec]

theorem finishClaims_refines_spec (lay : Model.Layout.PublicLayout) (publicInput : Array E)
    (busClaims : Array Spec.Bus.ColumnClaim) (tableClaims : Array Spec.Bus.TableClaims)
    (rPi : E) :
    Model.Bus.finishClaims lay publicInput busClaims tableClaims rPi =
      Spec.Bus.finishClaims lay publicInput busClaims tableClaims rPi := by
  simp only [Model.Bus.finishClaims, Spec.Bus.finishClaims,
    bindPiClaims_refines_spec, Model.Bus.routeSlotClaims]
  rfl

theorem proveBusAndConstraints_refines_spec (program : Array Spec.Vm.Op) (iv : ByteArray)
    (publicInput : Array E) (bundle : WitnessBundle) :
    (Model.Bus.proveBusAndConstraints program iv publicInput bundle).toSpec =
      Spec.Bus.proveBusAndConstraints program iv publicInput bundle := by
  unfold Model.Bus.proveBusAndConstraints Spec.Bus.proveBusAndConstraints
    Model.Bus.BusStageOutput.toSpec
  rcases startTranscript_refines_spec iv publicInput bundle.sized bundle.root with ⟨hs0, hp0⟩
  have hpRel0 : psRel (Model.Bus.startTranscript iv publicInput bundle.sized bundle.root)
      (Spec.Bus.startTranscript iv publicInput bundle.sized bundle.root) := ⟨hp0, hs0⟩
  simp only [buildColumns_refines_spec, Proofs.Layout.bytecodeColumnsFast_refines_spec,
    Model.Bus.keccakOutputClaim]
  let cols := Spec.Bus.buildColumns program bundle.sized bundle.message
  let bcCols := bytecodeColumns program
  let lim := Model.Bus.maxBusGpowIndex program bundle.sized
  have hBal := proveBalance_rel lim bundle.sized.layout cols bcCols
    (Model.Bus.startTranscript iv publicInput bundle.sized bundle.root)
    (Spec.Bus.startTranscript iv publicInput bundle.sized bundle.root) hpRel0
  cases hMBal : Model.Bus.proveBalance (Model.Layout.gpowTable lim) bundle.sized.layout
    cols bcCols (Model.Bus.startTranscript iv publicInput bundle.sized bundle.root) with
  | mk busM ps1M =>
  cases hSBal : Spec.Bus.proveBalance bundle.sized.layout cols bcCols
    (Spec.Bus.startTranscript iv publicInput bundle.sized bundle.root) with
  | mk busS ps1S =>
  rw [hMBal, hSBal] at hBal
  rcases hBal with ⟨rfl, hpRel1⟩
  dsimp only [] at hpRel1 ⊢
  have hXi := psRel_sampleChallenge hpRel1
  cases hMXi : Model.Bus.sampleChallenge ps1M with
  | mk xiM ps2M =>
  cases hSXi : Spec.Bus.sampleChallenge ps1S with
  | mk xiS ps2S =>
  rw [hMXi, hSXi] at hXi
  rcases hXi with ⟨rfl, hpRel2⟩
  dsimp only [] at hpRel2 ⊢
  simp only [buildAirs_refines_spec]
  let airs := Spec.Bus.buildAirs bundle.sized.layout.taus busM xiM
  have hCon := proveConstraints_rel airs cols busM.point ps2M ps2S hpRel2
  cases hMCon : Model.Bus.proveConstraints airs cols busM.point ps2M with
  | mk tcM ps3M =>
  cases hSCon : Spec.Bus.proveConstraints airs cols busM.point ps2S with
  | mk tcS ps3S =>
  rw [hMCon, hSCon] at hCon
  rcases hCon with ⟨rfl, hpRel3⟩
  dsimp only [] at hpRel3 ⊢
  have hRpi := psRel_sampleChallenge hpRel3
  cases hMRpi : Model.Bus.sampleChallenge ps3M with
  | mk rPiM ps4M =>
  cases hSRpi : Spec.Bus.sampleChallenge ps3S with
  | mk rPiS ps4S =>
  rw [hMRpi, hSRpi] at hRpi
  rcases hRpi with ⟨rfl, _, hs4⟩
  dsimp only [] at hs4 ⊢
  simp only [finishClaims_refines_spec, hs4]

end LeanVmXmss.Proofs.Bus
