import Model.KeccakGkr.Scalar
import Proofs.Bus.Refinement

namespace LeanVmXmss.Proofs.KeccakGkr

open Spec.Field (K E zero one)
open Model.Pcs.Ntt (foldRange foldRangeLoop)

set_option maxRecDepth 20000
set_option maxHeartbeats 800000

private theorem eadd_eq_spec : Model.Field.eadd = Spec.Field.eadd := rfl

theorem dot_refines_spec (a b : Array E) :
    Model.KeccakGkr.dot a b = Spec.KeccakGkr.dot a b := by
  simp only [Model.KeccakGkr.dot, Spec.KeccakGkr.dot,
    Proofs.Bus.nativeKaratsuba_eq_emul, eadd_eq_spec]

theorem eqTable_refines_spec (point : Array E) :
    Model.KeccakGkr.eqTable point = Spec.KeccakGkr.eqTable point := by
  simp only [Model.KeccakGkr.eqTable, Spec.KeccakGkr.eqTable, Proofs.Bus.eqTable_eq_spec]

theorem polyEval_refines_spec (coeffs : Array E) (point : E) :
    Model.KeccakGkr.polyEval coeffs point = Spec.KeccakGkr.polyEval coeffs point := by
  simp only [Model.KeccakGkr.polyEval, Spec.KeccakGkr.polyEval, Proofs.Bus.polyEval_eq_spec]

theorem powersOf_refines_spec (seed : E) (count : Nat) :
    Model.KeccakGkr.powersOf seed count = Spec.KeccakGkr.powersOf seed count := by
  simp only [Model.KeccakGkr.powersOf, Spec.KeccakGkr.powersOf, Proofs.Bus.nativeKaratsuba_eq_emul]

theorem instanceWeights_refines_spec (seed : E) :
    Model.KeccakGkr.instanceWeights seed = Spec.KeccakGkr.instanceWeights seed := by
  simp only [Model.KeccakGkr.instanceWeights, Spec.KeccakGkr.instanceWeights,
    powersOf_refines_spec, eadd_eq_spec]

theorem productAt_refines_spec (masks : Array (Array (Array UInt64))) (layer : Nat)
    (eqs weights : Array E) :
    Model.KeccakGkr.productAt masks layer eqs weights =
      Spec.KeccakGkr.productAt masks layer eqs weights := by
  simp only [Model.KeccakGkr.productAt, Spec.KeccakGkr.productAt,
    Proofs.Bus.nativeKaratsuba_eq_emul, eadd_eq_spec]

theorem roundCoefficients_refines_spec (scale zeroV infinity value here : E) :
    Model.KeccakGkr.roundCoefficients scale zeroV infinity value here =
      Spec.KeccakGkr.roundCoefficients scale zeroV infinity value here := by
  simp only [Model.KeccakGkr.roundCoefficients, Spec.KeccakGkr.roundCoefficients,
    Proofs.Bus.nativeKaratsuba_eq_emul, Proofs.Bus.nativeEinv_eq_einv, eadd_eq_spec]

theorem pairSums_refines_spec (rows : Array (Array E)) (claimWeights eqs : Array E) (kappa : E) :
    Model.KeccakGkr.pairSums rows claimWeights eqs kappa =
      Spec.KeccakGkr.pairSums rows claimWeights eqs kappa := by
  simp only [Model.KeccakGkr.pairSums, Spec.KeccakGkr.pairSums,
    Proofs.Bus.nativeKaratsuba_eq_emul, eadd_eq_spec]

theorem foldRows_refines_spec (rows : Array (Array E)) (challenge : E) :
    Model.KeccakGkr.foldRows rows challenge = Spec.KeccakGkr.foldRows rows challenge := by
  simp only [Model.KeccakGkr.foldRows, Spec.KeccakGkr.foldRows,
    Proofs.Bus.nativeKaratsuba_eq_emul, eadd_eq_spec]

theorem initialTable_refines_spec (masks : Array (Array (Array UInt64))) (layer : Nat) (mu : Array E) :
    Model.KeccakGkr.initialTable masks layer mu = Spec.KeccakGkr.initialTable masks layer mu := rfl

theorem localRound_refines_spec (w a b c : Array E) (kappa scale : E) :
    Model.KeccakGkr.localRound w a b c kappa scale =
      Spec.KeccakGkr.localRound w a b c kappa scale := by
  simp only [Model.KeccakGkr.localRound, Spec.KeccakGkr.localRound,
    Proofs.Bus.nativeKaratsuba_eq_emul, eadd_eq_spec]

theorem fold1_refines_spec (table : Array E) (challenge : E) :
    Model.KeccakGkr.fold1 table challenge = Spec.KeccakGkr.fold1 table challenge := by
  simp only [Model.KeccakGkr.fold1, Spec.KeccakGkr.fold1,
    Proofs.Bus.nativeKaratsuba_eq_emul, eadd_eq_spec]

theorem slotWeights_refines_spec (claim : Spec.KeccakGkr.GkrClaim) (first count : Nat) :
    Model.KeccakGkr.slotWeights claim first count = Spec.KeccakGkr.slotWeights claim first count := by
  simp only [Model.KeccakGkr.slotWeights, Spec.KeccakGkr.slotWeights,
    eqTable_refines_spec, Proofs.Bus.nativeKaratsuba_eq_emul]

theorem roundValues_refines_spec (a b : Array E) (width : Nat) :
    Model.KeccakGkr.roundValues a b width = Spec.KeccakGkr.roundValues a b width := by
  simp only [Model.KeccakGkr.roundValues, Spec.KeccakGkr.roundValues,
    Proofs.Bus.nativeKaratsuba_eq_emul, eadd_eq_spec]

theorem foldWidth_refines_spec (table : Array E) (width : Nat) (challenge : E) :
    Model.KeccakGkr.foldWidth table width challenge = Spec.KeccakGkr.foldWidth table width challenge := by
  simp only [Model.KeccakGkr.foldWidth, Spec.KeccakGkr.foldWidth,
    Proofs.Bus.nativeKaratsuba_eq_emul, eadd_eq_spec]

theorem outputWords_refines_spec (committed : Array K) (width : Nat) (inst : Array E) :
    Model.KeccakGkr.outputWords committed width inst = Spec.KeccakGkr.outputWords committed width inst := by
  simp only [Model.KeccakGkr.outputWords, Spec.KeccakGkr.outputWords,
    eqTable_refines_spec, Proofs.Bus.nativeMulBase_eq_mulBase, eadd_eq_spec]

theorem wordWeights_refines_spec (claim : Spec.KeccakGkr.GkrClaim) :
    Model.KeccakGkr.wordWeights claim = Spec.KeccakGkr.wordWeights claim := by
  simp only [Model.KeccakGkr.wordWeights, Spec.KeccakGkr.wordWeights, slotWeights_refines_spec]

theorem packEval_refines_spec (committed : Array K) (width : Nat) (pack : Array E) :
    Model.KeccakGkr.packEval committed width pack = Spec.KeccakGkr.packEval committed width pack := by
  simp only [Model.KeccakGkr.packEval, Spec.KeccakGkr.packEval, eqTable_refines_spec, eadd_eq_spec]

theorem perInstance_refines_spec (folded weights : Array E) :
    Model.KeccakGkr.perInstance folded weights = Spec.KeccakGkr.perInstance folded weights := by
  simp only [Model.KeccakGkr.perInstance, Spec.KeccakGkr.perInstance, dot_refines_spec, eadd_eq_spec]

theorem atInstance_refines_spec (folded low : Array E) :
    Model.KeccakGkr.atInstance folded low = Spec.KeccakGkr.atInstance folded low := by
  simp only [Model.KeccakGkr.atInstance, Spec.KeccakGkr.atInstance,
    eqTable_refines_spec, Proofs.Bus.nativeKaratsuba_eq_emul, eadd_eq_spec]

private def psRel (m : Model.Bus.ProverState) (s : Spec.Bus.ProverState) : Prop :=
  m.sponge.pending ≤ 4 ∧ m.toSpec = s

private theorem sponge_observe_pending (s : Model.Transcript.Registers.Sponge) (x : E) :
    (Model.Transcript.Registers.observe s x).pending ≤ 4 := by
  unfold Model.Transcript.Registers.observe Model.Transcript.Registers.absorb
  by_cases h4 : s.pending = 4
  · simp only [h4, ite_true, Proofs.Transcript.Registers.duplex_pending]; omega
  · simp only [h4, ite_false]
    match hp : s.pending with
    | 0 => simp only []; omega
    | 1 => simp only []; omega
    | 2 => simp only []; omega
    | _ + 3 => simp only []; omega

private theorem sponge_sample_pending (s : Model.Transcript.Registers.Sponge) :
    (Model.Transcript.Registers.sample s).2.pending ≤ 4 := by
  change (Model.Transcript.Registers.duplex s).2.pending ≤ 4
  rw [Proofs.Transcript.Registers.duplex_pending]; omega

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
    ((Model.Bus.sampleChallenge ps).1, (Model.Bus.sampleChallenge ps).2.toSpec) =
      Spec.Bus.sampleChallenge ps.toSpec := by
  rcases ps with ⟨sponge, stream⟩
  unfold Model.Bus.sampleChallenge Spec.Bus.sampleChallenge Model.Bus.ProverState.toSpec
  have hs := Proofs.Transcript.Registers.sample_refines sponge
  have h1 := congrArg Prod.fst hs
  have h2 := congrArg Prod.snd hs
  dsimp at h1 h2
  change (Model.Transcript.Registers.sample sponge).fst =
      (Spec.Transcript.challenge (Model.Transcript.Registers.toSpec sponge)).fst at h1
  change Model.Transcript.Registers.toSpec (Model.Transcript.Registers.sample sponge).snd =
      (Spec.Transcript.challenge (Model.Transcript.Registers.toSpec sponge)).snd at h2
  dsimp only []
  rw [h1, h2]

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

private def foldN {α : Type} (n : Nat) (f : α → Nat → α) (init : α) : α :=
  foldRange n f init

private theorem foldRange_rel {α β : Type} (R : α → β → Prop)
    (f : α → Nat → α) (g : β → Nat → β)
    (hstep : ∀ a b i, R a b → R (f a i) (g b i))
    (n : Nat) (a : α) (b : β) (h0 : R a b) :
    R (foldN n f a) (foldN n g b) := by
  unfold foldN
  unfold foldRange
  suffices h : ∀ rem idx a b, R a b → R (foldRangeLoop f rem idx a) (foldRangeLoop g rem idx b) from
    h n 0 a b h0
  intro rem
  induction rem with
  | zero => intro _ a b hab; exact hab
  | succ rem ih =>
    intro idx a b hab
    rw [Proofs.Pcs.foldRangeLoop_succ, Proofs.Pcs.foldRangeLoop_succ]
    exact ih (idx + 1) (f a idx) (g b idx) (hstep a b idx hab)

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
  dsimp only []
  have hsc := psRel_sampleChallenge hp
  cases hm : Model.Bus.sampleChallenge pM with
  | mk chM nextM =>
  cases hs : Spec.Bus.sampleChallenge pS with
  | mk chS nextS =>
  rw [hm, hs] at hsc
  rcases hsc with ⟨rfl, hps⟩
  exact ⟨rfl, hps⟩

private theorem psRel_addRoundPoly {m : Model.Bus.ProverState} {s : Spec.Bus.ProverState}
    (h : psRel m s) (coeffs : Array E) (equality : Bool) :
    psRel (Model.KeccakGkr.addRoundPoly m coeffs equality)
      (Spec.KeccakGkr.addRoundPoly s coeffs equality) := by
  unfold Model.KeccakGkr.addRoundPoly Spec.KeccakGkr.addRoundPoly
  refine foldRange_rel psRel _ _ ?_ coeffs.size m s h
  intro a b i hab
  by_cases hskip : i = (if equality then 0 else 1)
  · simp only [hskip, ite_true]; exact hab
  · simp only [hskip, ite_false]; exact psRel_addScalar hab (coeffs[i]?.getD zero)

private theorem proveRounds_rel (a b : Array E) (width : Nat) (scale value : E)
    {m : Model.Bus.ProverState} {s : Spec.Bus.ProverState} (h : psRel m s) :
    let rm := Model.KeccakGkr.proveRounds m a b width scale value
    let rs := Spec.KeccakGkr.proveRounds s a b width scale value
    rm.1 = rs.1 ∧ rm.2.1 = rs.2.1 ∧ rm.2.2.1 = rs.2.2.1 ∧ rm.2.2.2.1 = rs.2.2.2.1 ∧
      psRel rm.2.2.2.2 rs.2.2.2.2 := by
  dsimp only []
  unfold Model.KeccakGkr.proveRounds Spec.KeccakGkr.proveRounds
  simp only [roundValues_refines_spec, foldWidth_refines_spec, polyEval_refines_spec,
    Proofs.Bus.nativeKaratsuba_eq_emul, eadd_eq_spec]
  refine foldRange_rel
    (fun (rm : Array E × Array E × Array E × E × Model.Bus.ProverState)
         (rs : Array E × Array E × Array E × E × Spec.Bus.ProverState) =>
      rm.1 = rs.1 ∧ rm.2.1 = rs.2.1 ∧ rm.2.2.1 = rs.2.2.1 ∧
        rm.2.2.2.1 = rs.2.2.2.1 ∧ psRel rm.2.2.2.2 rs.2.2.2.2)
    _ _ ?_ _ _ _ ⟨rfl, rfl, rfl, rfl, h⟩
  rintro ⟨pM, lM, rM, vM, cM⟩ ⟨pS, lS, rS, vS, cS⟩ _ ⟨rfl, rfl, rfl, rfl, hc⟩
  dsimp only []
  let coeffs := #[Spec.Field.emul scale (Spec.KeccakGkr.roundValues lM rM width).1,
    Spec.Field.eadd vM (Spec.Field.emul scale (Spec.KeccakGkr.roundValues lM rM width).2),
    Spec.Field.emul scale (Spec.KeccakGkr.roundValues lM rM width).2]
  have hsc := psRel_sampleChallenge (psRel_addRoundPoly hc coeffs false)
  cases hm : Model.Bus.sampleChallenge (Model.KeccakGkr.addRoundPoly cM coeffs false) with
  | mk chM nextM =>
  cases hs : Spec.Bus.sampleChallenge (Spec.KeccakGkr.addRoundPoly cS coeffs false) with
  | mk chS nextS =>
  rw [hm, hs] at hsc
  rcases hsc with ⟨rfl, hnext⟩
  exact ⟨rfl, rfl, rfl, rfl, hnext⟩

private theorem proveLayer_bound_rel (claim : Spec.KeccakGkr.GkrClaim) (kappa value0 : E)
    (table0 : Array (Array E))
    {s1M : Model.Bus.ProverState} {s1S : Spec.Bus.ProverState} (hs1 : psRel s1M s1S) :
    let bm := foldRange claim.point.size
      (fun (acc : Array E × E × E × Model.Bus.ProverState × Array (Array E)) index =>
        let point := acc.1; let value := acc.2.1; let scale := acc.2.2.1
        let current := acc.2.2.2.1; let table := acc.2.2.2.2
        let here := claim.point[index]?.getD zero
        let later := Spec.KeccakGkr.eqTable (claim.point.extract (index + 1) claim.point.size)
        let pair := Spec.KeccakGkr.pairSums table claim.weights later kappa
        let coeffs := Spec.KeccakGkr.roundCoefficients scale pair.1 pair.2 value here
        let written := Model.KeccakGkr.addRoundPoly current coeffs true
        let (challenge, next) := Model.Bus.sampleChallenge written
        let grown := Spec.Field.eadd (Spec.Field.eadd one here) challenge
        (point.push challenge, Spec.Field.emul grown (Spec.KeccakGkr.polyEval coeffs challenge),
          Spec.Field.emul scale grown, next, Spec.KeccakGkr.foldRows table challenge))
      (Array.emptyWithCapacity claim.point.size, value0, one, s1M, table0)
    let bs := foldRange claim.point.size
      (fun (acc : Array E × E × E × Spec.Bus.ProverState × Array (Array E)) index =>
        let point := acc.1; let value := acc.2.1; let scale := acc.2.2.1
        let current := acc.2.2.2.1; let table := acc.2.2.2.2
        let here := claim.point[index]?.getD zero
        let later := Spec.KeccakGkr.eqTable (claim.point.extract (index + 1) claim.point.size)
        let pair := Spec.KeccakGkr.pairSums table claim.weights later kappa
        let coeffs := Spec.KeccakGkr.roundCoefficients scale pair.1 pair.2 value here
        let written := Spec.KeccakGkr.addRoundPoly current coeffs true
        let (challenge, next) := Spec.Bus.sampleChallenge written
        let grown := Spec.Field.eadd (Spec.Field.eadd one here) challenge
        (point.push challenge, Spec.Field.emul grown (Spec.KeccakGkr.polyEval coeffs challenge),
          Spec.Field.emul scale grown, next, Spec.KeccakGkr.foldRows table challenge))
      (Array.emptyWithCapacity claim.point.size, value0, one, s1S, table0)
    bm.1 = bs.1 ∧ bm.2.1 = bs.2.1 ∧ bm.2.2.1 = bs.2.2.1 ∧
      psRel bm.2.2.2.1 bs.2.2.2.1 ∧ bm.2.2.2.2 = bs.2.2.2.2 := by
  dsimp only []
  refine foldRange_rel
    (fun (bm : Array E × E × E × Model.Bus.ProverState × Array (Array E))
         (bs : Array E × E × E × Spec.Bus.ProverState × Array (Array E)) =>
      bm.1 = bs.1 ∧ bm.2.1 = bs.2.1 ∧ bm.2.2.1 = bs.2.2.1 ∧
        psRel bm.2.2.2.1 bs.2.2.2.1 ∧ bm.2.2.2.2 = bs.2.2.2.2)
    _ _ ?_ claim.point.size _ _ ⟨rfl, rfl, rfl, hs1, rfl⟩
  rintro ⟨pM, vM, scM, curM, tM⟩ ⟨pS, vS, scS, curS, tS⟩ index ⟨rfl, rfl, rfl, hcur, rfl⟩
  dsimp only []
  let here := claim.point[index]?.getD zero
  let later := Spec.KeccakGkr.eqTable (claim.point.extract (index + 1) claim.point.size)
  let pair := Spec.KeccakGkr.pairSums tM claim.weights later kappa
  let coeffs := Spec.KeccakGkr.roundCoefficients scM pair.1 pair.2 vM here
  have hsc := psRel_sampleChallenge (psRel_addRoundPoly hcur coeffs true)
  cases hm : Model.Bus.sampleChallenge (Model.KeccakGkr.addRoundPoly curM coeffs true) with
  | mk chM nextM =>
  cases hs : Spec.Bus.sampleChallenge (Spec.KeccakGkr.addRoundPoly curS coeffs true) with
  | mk chS nextS =>
  rw [hm, hs] at hsc
  rcases hsc with ⟨rfl, hnext⟩
  exact ⟨rfl, rfl, rfl, hnext, rfl⟩

private theorem proveLayer_local_rel (bits : Nat) (w0 a0 b0 c0 : Array E) (kappa scale : E)
    {curM : Model.Bus.ProverState} {curS : Spec.Bus.ProverState} (hcur : psRel curM curS) :
    let lm := foldRange bits
      (fun (acc : Array E × Array E × Array E × Array E × Array E × Model.Bus.ProverState) _ =>
        let lp := acc.1; let w := acc.2.1; let a := acc.2.2.1
        let b := acc.2.2.2.1; let c := acc.2.2.2.2.1; let cur := acc.2.2.2.2.2
        let coeffs := Spec.KeccakGkr.localRound w a b c kappa scale
        let written := Model.KeccakGkr.addRoundPoly cur coeffs false
        let (challenge, next) := Model.Bus.sampleChallenge written
        (lp.push challenge, Spec.KeccakGkr.fold1 w challenge,
          Spec.KeccakGkr.fold1 a challenge, Spec.KeccakGkr.fold1 b challenge,
          Spec.KeccakGkr.fold1 c challenge, next))
      (Array.emptyWithCapacity bits, w0, a0, b0, c0, curM)
    let ls := foldRange bits
      (fun (acc : Array E × Array E × Array E × Array E × Array E × Spec.Bus.ProverState) _ =>
        let lp := acc.1; let w := acc.2.1; let a := acc.2.2.1
        let b := acc.2.2.2.1; let c := acc.2.2.2.2.1; let cur := acc.2.2.2.2.2
        let coeffs := Spec.KeccakGkr.localRound w a b c kappa scale
        let written := Spec.KeccakGkr.addRoundPoly cur coeffs false
        let (challenge, next) := Spec.Bus.sampleChallenge written
        (lp.push challenge, Spec.KeccakGkr.fold1 w challenge,
          Spec.KeccakGkr.fold1 a challenge, Spec.KeccakGkr.fold1 b challenge,
          Spec.KeccakGkr.fold1 c challenge, next))
      (Array.emptyWithCapacity bits, w0, a0, b0, c0, curS)
    lm.1 = ls.1 ∧ lm.2.1 = ls.2.1 ∧ lm.2.2.1 = ls.2.2.1 ∧
      lm.2.2.2.1 = ls.2.2.2.1 ∧ lm.2.2.2.2.1 = ls.2.2.2.2.1 ∧
      psRel lm.2.2.2.2.2 ls.2.2.2.2.2 := by
  dsimp only []
  refine foldRange_rel
    (fun (lm : Array E × Array E × Array E × Array E × Array E × Model.Bus.ProverState)
         (ls : Array E × Array E × Array E × Array E × Array E × Spec.Bus.ProverState) =>
      lm.1 = ls.1 ∧ lm.2.1 = ls.2.1 ∧ lm.2.2.1 = ls.2.2.1 ∧
        lm.2.2.2.1 = ls.2.2.2.1 ∧ lm.2.2.2.2.1 = ls.2.2.2.2.1 ∧
        psRel lm.2.2.2.2.2 ls.2.2.2.2.2)
    _ _ ?_ bits _ _ ⟨rfl, rfl, rfl, rfl, rfl, hcur⟩
  rintro ⟨lpM, wM, aM, bM, cM, qM⟩ ⟨lpS, wS, aS, bS, cS, qS⟩ _ ⟨rfl, rfl, rfl, rfl, rfl, hq⟩
  dsimp only []
  let coeffs := Spec.KeccakGkr.localRound wM aM bM cM kappa scale
  have hsc := psRel_sampleChallenge (psRel_addRoundPoly hq coeffs false)
  cases hm : Model.Bus.sampleChallenge (Model.KeccakGkr.addRoundPoly qM coeffs false) with
  | mk chM nextM =>
  cases hs : Spec.Bus.sampleChallenge (Spec.KeccakGkr.addRoundPoly qS coeffs false) with
  | mk chS nextS =>
  rw [hm, hs] at hsc
  rcases hsc with ⟨rfl, hnext⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, hnext⟩

private theorem proveLayer_rel (masks : Array (Array (Array UInt64))) (layer : Nat)
    (claim : Spec.KeccakGkr.GkrClaim)
    {m : Model.Bus.ProverState} {s : Spec.Bus.ProverState} (h : psRel m s) :
    (Model.KeccakGkr.proveLayer m masks layer claim).1 =
      (Spec.KeccakGkr.proveLayer s masks layer claim).1 ∧
      psRel (Model.KeccakGkr.proveLayer m masks layer claim).2
        (Spec.KeccakGkr.proveLayer s masks layer claim).2 := by
  unfold Model.KeccakGkr.proveLayer Spec.KeccakGkr.proveLayer
  simp only [productAt_refines_spec, eqTable_refines_spec, instanceWeights_refines_spec,
    polyEval_refines_spec, initialTable_refines_spec, roundCoefficients_refines_spec,
    pairSums_refines_spec, foldRows_refines_spec, localRound_refines_spec, fold1_refines_spec,
    Model.KeccakGkr.sumSlice, Model.KeccakGkr.linearTranspose,
    Proofs.Bus.nativeKaratsuba_eq_emul, eadd_eq_spec]
  let product := Spec.KeccakGkr.productAt masks layer
    (Spec.KeccakGkr.eqTable claim.point) claim.weights
  have hseed := psRel_sampleChallenge (psRel_addScalars h product)
  cases hm0 : Model.Bus.sampleChallenge (Model.Bus.addScalars m product) with
  | mk seedM s1M =>
  cases hs0 : Spec.Bus.sampleChallenge (Spec.Bus.addScalars s product) with
  | mk seedS s1S =>
  rw [hm0, hs0] at hseed
  rcases hseed with ⟨rfl, hs1⟩
  dsimp only []
  let mu := Spec.KeccakGkr.instanceWeights seedM
  let kappa := Spec.KeccakGkr.sumSlice mu
  let value0 := Spec.KeccakGkr.polyEval product seedM
  let table0 := Spec.KeccakGkr.initialTable masks layer mu
  have hb := proveLayer_bound_rel claim kappa value0 table0 hs1
  rcases hbm : foldRange claim.point.size
    (fun (acc : Array E × E × E × Model.Bus.ProverState × Array (Array E)) index =>
      let point := acc.1; let value := acc.2.1; let scale := acc.2.2.1
      let current := acc.2.2.2.1; let table := acc.2.2.2.2
      let here := claim.point[index]?.getD zero
      let later := Spec.KeccakGkr.eqTable (claim.point.extract (index + 1) claim.point.size)
      let pair := Spec.KeccakGkr.pairSums table claim.weights later kappa
      let coeffs := Spec.KeccakGkr.roundCoefficients scale pair.1 pair.2 value here
      let written := Model.KeccakGkr.addRoundPoly current coeffs true
      let (challenge, next) := Model.Bus.sampleChallenge written
      let grown := Spec.Field.eadd (Spec.Field.eadd one here) challenge
      (point.push challenge, Spec.Field.emul grown (Spec.KeccakGkr.polyEval coeffs challenge),
        Spec.Field.emul scale grown, next, Spec.KeccakGkr.foldRows table challenge))
    (Array.emptyWithCapacity claim.point.size, value0, one, s1M, table0) with
    ⟨ptM, valM, scM, curM, tabM⟩
  rcases hbs : foldRange claim.point.size
    (fun (acc : Array E × E × E × Spec.Bus.ProverState × Array (Array E)) index =>
      let point := acc.1; let value := acc.2.1; let scale := acc.2.2.1
      let current := acc.2.2.2.1; let table := acc.2.2.2.2
      let here := claim.point[index]?.getD zero
      let later := Spec.KeccakGkr.eqTable (claim.point.extract (index + 1) claim.point.size)
      let pair := Spec.KeccakGkr.pairSums table claim.weights later kappa
      let coeffs := Spec.KeccakGkr.roundCoefficients scale pair.1 pair.2 value here
      let written := Spec.KeccakGkr.addRoundPoly current coeffs true
      let (challenge, next) := Spec.Bus.sampleChallenge written
      let grown := Spec.Field.eadd (Spec.Field.eadd one here) challenge
      (point.push challenge, Spec.Field.emul grown (Spec.KeccakGkr.polyEval coeffs challenge),
        Spec.Field.emul scale grown, next, Spec.KeccakGkr.foldRows table challenge))
    (Array.emptyWithCapacity claim.point.size, value0, one, s1S, table0) with
    ⟨ptS, valS, scS, curS, tabS⟩
  dsimp only [] at hb
  rw [hbm, hbs] at hb
  rcases hb with ⟨rfl, _, rfl, hcur, rfl⟩
  dsimp only []
  let cube := 1 <<< Spec.KeccakGkr.localBits
  let table := tabM[0]?.getD (Array.replicate Spec.KeccakGkr.bitCount zero)
  let shift (k : Nat) := (Array.range cube).map fun j =>
    if j < Spec.KeccakGkr.bitCount then table[Spec.KeccakGkr.along j k]?.getD zero else zero
  let w0 := claim.weights ++ Array.replicate (cube - claim.weights.size) zero
  let a0 := table ++ Array.replicate (cube - Spec.KeccakGkr.bitCount) zero
  have hl := proveLayer_local_rel Spec.KeccakGkr.localBits w0 a0 (shift 1) (shift 2) kappa scM hcur
  rcases hlm : foldRange Spec.KeccakGkr.localBits
    (fun (acc : Array E × Array E × Array E × Array E × Array E × Model.Bus.ProverState) _ =>
      let lp := acc.1; let w := acc.2.1; let a := acc.2.2.1
      let b := acc.2.2.2.1; let c := acc.2.2.2.2.1; let cur := acc.2.2.2.2.2
      let coeffs := Spec.KeccakGkr.localRound w a b c kappa scM
      let written := Model.KeccakGkr.addRoundPoly cur coeffs false
      let (challenge, next) := Model.Bus.sampleChallenge written
      (lp.push challenge, Spec.KeccakGkr.fold1 w challenge,
        Spec.KeccakGkr.fold1 a challenge, Spec.KeccakGkr.fold1 b challenge,
        Spec.KeccakGkr.fold1 c challenge, next))
    (Array.emptyWithCapacity Spec.KeccakGkr.localBits, w0, a0, shift 1, shift 2, curM) with
    ⟨lpM, fwM, faM, fbM, fcM, cur2M⟩
  rcases hls : foldRange Spec.KeccakGkr.localBits
    (fun (acc : Array E × Array E × Array E × Array E × Array E × Spec.Bus.ProverState) _ =>
      let lp := acc.1; let w := acc.2.1; let a := acc.2.2.1
      let b := acc.2.2.2.1; let c := acc.2.2.2.2.1; let cur := acc.2.2.2.2.2
      let coeffs := Spec.KeccakGkr.localRound w a b c kappa scM
      let written := Spec.KeccakGkr.addRoundPoly cur coeffs false
      let (challenge, next) := Spec.Bus.sampleChallenge written
      (lp.push challenge, Spec.KeccakGkr.fold1 w challenge,
        Spec.KeccakGkr.fold1 a challenge, Spec.KeccakGkr.fold1 b challenge,
        Spec.KeccakGkr.fold1 c challenge, next))
    (Array.emptyWithCapacity Spec.KeccakGkr.localBits, w0, a0, shift 1, shift 2, curS) with
    ⟨lpS, fwS, faS, fbS, fcS, cur2S⟩
  dsimp only [] at hl
  rw [hlm, hls] at hl
  rcases hl with ⟨rfl, _, rfl, rfl, rfl, hcur2⟩
  dsimp only []
  let t := #[faM[0]?.getD zero, fbM[0]?.getD zero, fcM[0]?.getD zero]
  have hbeta := psRel_sampleChallenge (psRel_addScalars hcur2 t)
  cases hbm2 : Model.Bus.sampleChallenge (Model.Bus.addScalars cur2M t) with
  | mk betaM doneM =>
  cases hbs2 : Spec.Bus.sampleChallenge (Spec.Bus.addScalars cur2S t) with
  | mk betaS doneS =>
  rw [hbm2, hbs2] at hbeta
  rcases hbeta with ⟨rfl, hdone⟩
  exact ⟨rfl, hdone⟩

private theorem openOutputs_rel (committed : Array K) (width : Nat) (inst : Array E)
    (claim : Spec.KeccakGkr.GkrClaim) (value : E)
    {m : Model.Bus.ProverState} {s : Spec.Bus.ProverState} (h : psRel m s) :
    (Model.KeccakGkr.openOutputs m committed width inst claim value).1 =
      (Spec.KeccakGkr.openOutputs s committed width inst claim value).1 ∧
      psRel (Model.KeccakGkr.openOutputs m committed width inst claim value).2
        (Spec.KeccakGkr.openOutputs s committed width inst claim value).2 := by
  unfold Model.KeccakGkr.openOutputs Spec.KeccakGkr.openOutputs
  simp only [outputWords_refines_spec, wordWeights_refines_spec]
  let words := Spec.KeccakGkr.outputWords committed width inst
  let ww := Spec.KeccakGkr.wordWeights claim
  have hr := proveRounds_rel words ww 1 one value h
  rcases hm : Model.KeccakGkr.proveRounds m words ww 1 one value with ⟨sM, lM, rM, vM, cM⟩
  rcases hs : Spec.KeccakGkr.proveRounds s words ww 1 one value with ⟨sS, lS, rS, vS, cS⟩
  dsimp only [] at hr
  rw [hm, hs] at hr
  rcases hr with ⟨rfl, rfl, _, _, h5⟩
  exact ⟨rfl, psRel_addScalar h5 _⟩

private theorem openInputs_body_rel (pack folded weights instances mu : Array E) (val0 : E)
    {m : Model.Bus.ProverState} {s : Spec.Bus.ProverState} (h : psRel m s) :
    let outM : Spec.KeccakGkr.Opening × Model.Bus.ProverState :=
      let bound := Model.KeccakGkr.proveRounds m instances mu 1 one val0
      let low := bound.1
      let mu0 := bound.2.2.1[0]?.getD zero
      let value := bound.2.2.2.1
      let current := bound.2.2.2.2
      let slices0 := Spec.KeccakGkr.atInstance folded low
      let slotBound := Model.KeccakGkr.proveRounds current slices0 weights Spec.KeccakGkr.wordBits mu0 value
      let slices := slotBound.2.1
      let written := Model.Bus.addScalars slotBound.2.2.2.2 slices
      (⟨low ++ pack ++ slotBound.1, slices⟩, written)
    let outS : Spec.KeccakGkr.Opening × Spec.Bus.ProverState :=
      let bound := Spec.KeccakGkr.proveRounds s instances mu 1 one val0
      let low := bound.1
      let mu0 := bound.2.2.1[0]?.getD zero
      let value := bound.2.2.2.1
      let current := bound.2.2.2.2
      let slices0 := Spec.KeccakGkr.atInstance folded low
      let slotBound := Spec.KeccakGkr.proveRounds current slices0 weights Spec.KeccakGkr.wordBits mu0 value
      let slices := slotBound.2.1
      let written := Spec.Bus.addScalars slotBound.2.2.2.2 slices
      (⟨low ++ pack ++ slotBound.1, slices⟩, written)
    outM.1 = outS.1 ∧ psRel outM.2 outS.2 := by
  dsimp only []
  have hr1 := proveRounds_rel instances mu 1 one val0 h
  rcases hm1 : Model.KeccakGkr.proveRounds m instances mu 1 one val0 with
    ⟨lowM, l1M, r1M, valM, curM⟩
  rcases hs1 : Spec.KeccakGkr.proveRounds s instances mu 1 one val0 with
    ⟨lowS, l1S, r1S, valS, curS⟩
  dsimp only [] at hr1
  rw [hm1, hs1] at hr1
  rcases hr1 with ⟨rfl, _, rfl, rfl, hcur⟩
  dsimp only []
  let slices0 := Spec.KeccakGkr.atInstance folded lowM
  let mu0 := r1M[0]?.getD zero
  have hr2 := proveRounds_rel slices0 weights Spec.KeccakGkr.wordBits mu0 valM hcur
  rcases hm2 : Model.KeccakGkr.proveRounds curM slices0 weights Spec.KeccakGkr.wordBits mu0 valM with
    ⟨slotM, slicesM, r2M, v2M, cur2M⟩
  rcases hs2 : Spec.KeccakGkr.proveRounds curS slices0 weights Spec.KeccakGkr.wordBits mu0 valM with
    ⟨slotS, slicesS, r2S, v2S, cur2S⟩
  dsimp only [] at hr2
  rw [hm2, hs2] at hr2
  rcases hr2 with ⟨rfl, rfl, _, _, hcur2⟩
  exact ⟨rfl, psRel_addScalars hcur2 _⟩

private theorem openInputs_rel (committed : Array K) (width : Nat) (claim : Spec.KeccakGkr.GkrClaim)
    {m : Model.Bus.ProverState} {s : Spec.Bus.ProverState} (h : psRel m s) :
    (Model.KeccakGkr.openInputs m committed width claim).1 =
      (Spec.KeccakGkr.openInputs s committed width claim).1 ∧
      psRel (Model.KeccakGkr.openInputs m committed width claim).2
        (Spec.KeccakGkr.openInputs s committed width claim).2 := by
  unfold Model.KeccakGkr.openInputs Spec.KeccakGkr.openInputs
  simp only [packEval_refines_spec, slotWeights_refines_spec, perInstance_refines_spec,
    atInstance_refines_spec]
  exact openInputs_body_rel _ _ _ _ _ _ h

attribute [irreducible] foldN

private theorem proveReduction_layers_rel (depth : Nat)
    (stepM : Spec.KeccakGkr.GkrClaim × Model.Bus.ProverState → Nat →
      Spec.KeccakGkr.GkrClaim × Model.Bus.ProverState)
    (stepS : Spec.KeccakGkr.GkrClaim × Spec.Bus.ProverState → Nat →
      Spec.KeccakGkr.GkrClaim × Spec.Bus.ProverState)
    (hstep : ∀ c qM qS layer, psRel qM qS →
      (stepM (c, qM) layer).1 = (stepS (c, qS) layer).1 ∧
        psRel (stepM (c, qM) layer).2 (stepS (c, qS) layer).2)
    (first : Spec.KeccakGkr.GkrClaim)
    {pM : Model.Bus.ProverState} {pS : Spec.Bus.ProverState} (hp : psRel pM pS) :
    (foldRange depth stepM (first, pM)).1 =
      (foldRange depth stepS (first, pS)).1 ∧
      psRel (foldRange depth stepM (first, pM)).2
        (foldRange depth stepS (first, pS)).2 := by
  have h := foldRange_rel
    (fun (x : Spec.KeccakGkr.GkrClaim × Model.Bus.ProverState)
         (y : Spec.KeccakGkr.GkrClaim × Spec.Bus.ProverState) =>
      x.1 = y.1 ∧ psRel x.2 y.2)
    stepM stepS
    (by
      intro a b layer hab
      rcases a with ⟨cM, qM⟩
      rcases b with ⟨cS, qS⟩
      rcases hab with ⟨rfl, hq⟩
      exact hstep cM qM qS layer hq)
    depth (first, pM) (first, pS) ⟨rfl, hp⟩
  unfold foldN at h
  exact h

private theorem openings_true_rel
    (committed : Array K) (width : Nat) (inst : Array E)
    (first : Spec.KeccakGkr.GkrClaim) (committedValue : E)
    (redM : Spec.KeccakGkr.GkrClaim × Model.Bus.ProverState)
    (redS : Spec.KeccakGkr.GkrClaim × Spec.Bus.ProverState)
    (hred : redM.1 = redS.1 ∧ psRel redM.2 redS.2) :
    (let openedOut := Model.KeccakGkr.openOutputs redM.2 committed width inst first committedValue
     let inputs := Model.KeccakGkr.openInputs openedOut.2 committed width redM.1
     Spec.KeccakGkr.Openings.mk (some openedOut.1) inputs.1) =
    (let openedOut := Spec.KeccakGkr.openOutputs redS.2 committed width inst first committedValue
     let inputs := Spec.KeccakGkr.openInputs openedOut.2 committed width redS.1
     Spec.KeccakGkr.Openings.mk (some openedOut.1) inputs.1) ∧
    psRel
      (let openedOut := Model.KeccakGkr.openOutputs redM.2 committed width inst first committedValue
       (Model.KeccakGkr.openInputs openedOut.2 committed width redM.1).2)
      (let openedOut := Spec.KeccakGkr.openOutputs redS.2 committed width inst first committedValue
       (Spec.KeccakGkr.openInputs openedOut.2 committed width redS.1).2) := by
  rcases redM with ⟨claimM, openedM⟩
  rcases redS with ⟨claimS, openedS⟩
  rcases hred with ⟨rfl, hopened⟩
  dsimp only []
  have hout := openOutputs_rel committed width inst first committedValue hopened
  cases hom : Model.KeccakGkr.openOutputs openedM committed width inst first committedValue with
  | mk outM afterOutM =>
  cases hos : Spec.KeccakGkr.openOutputs openedS committed width inst first committedValue with
  | mk outS afterOutS =>
  rw [hom, hos] at hout
  rcases hout with ⟨rfl, hafterOut⟩
  dsimp only []
  have hin := openInputs_rel committed width claimM hafterOut
  cases him : Model.KeccakGkr.openInputs afterOutM committed width claimM with
  | mk inM finM =>
  cases his : Spec.KeccakGkr.openInputs afterOutS committed width claimM with
  | mk inS finS =>
  rw [him, his] at hin
  rcases hin with ⟨rfl, hfin⟩
  exact ⟨rfl, hfin⟩

private theorem segments_gt_one : Spec.KeccakGkr.segments > 1 := by
  decide

private theorem proveReduction_rel (committed : Array K) (executed : Nat)
    (output : Spec.Bus.OutputClaim)
    {m : Model.Bus.ProverState} {s : Spec.Bus.ProverState} (h : psRel m s) :
    (Model.KeccakGkr.proveReduction m committed executed output).1 =
      (Spec.KeccakGkr.proveReduction s committed executed output).1 ∧
      psRel (Model.KeccakGkr.proveReduction m committed executed output).2
        (Spec.KeccakGkr.proveReduction s committed executed output).2 := by
  unfold Model.KeccakGkr.proveReduction Spec.KeccakGkr.proveReduction
  have hv1 := psRel_sampleVec h Spec.KeccakGkr.segLog
  cases hm1 : Model.Bus.sampleVec m Spec.KeccakGkr.segLog with
  | mk segM s1M =>
  cases hs1 : Spec.Bus.sampleVec s Spec.KeccakGkr.segLog with
  | mk segS s1S =>
  rw [hm1, hs1] at hv1
  rcases hv1 with ⟨rfl, hp1⟩
  dsimp only []
  have hv2 := psRel_sampleVec hp1 Spec.KeccakGkr.laneBits
  cases hm2 : Model.Bus.sampleVec s1M Spec.KeccakGkr.laneBits with
  | mk lanesM s2M =>
  cases hs2 : Spec.Bus.sampleVec s1S Spec.KeccakGkr.laneBits with
  | mk lanesS s2S =>
  rw [hm2, hs2] at hv2
  rcases hv2 with ⟨rfl, hp2⟩
  dsimp only []
  simp only [segments_gt_one, ite_true,
    eqTable_refines_spec, outputWords_refines_spec, wordWeights_refines_spec,
    dot_refines_spec, Proofs.Bus.nativeKaratsuba_eq_emul, eadd_eq_spec]
  generalize (1 <<< Spec.KeccakGkr.stepsLog executed) = width
  generalize Spec.KeccakGkr.buildRoundMasks committed width = masks
  generalize Spec.KeccakGkr.dot (Spec.KeccakGkr.outputWords committed width output.instancePoint)
    (Spec.KeccakGkr.wordWeights
      ⟨zero, Spec.KeccakGkr.eqTable (output.instancePoint.extract 0 Spec.KeccakGkr.packBits),
        output.instancePoint.extract Spec.KeccakGkr.packBits output.instancePoint.size ++ segM,
        (Array.range Spec.KeccakGkr.bitCount).map fun position =>
          Spec.Field.emul ((Spec.KeccakGkr.eqTable lanesM)[position / Spec.KeccakGkr.wordBits]?.getD zero)
            (Spec.Field.embed (UInt64.ofNat (1 <<< (position % Spec.KeccakGkr.wordBits))))⟩) = committedValue
  generalize (⟨Spec.Field.eadd committedValue
      (Spec.Field.emul ((Spec.KeccakGkr.eqTable segM)[Spec.KeccakGkr.segments - 1]?.getD zero)
        (Spec.KeccakGkr.dot ((Spec.KeccakGkr.eqTable lanesM).extract 0 Spec.Layout.stateLanes) output.lanes)),
      Spec.KeccakGkr.eqTable (output.instancePoint.extract 0 Spec.KeccakGkr.packBits),
      output.instancePoint.extract Spec.KeccakGkr.packBits output.instancePoint.size ++ segM,
      (Array.range Spec.KeccakGkr.bitCount).map fun position =>
        Spec.Field.emul ((Spec.KeccakGkr.eqTable lanesM)[position / Spec.KeccakGkr.wordBits]?.getD zero)
          (Spec.Field.embed (UInt64.ofNat (1 <<< (position % Spec.KeccakGkr.wordBits))))⟩ : Spec.KeccakGkr.GkrClaim) = first
  have hafter := psRel_addScalar hp2 committedValue
  let stepM := fun (acc : Spec.KeccakGkr.GkrClaim × Model.Bus.ProverState) layer =>
    let step := Model.KeccakGkr.proveLayer acc.2 masks layer acc.1
    (step.1, step.2)
  let stepS := fun (acc : Spec.KeccakGkr.GkrClaim × Spec.Bus.ProverState) layer =>
    let step := Spec.KeccakGkr.proveLayer acc.2 masks layer acc.1
    (step.1, step.2)
  have hstep : ∀ c qM qS layer, psRel qM qS →
      (stepM (c, qM) layer).1 = (stepS (c, qS) layer).1 ∧
        psRel (stepM (c, qM) layer).2 (stepS (c, qS) layer).2 := by
    intro c qM qS layer hq
    dsimp only [stepM, stepS]
    exact proveLayer_rel masks layer c hq
  have hred := proveReduction_layers_rel Spec.Layout.keccakDepth stepM stepS hstep first hafter
  exact openings_true_rel committed width output.instancePoint first committedValue _ _ hred

private theorem proveBusAndConstraints_pending (program : Array Spec.Vm.Op) (iv : ByteArray)
    (publicInput : Array E) (bundle : Spec.Witness.WitnessBundle) :
    (Model.Bus.proveBusAndConstraints program iv publicInput bundle).ps.sponge.pending ≤ 4 := by
  unfold Model.Bus.proveBusAndConstraints
  dsimp only []
  cases Model.Bus.proveBalance
      (Model.Layout.gpowTable (Model.Bus.maxBusGpowIndex program bundle.sized))
      bundle.sized.layout
      (Model.Bus.buildColumns program bundle.sized bundle.message)
      (Model.Layout.bytecodeColumnsFast program)
      (Model.Bus.startTranscript iv publicInput bundle.sized bundle.root) with
  | mk bus ps1 =>
  dsimp only []
  cases Model.Bus.sampleChallenge ps1 with
  | mk xi ps2 =>
  dsimp only []
  cases Model.Bus.proveConstraints
      (Model.Bus.buildAirs bundle.sized.layout.taus bus xi)
      (Model.Bus.buildColumns program bundle.sized bundle.message) bus.point ps2 with
  | mk tableClaims ps3 =>
  dsimp only []
  have hp := sampleChallenge_pending ps3
  cases hsc : Model.Bus.sampleChallenge ps3 with
  | mk rPi ps4 =>
  rw [hsc] at hp
  exact hp

theorem proveKeccakGkr_refines_spec (program : Array Spec.Vm.Op) (iv : ByteArray)
    (publicInput : Array E) (bundle : Spec.Witness.WitnessBundle) :
    (Model.KeccakGkr.proveKeccakGkr program iv publicInput bundle).toSpec =
      Spec.KeccakGkr.proveKeccakGkr program iv publicInput bundle := by
  unfold Model.KeccakGkr.proveKeccakGkr Spec.KeccakGkr.proveKeccakGkr
    Model.KeccakGkr.KeccakGkrStageOutput.toSpec
  dsimp only []
  have hBus := Proofs.Bus.proveBusAndConstraints_refines_spec program iv publicInput bundle
  have hp := proveBusAndConstraints_pending program iv publicInput bundle
  generalize Model.Bus.proveBusAndConstraints program iv publicInput bundle = busM at hBus hp ⊢
  generalize Spec.Bus.proveBusAndConstraints program iv publicInput bundle = busS at hBus ⊢
  subst hBus
  dsimp only [Model.Bus.BusStageOutput.toSpec]
  let qBase := (bundle.sized.layout.placements[Spec.Layout.qKeccak]?.join).map
    Spec.Layout.Placement.index |>.getD 0
  let executed := bundle.sized.rows[Spec.Layout.opKeccak]?.getD 0
  let width := 1 <<< Spec.KeccakGkr.stepsLog executed
  let span := (1 <<< Spec.KeccakGkr.slotBits) * width
  let committed := (Array.range span).map fun index => bundle.message[qBase + index]?.getD 0
  have hRed := proveReduction_rel committed executed busM.keccakOutput ⟨hp, rfl⟩
  rcases hRed with ⟨hOpen, _, hFin⟩
  cases hrm : Model.KeccakGkr.proveReduction busM.ps committed executed busM.keccakOutput with
  | mk openM finM =>
  cases hrs : Spec.KeccakGkr.proveReduction busM.ps.toSpec committed executed busM.keccakOutput with
  | mk openS finS =>
  rw [hrm, hrs] at hOpen hFin
  dsimp only [] at hOpen hFin ⊢
  subst hOpen
  rw [hFin]
  cases openM.outputs <;> rfl

end LeanVmXmss.Proofs.KeccakGkr
