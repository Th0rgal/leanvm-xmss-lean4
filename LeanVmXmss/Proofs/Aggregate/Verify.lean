import Model.Aggregate.Verify
import Proofs.Aggregate.Wire
import Proofs.Bus.Refinement
import Proofs.KeccakGkr.Refinement
import Proofs.Pcs.Whir
import Proofs.Layout.Basic

namespace LeanVmXmss.Proofs.Aggregate.Verify

open Spec.Field (K E zero one embed)
open Spec.Layout
open Spec.Aggregate.Verify (PreparedBytecode ExecutionSummary BusVerifyResult)

set_option maxRecDepth 20000
set_option maxHeartbeats 800000

private theorem foldRange_eq_spec :
    @Model.Pcs.Ntt.foldRange = @Spec.Aggregate.Verify.foldRange := by
  funext α n f init
  exact Proofs.Pcs.foldRange_eq n f init

private theorem eadd_eq_spec :
    Model.Field.eadd = Spec.Field.eadd := rfl

theorem prepareBytecodeFast_refines (program : Array Spec.Vm.Op) :
    Model.Aggregate.Verify.prepareBytecodeFast program =
      Spec.Aggregate.Verify.prepareBytecode program := by
  dsimp only [Model.Aggregate.Verify.prepareBytecodeFast, Spec.Aggregate.Verify.prepareBytecode]
  rw [Proofs.Layout.bytecodeColumnsFast_refines_spec,
    Proofs.Layout.stackBytecodeColumnsFast_refines_spec,
    Proofs.Layout.fiatShamirIvFast_refines_spec]

theorem dot_refines (a b : Array E) :
    Model.Aggregate.Verify.dot a b = Spec.Aggregate.Verify.dot a b :=
  Proofs.Pcs.Whir.dot_refines a b

theorem dot_eq_spec :
    Model.Aggregate.Verify.dot = Spec.Aggregate.Verify.dot := by
  funext a b
  exact dot_refines a b

theorem powers_refines (x : E) (n : Nat) :
    Model.Aggregate.Verify.powers x n = Spec.Aggregate.Verify.powers x n :=
  Proofs.Pcs.Whir.powers_refines x n

theorem powers_eq_spec :
    Model.Aggregate.Verify.powers = Spec.Aggregate.Verify.powers := by
  funext x n
  exact powers_refines x n

theorem eqKernel_refines (point : Array E) :
    Model.Aggregate.Verify.eqKernel point = Spec.Aggregate.Verify.eqKernel point :=
  Proofs.Pcs.Whir.eqKernel_refines point

theorem eqKernel_eq_spec :
    Model.Aggregate.Verify.eqKernel = Spec.Aggregate.Verify.eqKernel := by
  funext point
  exact eqKernel_refines point

theorem verifierSamples_refines (s : Spec.Transcript.VerifierState) (n : Nat) :
    Model.Aggregate.Verify.verifierSamples s n = Spec.Aggregate.Verify.verifierSamples s n := rfl

theorem multilinearEvalE_refines (values point : Array E) :
    Model.Aggregate.Verify.multilinearEvalE values point =
      Spec.Aggregate.Verify.multilinearEvalE values point := by
  dsimp only [Model.Aggregate.Verify.multilinearEvalE, Spec.Aggregate.Verify.multilinearEvalE]
  rw [eadd_eq_spec, Proofs.Bus.nativeKaratsuba_eq_emul]

theorem multilinearEvalE_eq_spec :
    Model.Aggregate.Verify.multilinearEvalE = Spec.Aggregate.Verify.multilinearEvalE := by
  funext values point
  exact multilinearEvalE_refines values point

theorem evalBytecodeFast_refines (bc : PreparedBytecode) (point : Array E) :
    Model.Aggregate.Verify.evalBytecodeFast bc point =
      if decide (bc.table.size ≠ 1 <<< point.size) then
        none
      else
        some (Spec.Pcs.Whir.multilinearEval bc.table point) := by
  unfold Model.Aggregate.Verify.evalBytecodeFast
  rw [Proofs.Pcs.Whir.multilinearEval_refines]

theorem evalBytecodeFast_eq_spec :
    Model.Aggregate.Verify.evalBytecodeFast =
      fun bc point =>
        if decide (bc.table.size ≠ 1 <<< point.size) then
          none
        else
          some (Spec.Pcs.Whir.multilinearEval bc.table point) := by
  funext bc point
  exact evalBytecodeFast_refines bc point

theorem sumcheckRoundPolyFast_refines (s : Spec.Transcript.VerifierState) (degree : Nat)
    (claimedSum : E) (eqFactor : Option E) :
    Model.Aggregate.Verify.sumcheckRoundPolyFast s degree claimedSum eqFactor =
      Spec.Transcript.sumcheckRoundPoly s degree claimedSum eqFactor := by
  cases eqFactor <;>
    dsimp only [Model.Aggregate.Verify.sumcheckRoundPolyFast, Spec.Transcript.sumcheckRoundPoly]
  · rw [eadd_eq_spec]
  · rw [eadd_eq_spec, Proofs.Bus.nativeKaratsuba_eq_emul]

theorem sumcheckRoundPolyFast_eq_spec :
    @Model.Aggregate.Verify.sumcheckRoundPolyFast = @Spec.Transcript.sumcheckRoundPoly := by
  funext s degree claimedSum eqFactor
  exact sumcheckRoundPolyFast_refines s degree claimedSum eqFactor

theorem sumcheckPlain_refines (s : Spec.Transcript.VerifierState) (degree rounds : Nat)
    (claim : E) :
    Model.Aggregate.Verify.sumcheckPlain s degree rounds claim =
      Spec.Aggregate.Verify.sumcheckPlain s degree rounds claim := by
  dsimp only [Model.Aggregate.Verify.sumcheckPlain, Spec.Aggregate.Verify.sumcheckPlain]
  rw [sumcheckRoundPolyFast_eq_spec, Proofs.Bus.polyEval_eq_spec]

theorem sumcheckPlain_eq_spec :
    Model.Aggregate.Verify.sumcheckPlain = Spec.Aggregate.Verify.sumcheckPlain := by
  funext s degree rounds claim
  exact sumcheckPlain_refines s degree rounds claim

theorem sumcheckWithEq_refines (s : Spec.Transcript.VerifierState) (degree : Nat)
    (claim : E) (equalities : Array E) :
    Model.Aggregate.Verify.sumcheckWithEq s degree claim equalities =
      Spec.Aggregate.Verify.sumcheckWithEq s degree claim equalities := by
  dsimp only [Model.Aggregate.Verify.sumcheckWithEq, Spec.Aggregate.Verify.sumcheckWithEq]
  rw [sumcheckRoundPolyFast_eq_spec, Proofs.Bus.polyEval_eq_spec]

theorem sumcheckWithEq_eq_spec :
    Model.Aggregate.Verify.sumcheckWithEq = Spec.Aggregate.Verify.sumcheckWithEq := by
  funext s degree claim equalities
  exact sumcheckWithEq_refines s degree claim equalities

theorem prodArray_refines (xs : Array E) :
    Model.Aggregate.Verify.prodArray xs = Spec.Aggregate.Verify.prodArray xs := by
  dsimp only [Model.Aggregate.Verify.prodArray, Spec.Aggregate.Verify.prodArray]
  rw [Proofs.Bus.nativeKaratsuba_eq_emul]

theorem prodArray_eq_spec :
    Model.Aggregate.Verify.prodArray = Spec.Aggregate.Verify.prodArray := by
  funext xs
  exact prodArray_refines xs

theorem verifyGkrGrandProducts_refines (depth : Nat) (s : Spec.Transcript.VerifierState) :
    Model.Aggregate.Verify.verifyGkrGrandProducts depth s =
      Spec.Aggregate.Verify.verifyGkrGrandProducts depth s := by
  dsimp only [Model.Aggregate.Verify.verifyGkrGrandProducts,
    Spec.Aggregate.Verify.verifyGkrGrandProducts,
    Model.Aggregate.Verify.verifierSamples, Spec.Aggregate.Verify.verifierSamples,
    Model.Pcs.Whir.verifierSamples, Spec.Pcs.Whir.verifierSamples]
  rw [Proofs.Bus.polyEval_eq_spec, sumcheckWithEq_eq_spec, prodArray_eq_spec,
    multilinearEvalE_eq_spec]

theorem scaleBusFormFast_refines (form : Spec.Bus.BusForm) (factor : E) :
    Model.Aggregate.Verify.scaleBusFormFast form factor =
      Spec.Bus.scaleBusForm form factor := by
  dsimp only [Model.Aggregate.Verify.scaleBusFormFast, Spec.Bus.scaleBusForm]
  rw [Proofs.Bus.nativeKaratsuba_eq_emul]

theorem scaleBusFormFast_eq_spec :
    Model.Aggregate.Verify.scaleBusFormFast = Spec.Bus.scaleBusForm := by
  funext form factor
  exact scaleBusFormFast_refines form factor

theorem evalBusForm_refines (form : Spec.Bus.BusForm) (evals : Array E) :
    Model.Aggregate.Verify.evalBusForm form evals =
      Spec.Aggregate.Verify.evalBusForm form evals := by
  dsimp only [Model.Aggregate.Verify.evalBusForm, Spec.Aggregate.Verify.evalBusForm]
  rw [foldRange_eq_spec, eadd_eq_spec, Proofs.Bus.nativeKaratsuba_eq_emul]
  rfl

theorem evalBusForm_eq_spec :
    Model.Aggregate.Verify.evalBusForm = Spec.Aggregate.Verify.evalBusForm := by
  funext form evals
  exact evalBusForm_refines form evals

theorem verifySideBlocks_refines (blocks : Array Block) (lay : BusLayout) (mu : Nat)
    (point : Array E) (frameworkCount : Nat) (frameworkFps weights : Array E)
    (sideBeta treeValue : E) :
    Model.Aggregate.Verify.verifySideBlocks blocks lay mu point frameworkCount frameworkFps weights
        sideBeta treeValue =
      Spec.Aggregate.Verify.verifySideBlocks blocks lay mu point frameworkCount frameworkFps weights
        sideBeta treeValue := by
  dsimp only [Model.Aggregate.Verify.verifySideBlocks, Spec.Aggregate.Verify.verifySideBlocks]
  rw [foldRange_eq_spec, eadd_eq_spec, Proofs.Bus.eqEval_eq_spec, Proofs.Bus.nativeKaratsuba_eq_emul,
    scaleBusFormFast_eq_spec, evalBusForm_eq_spec, Proofs.Bus.paddingWeight_eq_spec]
  rfl

theorem verifySideBlocks_eq_spec :
    Model.Aggregate.Verify.verifySideBlocks = Spec.Aggregate.Verify.verifySideBlocks := by
  funext blocks lay mu point frameworkCount frameworkFps weights sideBeta treeValue
  exact verifySideBlocks_refines blocks lay mu point frameworkCount frameworkFps weights sideBeta
    treeValue

private def toSpecLayout (lay : Model.Layout.PublicLayout) : Spec.Aggregate.Verify.PublicLayout :=
  ⟨lay.logMem, lay.logBytecode, lay.rows, lay.taus, lay.placements, lay.shape, lay.placed,
    lay.push, lay.pull, lay.count, lay.pushLayout, lay.pullLayout, lay.countLayout⟩

private theorem all_toList_decide (rows : Array Nat) :
    (rows.toList.all fun r => decide (r ≤ (1 <<< maxTableLog))) =
      rows.all (fun r => decide (r ≤ (1 <<< maxTableLog))) := by
  rw [← Array.all_toList]

private theorem decide_and_eq {p q : Prop} [Decidable p] [Decidable q] :
    decide (p ∧ q) = (decide p && decide q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

private theorem validateSizes_refines (logMem logBytecode logInvRate : Nat) (rows : Array Nat) :
    Model.Layout.validateSizes logMem logBytecode logInvRate rows =
      Spec.Aggregate.Verify.validateSizes logMem logBytecode logInvRate rows := by
  unfold Model.Layout.validateSizes Spec.Aggregate.Verify.validateSizes
  rw [all_toList_decide, decide_and_eq, decide_and_eq]
  simp only [Bool.and_assoc]

private theorem multilinearEval_whir_eq_spec :
    Model.Pcs.Whir.multilinearEval = Spec.Pcs.Whir.multilinearEval := by
  funext table point
  exact Proofs.Pcs.Whir.multilinearEval_refines table point

theorem verifyBusBalance_refines (bc : PreparedBytecode) (lay : Model.Layout.PublicLayout)
    (s : Spec.Transcript.VerifierState) :
    Model.Aggregate.Verify.verifyBusBalance bc lay s =
      Spec.Aggregate.Verify.verifyBusBalance bc (toSpecLayout lay) s := by
  dsimp only [Model.Aggregate.Verify.verifyBusBalance, Spec.Aggregate.Verify.verifyBusBalance,
    toSpecLayout, Model.Aggregate.Verify.verifierSamples, Spec.Aggregate.Verify.verifierSamples,
    Model.Pcs.Whir.verifierSamples, Spec.Pcs.Whir.verifierSamples,
    Model.Aggregate.Verify.evalBytecodeFast]
  rw [eqKernel_eq_spec, verifyGkrGrandProducts_refines, Proofs.Bus.indexMle_eq_spec,
    multilinearEval_whir_eq_spec, eadd_eq_spec, dot_eq_spec, verifySideBlocks_eq_spec]
  generalize Spec.Aggregate.Verify.verifyGkrGrandProducts lay.pushLayout.mu
      (Spec.Transcript.verifierSample
        ((Array.range busBits).foldl
          (fun x _ =>
            let p := Spec.Transcript.verifierSample x.2
            (x.1.push p.1, p.2))
          (#[], s)).2).2 = gkrOpt
  cases gkrOpt with
  | none => rfl
  | some gkrVal =>
    rcases gkrVal with ⟨cnt, point, treeValues, s1⟩
    dsimp only [Bind.bind, Option.bind]
    cases decide (point.size < lay.logMem) || decide (point.size < lay.logBytecode) with
    | true => rfl
    | false =>
      cases Spec.Transcript.nextScalars 3 s1 with
      | none => rfl
      | some memPair =>
        rcases memPair with ⟨memory, s2⟩
        dsimp only []
        cases Spec.Transcript.nextScalar s2 with
        | none => rfl
        | some mfPair =>
          rcases mfPair with ⟨memoryFinal, s3⟩
          dsimp only []
          cases Spec.Transcript.nextScalar s3 with
          | none => rfl
          | some bfPair =>
            rcases bfPair with ⟨bytecodeFinalVal, s4⟩
            dsimp only []
            cases decide (bc.table.size ≠ 1 <<< (point.extract 0 lay.logBytecode ++
                ((Array.range busBits).foldl
                  (fun x _ =>
                    let p := Spec.Transcript.verifierSample x.2
                    (x.1.push p.1, p.2))
                  (#[], s)).1).size) with
            | true => rfl
            | false => rfl

theorem verifyTableSumcheck_refines (taus : Array Nat)
    (forms0 forms1 forms2 : Array Spec.Bus.BusForm)
    (constraintPowers formPowers equalityPoint : Array E) (target : E)
    (s : Spec.Transcript.VerifierState) :
    Model.Aggregate.Verify.verifyTableSumcheck taus forms0 forms1 forms2
        constraintPowers formPowers equalityPoint target s =
      Spec.Aggregate.Verify.verifyTableSumcheck taus forms0 forms1 forms2
        constraintPowers formPowers equalityPoint target s := by
  dsimp only [Model.Aggregate.Verify.verifyTableSumcheck,
    Spec.Aggregate.Verify.verifyTableSumcheck]
  rw [sumcheckPlain_eq_spec, foldRange_eq_spec, eadd_eq_spec, Proofs.Bus.nativeKaratsuba_eq_emul,
    evalBusForm_eq_spec, dot_eq_spec]

private theorem instanceWeights_eq_spec :
    Model.KeccakGkr.instanceWeights = Spec.KeccakGkr.instanceWeights := by
  funext seed
  exact Proofs.KeccakGkr.instanceWeights_refines_spec seed

theorem verifyKeccakLayer_refines (logSteps step : Nat) (claim : Spec.KeccakGkr.GkrClaim)
    (s : Spec.Transcript.VerifierState) :
    Model.Aggregate.Verify.verifyKeccakLayer logSteps step claim s =
      Spec.Aggregate.Verify.verifyKeccakLayer logSteps step claim s := by
  dsimp only [Model.Aggregate.Verify.verifyKeccakLayer, Spec.Aggregate.Verify.verifyKeccakLayer,
    Model.KeccakGkr.sumSlice, Model.KeccakGkr.linearTranspose]
  rw [foldRange_eq_spec, eqKernel_eq_spec, eadd_eq_spec, Proofs.Bus.nativeKaratsuba_eq_emul,
    instanceWeights_eq_spec, Proofs.Bus.polyEval_eq_spec,
    sumcheckRoundPolyFast_eq_spec, sumcheckPlain_eq_spec, dot_eq_spec]

theorem verifyKeccakLayer_eq_spec :
    Model.Aggregate.Verify.verifyKeccakLayer = Spec.Aggregate.Verify.verifyKeccakLayer := by
  funext logSteps step claim s
  exact verifyKeccakLayer_refines logSteps step claim s

theorem slotWeights_refines (logSteps : Nat) (claim : Spec.KeccakGkr.GkrClaim) (first count : Nat) :
    Model.Aggregate.Verify.slotWeights logSteps claim first count =
      Spec.Aggregate.Verify.slotWeights logSteps claim first count := by
  dsimp only [Model.Aggregate.Verify.slotWeights, Spec.Aggregate.Verify.slotWeights]
  rw [foldRange_eq_spec, eqKernel_eq_spec, Proofs.Bus.nativeKaratsuba_eq_emul]

theorem openSlot_refines (logSteps : Nat) (claim : Spec.KeccakGkr.GkrClaim) (first count : Nat)
    (value : E) (s : Spec.Transcript.VerifierState) :
    Model.Aggregate.Verify.openSlot logSteps claim first count value s =
      Spec.Aggregate.Verify.openSlot logSteps claim first count value s := by
  dsimp only [Model.Aggregate.Verify.openSlot, Spec.Aggregate.Verify.openSlot]
  rw [sumcheckPlain_eq_spec, slotWeights_refines, foldRange_eq_spec, eadd_eq_spec,
    Proofs.Bus.nativeKaratsuba_eq_emul]

theorem openSlot_eq_spec :
    Model.Aggregate.Verify.openSlot = Spec.Aggregate.Verify.openSlot := by
  funext logSteps claim first count value s
  exact openSlot_refines logSteps claim first count value s

theorem verifyKeccak_refines (logSteps : Nat) (inst output : Array E)
    (s : Spec.Transcript.VerifierState) :
    Model.Aggregate.Verify.verifyKeccak logSteps inst output s =
      Spec.Aggregate.Verify.verifyKeccak logSteps inst output s := by
  dsimp only [Model.Aggregate.Verify.verifyKeccak, Spec.Aggregate.Verify.verifyKeccak,
    Model.Aggregate.Verify.verifierSamples, Spec.Aggregate.Verify.verifierSamples,
    Model.Pcs.Whir.verifierSamples, Spec.Pcs.Whir.verifierSamples]
  rw [eqKernel_eq_spec, eadd_eq_spec, Proofs.Bus.nativeMulBase_eq_mulBase,
    Proofs.Bus.nativeKaratsuba_eq_emul, dot_eq_spec, verifyKeccakLayer_eq_spec, openSlot_eq_spec,
    sumcheckPlain_eq_spec, multilinearEvalE_eq_spec]

private theorem verifyRingSwitchAndStacked_eq_spec :
    Model.Pcs.Whir.verifyRingSwitchAndStacked = Spec.Pcs.Whir.verifyRingSwitchAndStacked := by
  funext s root stackLog placed logInvRate qkeccak ringPoint slices claims
  exact Proofs.Pcs.Whir.verifyRingSwitchAndStacked_refines
    s root stackLog placed logInvRate qkeccak ringPoint slices claims

private theorem buildPublicLayout_toSpec (logMem logBytecode : Nat) (rowArr : Array Nat) :
    toSpecLayout (Model.Layout.buildPublicLayout logMem logBytecode rowArr) =
      Spec.Aggregate.Verify.buildPublicLayout logMem logBytecode rowArr := by
  dsimp only [Model.Layout.buildPublicLayout, Spec.Aggregate.Verify.buildPublicLayout,
    Model.Layout.placementsOf, toSpecLayout]

private theorem validateSizes_eq_spec :
    Model.Layout.validateSizes = Spec.Aggregate.Verify.validateSizes := by
  funext logMem logBytecode logInvRate rows
  exact validateSizes_refines logMem logBytecode logInvRate rows

private theorem verifyTableSumcheck_eq_spec :
    Model.Aggregate.Verify.verifyTableSumcheck = Spec.Aggregate.Verify.verifyTableSumcheck := by
  funext taus forms0 forms1 forms2 constraintPowers formPowers equalityPoint target s
  exact verifyTableSumcheck_refines taus forms0 forms1 forms2 constraintPowers formPowers
    equalityPoint target s

private theorem verifyKeccak_eq_spec :
    Model.Aggregate.Verify.verifyKeccak = Spec.Aggregate.Verify.verifyKeccak := by
  funext logSteps inst output s
  exact verifyKeccak_refines logSteps inst output s

theorem verifyExecution_refines (bc : PreparedBytecode) (publicInput : ByteArray)
    (proof : Spec.Aggregate.Wire.VmProof) :
    Model.Aggregate.Verify.verifyExecution bc publicInput proof =
      Spec.Aggregate.Verify.verifyExecution bc publicInput proof := by
  dsimp only [Model.Aggregate.Verify.verifyExecution, Spec.Aggregate.Verify.verifyExecution]
  rw [validateSizes_eq_spec, powers_eq_spec, dot_eq_spec, verifyTableSumcheck_eq_spec,
    foldRange_eq_spec, Proofs.Bus.interpK_eq_spec, verifyKeccak_eq_spec,
    verifyRingSwitchAndStacked_eq_spec]
  generalize hmBuild : Model.Layout.buildPublicLayout = mBuild
  generalize hsBuild : Spec.Aggregate.Verify.buildPublicLayout = sBuild
  have hBuild : ∀ a b c, sBuild a b c = toSpecLayout (mBuild a b c) := by
    intro a b c
    rw [← hsBuild, ← hmBuild]
    exact (buildPublicLayout_toSpec a b c).symm
  cases decide (publicInput.size ≠ 32) with
  | true => rfl
  | false =>
    dsimp only [Bind.bind, Option.bind]
    cases Spec.Transcript.nextScalars (2 + nTables)
        (Spec.Transcript.verifierNew ⟨proof.stream, proof.merkle⟩ bc.iv publicInput) with
    | none => rfl
    | some annPair =>
      rcases annPair with ⟨announced, s1⟩
      dsimp only []
      cases !(announced.all fun v => decide (v.c1 = 0 ∧ v.c2 = 0)) with
      | true => rfl
      | false =>
        cases !Spec.Aggregate.Verify.validateSizes (announced.getD 0 zero).c0.toNat bc.logBytecode
            (announced.getD (1 + nTables) zero).c0.toNat
            ((Array.range nTables).map fun i => (announced.getD (1 + i) zero).c0.toNat) with
        | true => rfl
        | false =>
          rw [hBuild]
          generalize mBuild (announced.getD 0 zero).c0.toNat bc.logBytecode
              ((Array.range nTables).map fun i => (announced.getD (1 + i) zero).c0.toNat) = mlay
          have hmu : (toSpecLayout mlay).shape.mu = mlay.shape.mu := rfl
          have htaus : (toSpecLayout mlay).taus = mlay.taus := rfl
          have hpl : (toSpecLayout mlay).placements = mlay.placements := rfl
          have hpcd : (toSpecLayout mlay).placed = mlay.placed := rfl
          have hlmem : (toSpecLayout mlay).logMem = mlay.logMem := rfl
          rw [hmu, htaus, hpl, hpcd, hlmem]
          cases !(decide (minStackedLog ≤ mlay.shape.mu ∧ mlay.shape.mu ≤ maxStackedLog)) with
          | true => rfl
          | false =>
            cases Spec.Transcript.nextScalars 2 s1 with
            | none => rfl
            | some hPair =>
              rcases hPair with ⟨halves, s2⟩
              dsimp only []
              cases Spec.Merkle.fromHalves (halves.getD 0 zero) (halves.getD 1 zero) with
              | none => rfl
              | some root =>
                dsimp only []
                rw [verifyBusBalance_refines]
                rfl

private theorem verifyExecution_eq_spec :
    Model.Aggregate.Verify.verifyExecution = Spec.Aggregate.Verify.verifyExecution := by
  funext bc publicInput proof
  exact verifyExecution_refines bc publicInput proof

theorem verifyEthereumProof_refines (guest : PreparedBytecode) (seed : E × E)
    (eth : Spec.Aggregate.Wire.EthereumProof) :
    Model.Aggregate.Verify.verifyEthereumProof guest seed eth =
      Spec.Aggregate.Verify.verifyEthereumProof guest seed eth := by
  unfold Model.Aggregate.Verify.verifyEthereumProof Spec.Aggregate.Verify.verifyEthereumProof
    Spec.Aggregate.Wire.deferredMatches
  rw [Proofs.Aggregate.Wire.signerSetOk_refines, evalBytecodeFast_refines,
    Proofs.Aggregate.Wire.ethereumProof_statement_refines, verifyExecution_eq_spec]
  cases !Spec.Aggregate.Wire.signerSetOk eth.claims with
  | true => rfl
  | false =>
    by_cases h : guest.table.size = 1 <<< eth.defer.bytecodePoint.size
    · have h1 : decide (guest.table.size ≠ 1 <<< eth.defer.bytecodePoint.size) = false :=
        decide_eq_false (fun hne => hne h)
      have h2 : decide (1 <<< eth.defer.bytecodePoint.size = guest.table.size) = true :=
        decide_eq_true h.symm
      simp only [h1, h2, Bool.false_eq_true, ite_false, ite_true]
    · have h1 : decide (guest.table.size ≠ 1 <<< eth.defer.bytecodePoint.size) = true :=
        decide_eq_true h
      have h2 : decide (1 <<< eth.defer.bytecodePoint.size = guest.table.size) = false :=
        decide_eq_false (fun heq => h heq.symm)
      rw [h1, h2]
      rfl

private theorem verifyEthereumProof_eq_spec :
    Model.Aggregate.Verify.verifyEthereumProof = Spec.Aggregate.Verify.verifyEthereumProof := by
  funext guest seed eth
  exact verifyEthereumProof_refines guest seed eth

theorem verifyEthereumBytes_refines (guest : PreparedBytecode) (seed : E × E)
    (bytes : ByteArray) :
    Model.Aggregate.Verify.verifyEthereumBytes guest seed bytes =
      Spec.Aggregate.Verify.verifyEthereumBytes guest seed bytes := by
  dsimp only [Model.Aggregate.Verify.verifyEthereumBytes, Spec.Aggregate.Verify.verifyEthereumBytes]
  rw [Proofs.Aggregate.Wire.fromBytes_refines, evalBytecodeFast_eq_spec, verifyEthereumProof_eq_spec]
  cases Spec.Aggregate.Wire.EthereumProof.fromBytes bytes zero with
  | none => rfl
  | some raw =>
    dsimp only []
    by_cases h : guest.table.size = 1 <<< raw.defer.bytecodePoint.size
    · have h1 : decide (guest.table.size ≠ 1 <<< raw.defer.bytecodePoint.size) = false :=
        decide_eq_false (fun hne => hne h)
      have h2 : decide (1 <<< raw.defer.bytecodePoint.size ≠ guest.table.size) = false :=
        decide_eq_false (fun hne => hne h.symm)
      rw [h1, h2]
      rfl
    · have h1 : decide (guest.table.size ≠ 1 <<< raw.defer.bytecodePoint.size) = true :=
        decide_eq_true h
      have h2 : decide (1 <<< raw.defer.bytecodePoint.size ≠ guest.table.size) = true :=
        decide_eq_true (fun heq => h heq.symm)
      rw [h1, h2]
      rfl

theorem verifyEthereumBytesWithoutPubkeys_refines (guest : PreparedBytecode) (seed : E × E)
    (claims : Spec.Aggregate.Wire.SignatureClaims) (bytes : ByteArray) :
    Model.Aggregate.Verify.verifyEthereumBytesWithoutPubkeys guest seed claims bytes =
      Spec.Aggregate.Verify.verifyEthereumBytesWithoutPubkeys guest seed claims bytes := by
  dsimp only [Model.Aggregate.Verify.verifyEthereumBytesWithoutPubkeys,
    Spec.Aggregate.Verify.verifyEthereumBytesWithoutPubkeys]
  rw [Proofs.Aggregate.Wire.fromBytesWithoutPubkeys_refines, evalBytecodeFast_eq_spec,
    verifyEthereumProof_eq_spec]
  cases Spec.Aggregate.Wire.EthereumProof.fromBytesWithoutPubkeys bytes claims zero with
  | none => rfl
  | some raw =>
    dsimp only []
    by_cases h : guest.table.size = 1 <<< raw.defer.bytecodePoint.size
    · have h1 : decide (guest.table.size ≠ 1 <<< raw.defer.bytecodePoint.size) = false :=
        decide_eq_false (fun hne => hne h)
      have h2 : decide (1 <<< raw.defer.bytecodePoint.size ≠ guest.table.size) = false :=
        decide_eq_false (fun hne => hne h.symm)
      rw [h1, h2]
      rfl
    · have h1 : decide (guest.table.size ≠ 1 <<< raw.defer.bytecodePoint.size) = true :=
        decide_eq_true h
      have h2 : decide (1 <<< raw.defer.bytecodePoint.size ≠ guest.table.size) = true :=
        decide_eq_true (fun heq => h heq.symm)
      rw [h1, h2]
      rfl

theorem verifyVmWireBytes_refines (bc : PreparedBytecode) (publicInput : ByteArray)
    (bytes : ByteArray) :
    Model.Aggregate.Verify.verifyVmWireBytes bc publicInput bytes =
      Spec.Aggregate.Verify.verifyVmWireBytes bc publicInput bytes := by
  dsimp only [Model.Aggregate.Verify.verifyVmWireBytes, Spec.Aggregate.Verify.verifyVmWireBytes]
  rw [verifyExecution_eq_spec]
  rfl

end LeanVmXmss.Proofs.Aggregate.Verify
