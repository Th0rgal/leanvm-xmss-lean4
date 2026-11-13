import Model.Cli.E2E

namespace LeanVmXmss.PcsOpeningDiagnostics
open Spec.Field (K E)
open Spec.Vm
open Model.Merkle (Digest32)
open Model.Pcs.Ntt (Vec8 foldRange)
open Model.Pcs.Whir
open Model.Pcs
open Model.Pcs.FlatWhir
open Model.Cli

-- A noinline IO call forces the pure result before the stop-clock read.
-- This module is diagnostics only and is excluded from matched certification.
@[noinline] def forceResult (x : α) : IO α := pure x

def measuredIO (name : String) (f : Unit → α) : IO α := do
  let start ← IO.monoNanosNow
  let value ← forceResult (f ())
  let stop ← IO.monoNanosNow
  IO.println s!"PCS_DIAG|{name}|nanos={stop-start}"
  return value

def measured (name : String) (f : Unit → α) : OptionT IO α :=
  OptionT.lift (measuredIO name f)

def need (x : Option α) : OptionT IO α := OptionT.mk (pure x)

def streamCosetsOpen (nCosets logRows subK blockLog : Nat) (indices : @& Array Nat)
    (encodeCoset : Nat → OptionT IO (Array Vec8))
    (extractRow : Array Vec8 → Nat → Array K)
    (leafAt : Array Vec8 → Nat → Digest32)
    (fastSubRoot : Array Vec8 → Nat → Nat → Digest32) :
    OptionT IO Spec.Merkle.PrunedMerklePaths := do
  let rowsPerCoset := 1 <<< logRows
  let subSize := 1 <<< subK
  let subsPerCoset := 1 <<< (logRows - subK)
  let totalSubs := 1 <<< (blockLog - subK)
  let initLow := Array.replicate subK (#[] : Array Digest32)
  let (openedRows, lowSibs, topActive, subRoots, _) ←
    (Array.range nCosets).foldlM
      (fun (opRows, lowAcc, topAct, roots, qCur) curC => do
        let cosetBase := curC * rowsPerCoset
        let cosetEnd := cosetBase + rowsPerCoset
        let encoded ← encodeCoset curC
        let cosetStop := advanceCursor indices cosetEnd qCur
        let opRows := foldRange (cosetStop - qCur) (fun acc k =>
          let gIdx := indices.getD (qCur + k) 0
          acc.push (extractRow encoded (gIdx - cosetBase))) opRows
        let (lowAcc, topAct, roots, qNext) ←
          (Array.range subsPerCoset).foldlM
            (fun (lSibs, tAct, rAcc, cur) m => do
              let subGlobalBase := cosetBase + (m <<< subK)
              let subGlobalEnd := subGlobalBase + subSize
              let nextCur := advanceCursor indices subGlobalEnd cur
              if decide (cur = nextCur) then
                let r ← measured s!"unqueried_merkle|coset={curC}|sub={m}|k={subK}" (fun _ => fastSubRoot encoded subK (m <<< subK))
                pure (lSibs, tAct, rAcc.push r, cur)
              else
                let leaves ← measured s!"queried_leaves|coset={curC}|sub={m}|k={subK}" (fun _ => foldRange subSize (fun acc j =>
                  acc.push (leafAt encoded ((m <<< subK) + j))) (Array.emptyWithCapacity subSize))
                let subTree ← need (← measured "queried_buildFlat" (fun _ => Model.Merkle.buildFlat subK leaves))
                let locAct := collectLocalActive indices subGlobalBase cur nextCur
                let (_, perLvl) := Model.Merkle.flatLevelsSiblings subTree locAct
                let lSibs := foldRange subK (fun ls lvl =>
                  ls.setIfInBounds lvl ((ls.getD lvl #[]) ++ (perLvl.getD lvl #[]))) lSibs
                let r := Model.Merkle.flatRoot subTree
                pure (lSibs, tAct.push (curC * subsPerCoset + m), rAcc.push r, nextCur))
            (lowAcc, topAct, roots, qCur)
        pure (opRows, lowAcc, topAct, roots, qNext))
      (Array.emptyWithCapacity indices.size, initLow, (#[] : Array Nat),
       Array.emptyWithCapacity totalSubs, 0)
  let topTree ← need (← measured "top_buildFlat" (fun _ => Model.Merkle.buildFlat (blockLog - subK) subRoots))
  let topSibs := Model.Merkle.flatSiblings topTree topActive.toList
  let lowFlat := foldRange subK (fun acc lvl => acc ++ (lowSibs.getD lvl #[])) #[]
  let allSibs := (lowFlat ++ topSibs).map Digest32.toSpecDigest
  pure ⟨openedRows, allSibs⟩

def openL0Cosets (bytes : @& ByteArray) (lanes logRows logInvRate : Nat)
    (queries : @& Array Nat) : OptionT IO Spec.Merkle.PrunedMerklePaths := do
  let blockLog := logRows + logInvRate
  let indices := Spec.Merkle.sortedUnique queries
  if !Spec.Merkle.validIndices blockLog indices then failure
  else
    let width := Spec.Pcs.Commit.rowWords lanes
    let nVecs := width / 8
    let table := Model.Pcs.Ntt.evals blockLog
    let st1 := Model.Pcs.Commit.zeroPrefixState 1
    let st2 := Model.Pcs.Commit.zeroPrefixState 2
    let st3 := Model.Pcs.Commit.zeroPrefixState 3
    let subK := min logRows 10
    streamCosetsOpen (1 <<< logInvRate) logRows subK blockLog indices
      (fun curC => do
        let first ← measured s!"firstCoset|coset={curC}|logRows={logRows}|nVecs={nVecs}" (fun _ => firstCosetFromBytes bytes lanes nVecs logRows)
        measured s!"nttL0|coset={curC}|logRows={logRows}|nVecs={nVecs}" (fun _ => Model.Pcs.Ntt.encodeCosetVec8 table first nVecs logRows logInvRate curC))
      (fun encoded loc => extractL0Row encoded lanes width nVecs loc)
      (fun encoded loc => Model.Pcs.Commit.hashLeafVec8From st1 st2 st3 encoded nVecs loc)
      (fun encoded k base => Model.Pcs.Commit.subtreeRootBuf st1 st2 st3 encoded nVecs k base)

def openExtCosets (prep : @& ExtPrepared) (queries : @& Array Nat) :
    OptionT IO Spec.Merkle.PrunedMerklePaths := do
  let logRows := prep.logRows
  let logInvRate := prep.logInvRate
  let blockLog := logRows + logInvRate
  let indices := Spec.Merkle.sortedUnique queries
  if !Spec.Merkle.validIndices blockLog indices then failure
  else
    let width := 3 * (1 <<< prep.logNumInterleaved)
    let nVecs := (width + 7) / 8
    let table := Model.Pcs.Ntt.evals blockLog
    let subK := min logRows 10
    streamCosetsOpen (1 <<< logInvRate) logRows subK blockLog indices
      (fun curC => measured s!"nttExt|coset={curC}|logRows={logRows}|nVecs={nVecs}" (fun _ => Model.Pcs.Ntt.encodeCosetVec8 table prep.first nVecs logRows logInvRate curC))
      (fun encoded loc => extractExtRow encoded width nVecs loc)
      (fun encoded loc => hashLeafExtVec8 encoded width nVecs loc)
      (fun encoded k base => subtreeRootExtVec8 encoded width nVecs k base)

def proveLevelPlanar (config : Spec.Pcs.Whir.Config) (logN lanes : Nat)
    (witness : @& ByteArray) (terms : @& WeightTerms)
    (p : PlanarFoldState) (level : Nat) (extPrep? : Option ExtPrepared) :
    OptionT IO (PlanarFoldState × Option ExtPrepared) := do
  let foldCount := config.folds.getD level 0
  let laneBlock := 1 <<< (logN - config.folds.getD 0 0)
  let p ← measured s!"fold|level={level}|foldCount={foldCount}" (fun _ =>
    if decide (level = 0) then
      foldInitialLanes witness lanes laneBlock foldCount terms p.claim p.state
    else
      foldRange foldCount (fun cur _ => stepFoldPlanar cur) p)
  let messageLog := logN - p.folds.size
  let finalLevel := decide (level + 1 = config.folds.size)
  let (s, oodInfo?, nextPrep?) ←
    if finalLevel then
      let s := Spec.Transcript.addScalars p.state (planarToArray p.f)
      pure (s, none, none)
    else
      let nextFold := config.folds.getD (level + 1) 0
      let nextRate := config.logInvRates.getD (level + 1) 0
      let (prep, root) ← measured s!"commitExt|level={level}|logRows={messageLog-nextFold}|fold={nextFold}|rate={nextRate}" (fun _ => commitExtPlanar p.f (messageLog - nextFold) nextFold nextRate)
      let s := addRootDigest32 p.state root
      let (ood, s) ← measured "introduceOod" (fun _ => introduceOodPlanar p.f s messageLog)
      pure (s, some ood, some prep)
  let s ← need (← measured "grindWhir" (fun _ => grindWhirFast s queryGrindingBits))
  let rate := config.logInvRates.getD level 0
  let blockLog := messageLog + rate
  let count := config.queries.getD level 0
  let perWord := 192 / blockLog
  if decide (perWord = 0) then failure
  else
    let (drawn, s) := Spec.Pcs.Whir.proverSamples s ((count + perWord - 1) / perWord)
    let queries := sampleQueries count blockLog drawn
    let (lam, s) := Spec.Transcript.sample s
    let weights := powers lam queries.size
    let indices := Spec.Merkle.sortedUnique queries
    let phase ←
      if decide (level = 0) then
        openL0Cosets witness lanes messageLog rate queries
      else
        match extPrep? with
        | some prep => openExtCosets prep queries
        | none => failure
    let s := hintPhaseFast s phase
    let laneFolds := p.folds.extract (p.folds.size - foldCount) p.folds.size
    let enforced := enforcedSumPhase level indices phase.rows queries laneFolds weights
    let basisI ← measured s!"inducedBasis|level={level}" (fun _ => inducedBasisPlanar messageLog rate queries weights)
    let (u0, u2) ← measured s!"msgPlanar|level={level}" (fun _ => msgPlanar p.f basisI)
    let (quadI, s) := Spec.Pcs.Whir.sendRound s enforced u0 u2
    let (basis, claim, quad) :=
      match oodInfo? with
      | some (z, oodVal, oodQuad) =>
        let s1 := lam
        let s2 := Model.Field.nativeKaratsuba lam lam
        let nextBasis := glueBasisPlanar p.basis (some z) s1 s2 basisI
        let nextClaim := Spec.Field.eadd p.claim
          (Spec.Field.eadd (Model.Field.nativeKaratsuba s1 oodVal)
            (Model.Field.nativeKaratsuba s2 enforced))
        let nextQuad := addScaled (addScaled p.quad s1 oodQuad) s2 quadI
        (nextBasis, nextClaim, nextQuad)
      | none =>
        let s1 := lam
        let nextBasis := glueBasisPlanar p.basis none Spec.Field.zero s1 basisI
        let nextClaim := Spec.Field.eadd p.claim (Model.Field.nativeKaratsuba s1 enforced)
        let nextQuad := addScaled p.quad s1 quadI
        (nextBasis, nextClaim, nextQuad)
    pure (⟨p.f, basis, claim, quad, p.folds, s⟩, nextPrep?)

def provePcsOpenFlat (s : Spec.Transcript.ProverState) (stackLog logInvRate : Nat)
    (witness : ByteArray) (points : Array Spec.Pcs.StackOpen.StackClaim)
    (ring : Spec.Pcs.StackOpen.RingSwitchOpen) : OptionT IO Spec.Transcript.ProverState := do
  let config ← need (deriveConfig stackLog logInvRate)
  if config.folds.isEmpty then failure
  else
    let k0 := config.folds.getD 0 0
    let laneVars := stackLog - k0
    let laneBlock := 1 <<< laneVars
    let nWords := witness.size / 8
    if decide (nWords = 0 ∨ nWords % laneBlock ≠ 0) then failure
    else
      let lanes := nWords / laneBlock
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
      let terms ← measured s!"termsOf|nWords={nWords}|lanes={lanes}|stackLog={stackLog}" (fun _ => termsOf nWords laneVars lam points ring ringWeights)
      let p0 : PlanarFoldState := ⟨planarEmpty 0, planarEmpty 0, target, #[], #[], s⟩
      let (done, _) ← (Array.range config.folds.size).foldlM
        (fun (p, prep?) level =>
          proveLevelPlanar config stackLog lanes witness terms p level prep?)
        (p0, none)
      let resLog := stackLog - done.folds.size
      let done := foldRange resLog (fun p j =>
        if decide (j + 1 < resLog) then stepFoldPlanar p else absorbFoldPlanar p) done
      pure done.state

def proveLeafEthereumTimedPass (program : Array Op) (frame : Nat)
    (schedule : Array (Array RHint)) (seed : ByteArray) (bytecodeValue : E)
    (records : Array Spec.Xmss.RawSignature) (logInvRate : Nat) (iv : ByteArray)
    (bcCols : Array (Array Spec.Field.K)) (exportDir : Option System.FilePath := none)
    (fuel : Nat := 10000000) :
    IO (Spec.Aggregate.Wire.EthereumProof × ByteArray × Nat × VmProvedRun ×
      ByteArray × PhaseTimings) := do
  let t0 ← IO.monoNanosNow
  let (signers, hints) ← verifyAndHintsParallel seed records bytecodeValue
  let statement := Model.Xmss.statementDigest seed signers bytecodeValue
  let streams := streamsOfHints hints
  let t0b ← IO.monoNanosNow
  let (rss0b, _) ← readProcMemBytes
  let publicInput := #[Spec.Xmss.packCell statement, Spec.Xmss.packCell statement 16]
  let state ← liftFault (Model.Vm.initial frame publicInput program.size)
  let trace ← liftFault
    (Model.Witness.executeTraceFlat fuel program schedule ⟨state, streams⟩)
  unless decide (trace.unconstrained = 0) do throw (IO.userError "unconstrained reads")
  let traceCycles := trace.cycles
  let traceMemUsed := trace.memUsed
  let initInput := #[Spec.Witness.cellWord state.memory 0, Spec.Witness.cellWord state.memory 1]
  let (sized, wq, wins) ← assembleWqK4 program trace
  let t1 ← IO.monoNanosNow
  let (rss1, _) ← readProcMemBytes
  let sh := sized.layout.shape
  let root ← Model.Witness.commitRootWqPar wq sh.nLanes (sh.mu - Spec.Layout.logBatch)
    Spec.Witness.logInvRateDefault
  let t2 ← IO.monoNanosNow
  let (rss2, _) ← readProcMemBytes
  let executed := sized.rows[Spec.Layout.opKeccak]?.getD 0
  let qBase := (sized.layout.placements[Spec.Layout.qKeccak]?.join).map
    Spec.Layout.Placement.index |>.getD 0
  let mu := sh.mu
  let bus := proveBusAndConstraintsWqWithBcCols program iv initInput sized root wq wins bcCols
  let t3 ← IO.monoNanosNow
  let (rss3, _) ← readProcMemBytes
  let stage ← proveKeccakGkrOnlyWq bus executed qBase wq
  let t4 ← IO.monoNanosNow
  let (rss4, _) ← readProcMemBytes
  let ps0 := specStateOf stage.ps
  let points := stackPointsOf stage
  let ring : Spec.Pcs.StackOpen.RingSwitchOpen :=
    ⟨stage.ringClaim.offset, #[⟨stage.ringClaim.suffixPoint, stage.ringClaim.slices⟩]⟩
  let result ← (provePcsOpenFlat ps0 mu logInvRate wq points ring).run
  let ps1 ← match result with
    | some ps => pure ps
    | none => throw (IO.userError "provePcsOpenFlat failed")
  let phases ← decodePhases ps1.merkle
  let claims := signers.map fun record => ⟨record.publicKey, record.message⟩
  unless Model.Aggregate.Wire.signerSetOk ⟨claims, #[]⟩ do
    throw (IO.userError "signer set failed strict order check")
  let eth := ethereumProofOf claims bytecodeValue ⟨ps1.stream, phases⟩
  let seedPair : E × E := (Spec.Xmss.packCell seed, Spec.Xmss.packCell seed 16)
  let wireStatement := scalarPairBytes (Model.Aggregate.Wire.EthereumProof.statement seedPair eth)
  unless bytesEqFast wireStatement statement do
    throw (IO.userError "EthereumProof statement mismatch against workload statement")
  let t5 ← IO.monoNanosNow
  let (rss5, _) ← readProcMemBytes
  let wire := Model.Aggregate.Wire.EthereumProof.toBytesWithoutPubkeys eth
  let t6 ← IO.monoNanosNow
  let (rss6, hwm6) ← readProcMemBytes
  if let some dir := exportDir then
    exportShardFixtures dir iv initInput hints sized root wq bus stage ⟨ps1.stream, phases⟩ wire
  let timings : PhaseTimings := {
    statementHints := t0b - t0
    executeWitness := t1 - t0b
    commitNttMerkle := t2 - t1
    busConstraints := t3 - t2
    keccakGkr := t4 - t3
    pcsOpen := t5 - t4
    wireEncode := t6 - t5
    total := t5 - t0
    vmRssBytes := rss6
    vmHwmBytes := hwm6
    rssStatementHints := rss0b
    rssExecuteWitness := rss1
    rssCommitNttMerkle := rss2
    rssBusConstraints := rss3
    rssKeccakGkr := rss4
    rssPcsOpen := rss5
    rssWireEncode := rss6 }
  let run : VmProvedRun := {
    proof := ⟨ps1.stream, phases⟩
    cycles := traceCycles
    memUsed := traceMemUsed
    memoryKeccak := ByteArray.empty
    stage := stage
    mu := mu }
  return (eth, statement, hints.size, run, wire, timings)

end LeanVmXmss.PcsOpeningDiagnostics

def main (args : List String) : IO Unit := do
  let dir : System.FilePath := ⟨args[0]?.getD ""⟩
  let outPath : System.FilePath := ⟨args[1]?.getD "diag.ethproof"⟩
  let records ← LeanVmXmss.Model.Cli.loadRawInputs (LeanVmXmss.Model.Cli.childPath dir "xmss-inputs.bin")
  let seed ← LeanVmXmss.Model.Cli.loadSeed (LeanVmXmss.Model.Cli.childPath dir "seed.bin")
  let bc ← LeanVmXmss.Model.Cli.loadBytecodeValue (LeanVmXmss.Model.Cli.childPath dir "bytecode-value.bin")
  let (program, frame, schedule) ← LeanVmXmss.Model.Cli.loadGuest dir
  let cols := LeanVmXmss.Model.Layout.bytecodeColumnsFast program
  let iv := LeanVmXmss.Model.Cli.ivOfCols program cols
  let (_, _, _, _, wire, timings) ← LeanVmXmss.PcsOpeningDiagnostics.proveLeafEthereumTimedPass
    program frame schedule seed bc records 1 iv cols
  IO.FS.writeBinFile outPath wire
  IO.println (LeanVmXmss.Model.Cli.phaseTimingsJson 0 timings)
