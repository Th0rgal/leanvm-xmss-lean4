import Model.Pcs.Ntt
import Model.Pcs.Commit
import Model.Keccak.Simd8

namespace LeanVmXmss.Model.Pcs.CommitSlab

open Spec.Field (K)
open Model.Pcs.Ntt (Vec8 foldRange foldRangeLoop evals rowFromEvals twiddleFromRow butterflyVec8U butterflyVec8V)
open Model.Merkle (Digest32)
open Model.Keccak.Simd8 (State25x8 bcastState25 KeccakWs8 mkKeccakWs8 Digests8 hash8LeavesFastWs hash8PairsWs)

/-- Retained L0 state produced by Phase 2 (`commitL0Slab`) for zero-recompute opening in Phase 5.
    Holds `2^numSubtreesLog` sub-slabs of `2^subLog` rows (`nVecs` `Vec8`s per row) and their
    subtree Merkle levels (`subLog + 1` levels per subtree), plus the top levels `subLog .. logD`. -/
structure RetainedL0 where
  lanes : Nat
  nVecs : Nat
  logRows : Nat
  logInvRate : Nat
  logD : Nat
  subLog : Nat
  subSlabs : Array (Array Vec8)
  subTrees : Array (Array (Array Digest32))
  topLevels : Array (Array Digest32)
  root : Digest32
  deriving Inhabited

@[inline] def readMsgRowColVec (message : Array K) (lanes width rows rowIdx curV : Nat) : Vec8 :=
  let base := 8 * curV
  let word (j : Nat) : K :=
    let col := base + j
    if decide (col + lanes ≥ width) then
      message.getD ((width - 1 - col) * rows + rowIdx) 0
    else 0
  ⟨word 0, word 1, word 2, word 3, word 4, w

@[inline] def fillGroupRowLoop (message : Array K) (lanes width nVecs rows baseRow step : Nat)
    (rem i : Nat) (grp : Array Vec8) : Array Vec8 :=
  foldRangeLoop (fun grp curI =>
    let rowIdx := baseRow + curI * step
    foldRangeLoop (fun grp curV =>
      grp.setIfInBounds (curI * nVecs + curV) (readMsgRowColVec message lanes width rows rowIdx curV))
      nVecs 0 grp)
    rem i grp

/-- Run layers `logInvRate .. deepStart - 1` (`g = deepStart - logInvRate` layers) inside a tiny
    `2^g`-row `Vec8` scratch group representing coset `coset` (`block = coset <<< localStep + b`). -/
def transformGroupLayers (twiddleRows : Array (Array K)) (nVecs g coset : Nat)
    (src : Array Vec8) (scratch : Array Vec8) : Array Vec8 :=
  let scratch := foldRange src.size (fun sc idx => sc.setIfInBounds idx (src.getD idx default)) scratch
  foldRange g (fun sc s =>
    let localBlocks := 1 <<< s
    let half := 1 <<< (g - 1 - s)
    let values := twiddleRows.getD s #[]
    let blockBase := coset <<< s
    foldRange localBlocks (fun sc lb =>
      let t := twiddleFromRow values (blockBase + lb)
      let rowBase := lb * (2 * half)
      foldRange half (fun sc r =>
        let topBase := (rowBase + r) * nVecs
        let botBase := topBase + half * nVecs
        foldRange nVecs (fun sc v =>
          let topIdx := topBase + v
          let botIdx := botBase + v
          let topV := sc.getD topIdx default
          let botV := sc.getD botIdx default
          let sc := sc.setIfInBounds topIdx default
          let sc := sc.setIfInBounds botIdx default
          let uV := butterflyVec8U topV botV t
          let vV := butterflyVec8V botV uV
          (sc.setIfInBounds topIdx uV).setIfInBounds botIdx vV) sc) sc) sc)
    scratch

/-- Build one residue shard (`resLo .. resHi`) across all `2^(g + logInvRate)` sub-blocks.
    Each task writes a compact flat `Array Vec8` of shape `[numSubs][resCount][nVecs]`,
    reading `message` once per residue and transforming all `rate` cosets in L1/L2 cache! -/
def runGatheredShard (message : Array K) (twiddleRows : Array (Array K))
    (lanes nVecs logRows logInvRate g resLo resCount : Nat) : Array Vec8 :=
  let rows := 1 <<< logRows
  let width := 8 * nVecs
  let rate := 1 <<< logInvRate
  let groupRows := 1 <<< g
  let step := 1 <<< (logRows - g)
  let numSubs := rate * groupRows
  let grpInit : Array Vec8 := Array.replicate (groupRows * nVecs) default
  let scInit : Array Vec8 := Array.replicate (groupRows * nVecs) default
  let outInit : Array Vec8 := Array.replicate (numSubs * resCount * nVecs) default
  let (_, _, out) :=
    foldRange resCount (fun (grp, sc, out) rOff =>
      let res := resLo + rOff
      let grp := fillGroupRowLoop message lanes width nVecs rows res step groupRows 0 grp
      foldRange rate (fun (grp, sc, out) c =>
        let sc := transformGroupLayers twiddleRows nVecs g c grp sc
        let out :=
          foldRange groupRows (fun out i =>
            let subIdx := c * groupRows + i
            let dstBase := (subIdx * resCount + rOff) * nVecs
            let srcBase := i * nVecs
            foldRange nVecs (fun out v =>
              out.setIfInBounds (dstBase + v) (sc.getD (srcBase + v) default)) out) out
        (grp, sc, out)) (grp, sc, out))
      (grpInit, scInit, outInit)
  out

/-- Assemble sub-block `subIdx` (`subRows = 2^subLog` rows) from the `nShards` gathered shards,
    then run the deep NTT layers `deepStart .. logD - 1` in place in L2 cache! -/
def assembleAndDeepSubBlock (shards : Array (Array Vec8)) (resPerShard : Nat)
    (deepTwiddleRows : Array (Array K)) (nVecs subLog deepStart subIdx : Nat) : Array Vec8 :=
  let subRows := 1 <<< subLog
  let totalVecs := subRows * nVecs
  let buf : Array Vec8 := Array.emptyWithCapacity totalVecs
  let buf :=
    foldRange shards.size (fun buf shIdx =>
      let sh := shards.getD shIdx #[]
      let rCount := min resPerShard (subRows - min subRows (shIdx * resPerShard))
      let srcStart := subIdx * resPerShard * nVecs
      foldRange (rCount * nVecs) (fun buf k =>
        buf.push (sh.getD (srcStart + k) default)) buf) buf
  foldRange subLog (fun data dStep =>
    let localBlocks := 1 <<< dStep
    let half := 1 <<< (subLog - 1 - dStep)
    let values := deepTwiddleRows.getD dStep #[]
    let blockBase := subIdx <<< dStep
    foldRange localBlocks (fun data lb =>
      let t := twiddleFromRow values (blockBase + lb)
      let blockRowBase := lb * (2 * half)
      Model.Pcs.Ntt.rowPairLoop blockRowBase half nVecs t half 0 data) data)
    buf

/-- Hash `subRows` (`2^subLog`, `subLog ≥ 3`) leaves of `buf` 8 at a time using `KeccakWs8`. -/
def hashSubBlockLeaves (st1 st2 st3 : State25x8) (ws : KeccakWs8)
    (buf : Array Vec8) (nVecs subRows : Nat) : Array Digest32 × KeccakWs8 :=
  let groups := subRows / 8
  let leaves := Array.emptyWithCapacity subRows
  let (leaves, ws) :=
    foldRange groups (fun (acc, ws) g =>
      let (d8, ws) := hash8LeavesFastWs st1 st2 st3 ws buf nVecs (g * 8)
      let acc := (((((((acc.push d8.d0).push d8.d1).push d8.d2).push d8.d3).push d8.d4).push d8.d5).push d8.d6).push d8.d7
      (acc, ws)) (leaves, ws)
  let remStart := groups * 8
  let s1 := Model.Pcs.Commit.zeroPrefixState 1
  let s2 := Model.Pcs.Commit.zeroPrefixState 2
  let s3 := Model.Pcs.Commit.zeroPrefixState 3
  let leaves :=
    foldRange (subRows - remStart) (fun acc k =>
      acc.push (Model.Pcs.Commit.hashLeafVec8From s1 s2 s3 buf nVecs (remStart + k))) leaves
  (leaves, ws)

/-- Compress one Merkle level using 8-way `hash8PairsWs` when `nodes.size ≥ 16`, falling back to scalar `hashPair25` for the tail. -/
def compressLevelSimd8 (ws : KeccakWs8) (nodes : Array Digest32) : Array Digest32 × KeccakWs8 :=
  let pairs := nodes.size / 2
  let groups := pairs / 8
  let out := Array.emptyWithCapacity pairs
  let (out, ws) :=
    foldRange groups (fun (acc, ws) g =>
      let b := g * 16
      let (d8, ws) :=
        if h : b + 16 ≤ nodes.size then
          hash8PairsWs ws
            nodes[b + 0]  nodes[b + 1]  nodes[b + 2]  nodes[b + 3]
            nodes[b + 4]  nodes[b + 5]  nodes[b + 6]  nodes[b + 7]
            nodes[b + 8]  nodes[b + 9]  nodes[b + 10] nodes[b + 11]
            nodes[b + 12] nodes[b + 13] nodes[b + 14] nodes[b + 15]
        else
          hash8PairsWs ws
            (nodes.getD (b + 0) default)  (nodes.getD (b + 1) default)
            (nodes.getD (b + 2) default)  (nodes.getD (b + 3) default)
            (nodes.getD (b + 4) default)  (nodes.getD (b + 5) default)
            (nodes.getD (b + 6) default)  (nodes.getD (b + 7) default)
            (nodes.getD (b + 8) default)  (nodes.getD (b + 9) default)
            (nodes.getD (b + 10) default) (nodes.getD (b + 11) default)
            (nodes.getD (b + 12) default) (nodes.getD (b + 13) default)
            (nodes.getD (b + 14) default) (nodes.getD (b + 15) default)
      let acc := (((((((acc.push d8.d0).push d8.d1).push d8.d2).push d8.d3).push d8.d4).push d8.d5).push d8.d6).push d8.d7
      (acc, ws)) (out, ws)
  let remPairs := pairs - groups * 8
  let out :=
    foldRange remPairs (fun acc k =>
      let i := groups * 8 + k
      acc.push (Model.Pcs.Commit.hashPair25 (nodes.getD (2 * i) default) (nodes.getD (2 * i + 1) default))) out
  (out, ws)

/-- Build all `depth + 1` Merkle levels (`level 0 = leaves`, ..., `level depth = #[root]`) on `ws`. -/
def buildSubtreeLevels (ws : KeccakWs8) (depth : Nat) (leaves : Array Digest32)
    : Array (Array Digest32) × KeccakWs8 :=
  let initLevels := (Array.emptyWithCapacity (depth + 1)).push leaves
  let (levels, _, ws) :=
    foldRange depth (fun (lvls, cur, ws) _ =>
      let (next, ws) := compressLevelSimd8 ws cur
      (lvls.push next, next, ws)) (initLevels, leaves, ws)
  (levels, ws)

/-- Fallback small-domain L0 commit (`logRows < 10` or `lanes > 64`): builds single-sub-tree `RetainedL0`. -/
def commitL0Small (message : Array K) (lanes logRows logInvRate : Nat) : ByteArray × RetainedL0 :=
  let width := Spec.Pcs.Commit.rowWords lanes
  let nVecs := width / 8
  let logD := logRows + logInvRate
  if decide (1 ≤ lanes ∧ lanes ≤ 64) then
    let table := evals logD
    let first := Model.Pcs.Commit.firstCosetVec8 message lanes nVecs logRows
    let rate := 1 <<< logInvRate
    let st1 := bcastState25 (Model.Pcs.Commit.zeroPrefixState 1)
    let st2 := bcastState25 (Model.Pcs.Commit.zeroPrefixState 2)
    let st3 := bcastState25 (Model.Pcs.Commit.zeroPrefixState 3)
    let ws := mkKeccakWs8 0
    let (slabs, trees, roots, _) :=
      foldRange rate (fun (slabs, trees, roots, ws) c =>
        let enc := Model.Pcs.Ntt.encodeCosetVec8 table first nVecs logRows logInvRate c
        let (leaves, ws) := hashSubBlockLeaves st1 st2 st3 ws enc nVecs (1 <<< logRows)
        let (lvls, ws) := buildSubtreeLevels ws logRows leaves
        let r := (lvls.getD logRows #[]).getD 0 default
        (slabs.push enc, trees.push lvls, roots.push r, ws))
        (#[], #[], #[], ws)
    let (topLvls, _) := buildSubtreeLevels (mkKeccakWs8 1) logInvRate roots
    let root := (topLvls.getD logInvRate #[]).getD 0 default
    (root.toBytes, ⟨lanes, nVecs, logRows, logInvRate, logD, logRows, slabs, trees, topLvls, root⟩)
  else
    let rootBytes := Spec.Pcs.Commit.root message lanes logRows logInvRate
    let root := (Digest32.fromBytes rootBytes).getD default
    (rootBytes, ⟨lanes, nVecs, logRows, logInvRate, logD, logRows, #[], #[], #[], root⟩)

/-- Parallel 16-task slab L0 commitment + Merkle tree construction.
    For `xmss1400` (`lanes = 51`, `logRows = 21`, `logInvRate = 1`, `logD = 22`):
    - Chooses `g = min (logRows - 6) (max 4 (logRows - 11))` so `subLog = logRows - g = 11` (`2048` rows = `896 KB`, fits Zen 5 1 MiB L2!).
    - Phase 2A: 16 tasks run `runGatheredShard` over disjoint residue ranges (`resCount = 128` each).
    - Phase 2B: 16 tasks run `assembleAndDeepSubBlock` + `hashSubBlockLeaves` + `buildSubtreeLevels` on `4` sub-blocks each (`64` sub-blocks total), keeping `KeccakWs8` zero-allocation per worker!
    - Phase 2C: climbs the top `g + logInvRate = 11` levels (`2048` subtree roots) using `buildSubtreeLevels`. -/
def commitL0Slab (message : Array K) (lanes logRows logInvRate : Nat) (nWorkers : Nat := 16)
    : ByteArray × RetainedL0 :=
  let width := Spec.Pcs.Commit.rowWords lanes
  let nVecs := width / 8
  let logD := logRows + logInvRate
  if decide (1 ≤ lanes ∧ lanes ≤ 64 ∧ logRows ≥ 10) then
    let subLog := min 11 (logRows - 4)
    let g := logRows - subLog
    let deepStart := logInvRate + g
    let table := evals logD
    let gTwiddles := (Array.range g).map fun s =>
      let layer := logInvRate + s
      rowFromEvals table logD (logD - layer - 1)
    let dTwiddles := (Array.range subLog).map fun dStep =>
      let layer := deepStart + dStep
      rowFromEvals table logD (logD - layer - 1)
    let step := 1 <<< subLog
    let resPerShard := (step + nWorkers - 1) / nWorkers
    let shardTasks := (Array.range nWorkers).map fun w =>
      Task.spawn fun _ =>
        let rLo := min step (w * resPerShard)
        let rCnt := min resPerShard (step - rLo)
        runGatheredShard message gTwiddles lanes nVecs logRows logInvRate g rLo rCnt
    let shards := shardTasks.map Task.get
    let numSubs := (1 <<< logInvRate) * (1 <<< g)
    let subsPerWorker := (numSubs + nWorkers - 1) / nWorkers
    let st1 := bcastState25 (Model.Pcs.Commit.zeroPrefixState 1)
    let st2 := bcastState25 (Model.Pcs.Commit.zeroPrefixState 2)
    let st3 := bcastState25 (Model.Pcs.Commit.zeroPrefixState 3)
    let subRows := 1 <<< subLog
    let deepTasks := (Array.range nWorkers).map fun w =>
      Task.spawn fun _ =>
        let sLo := min numSubs (w * subsPerWorker)
        let sCnt := min subsPerWorker (numSubs - sLo)
        let ws := mkKeccakWs8 w
        let (locSlabs, locTrees, locRoots, _) :=
          foldRange sCnt (fun (slabs, trees, roots, ws) k =>
            let subIdx := sLo + k
            let slab := assembleAndDeepSubBlock shards resPerShard dTwiddles nVecs subLog deepStart subIdx
            let (leaves, ws) := hashSubBlockLeaves st1 st2 st3 ws slab nVecs subRows
            let (lvls, ws) := buildSubtreeLevels ws subLog leaves
            let r := (lvls.getD subLog #[]).getD 0 default
            (slabs.push slab, trees.push lvls, roots.push r, ws))
            (Array.emptyWithCapacity sCnt, Array.emptyWithCapacity sCnt, Array.emptyWithCapacity sCnt, ws)
        (locSlabs, locTrees, locRoots)
    let (subSlabs, subTrees, subRoots) :=
      deepTasks.foldl (fun (allS, allT, allR) t =>
        let (ls, lt, lr) := t.get
        (allS ++ ls, allT ++ lt, allR ++ lr))
        (Array.emptyWithCapacity numSubs, Array.emptyWithCapacity numSubs, Array.emptyWithCapacity numSubs)
    let topDepth := logInvRate + g
    let (topLevels, _) := buildSubtreeLevels (mkKeccakWs8 0) topDepth subRoots
    let root := (topLevels.getD topDepth #[]).getD 0 default
    (root.toBytes, ⟨lanes, nVecs, logRows, logInvRate, logD, subLog, subSlabs, subTrees, topLevels, root⟩)
  else
    commitL0Small message lanes logRows logInvRate

/-- Convert `Digest32` directly to `Spec.Merkle.Digest` (`Vector UInt8 32`). -/
def digestOfDigest32 (d : Digest32) : Spec.Merkle.Digest :=
  Spec.Merkle.toDigest d.toBytes

/-- Fetch node `idx` at `level` (`0 ≤ level ≤ retained.logD`) from `RetainedL0` in O(1)! -/
@[inline] def getNodeAt (ret : RetainedL0) (level idx : Nat) : Digest32 :=
  if decide (level < ret.subLog) then
    let shift := ret.subLog - level
    let subIdx := idx >>> shift
    let localIdx := idx &&& ((1 <<< shift) - 1)
    ((ret.subTrees.getD subIdx #[]).getD level #[]).getD localIdx default
  else
    let topLvl := level - ret.subLog
    (ret.topLevels.getD topLvl #[]).getD idx default

/-- Extract one opened L0 row of width `lanes` (`(width - lanes)..width`) at codeword index `pos` in O(`lanes`)! -/
def getRowAt (ret : RetainedL0) (pos : Nat) : Array K :=
  let subIdx := pos >>> ret.subLog
  let localRow := pos &&& ((1 <<< ret.subLog) - 1)
  let slab := ret.subSlabs.getD subIdx #[]
  let width := 8 * ret.nVecs
  let pad := width - ret.lanes
  let rowBase := localRow * ret.nVecs
  let out := Array.emptyWithCapacity ret.lanes
  foldRange ret.lanes (fun out k =>
    let col := pad + k
    let v := slab.getD (rowBase + col / 8) default
    out.push (v.lane (col % 8))) out

/-- Prune one level of `RetainedL0` directly without materializing a full-domain `Array Digest`! -/
def pruneRetainedLevel (ret : RetainedL0) (level : Nat) (active : List Nat)
    : List Nat × Array Spec.Merkle.Digest :=
  active.zipIdx.foldr (fun (p, i) previous skip =>
    let rest := active.drop (i + 1)
    if skip then previous false else
      if rest.head? = some (p ^^^ 1) then
        let tail := previous true
        (p / 2 :: tail.1, tail.2)
      else
        let tail := previous false
        let sib := digestOfDigest32 (getNodeAt ret level (p ^^^ 1))
        (p / 2 :: tail.1, #[sib] ++ tail.2)) (fun _ => ([], #[])) false

/-- Open `queries` directly from `RetainedL0` in microseconds with zero NTT re-encoding and zero leaf hashing! -/
def openRetainedL0 (ret : RetainedL0) (queries : Array Nat) : Option Spec.Merkle.PrunedMerklePaths := do
  let depth := ret.logD
  let indices := Spec.Merkle.sortedUnique queries
  if !Spec.Merkle.validIndices depth indices then none else
    let openedRows := indices.map (getRowAt ret)
    let siblings :=
      ((Array.range depth).foldl (fun (acc, active) level =>
        let step := pruneRetainedLevel ret level active
        (acc ++ step.2, step.1)) (#[], indices.toList)).1
    some ⟨openedRows, siblings⟩

end LeanVmXmss.Model.Pcs.CommitSlab
