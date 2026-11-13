import Model.Pcs.FlatWhir

open LeanVmXmss
open LeanVmXmss.Spec.Field (K)
open LeanVmXmss.Model.Pcs.Ntt (Vec8 foldRange)
open LeanVmXmss.Model.Pcs.FlatWhir

namespace PcsOpeningBatchTest

def assertOk (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)

def word (pattern i : Nat) : UInt64 :=
  match pattern with
  | 0 => 0
  | 1 => 0xffffffffffffffff
  | 2 => (0x8000000000000000 : UInt64) ^^^ UInt64.ofNat i
  | _ => (UInt64.ofNat i + 1) * 0x9e3779b97f4a7c15

def vectors (pattern n : Nat) : Array Vec8 :=
  (Array.range n).map fun i =>
    ⟨word pattern (8*i), word pattern (8*i+1), word pattern (8*i+2),
     word pattern (8*i+3), word pattern (8*i+4), word pattern (8*i+5),
     word pattern (8*i+6), word pattern (8*i+7)⟩

-- Frozen scalar opening: only the unqueried-subtree callback differs from production.
def openScalar (bytes : @& ByteArray) (lanes logRows logInvRate : Nat)
    (queries : @& Array Nat) : Option Spec.Merkle.PrunedMerklePaths := do
  let blockLog := logRows + logInvRate
  let indices := Spec.Merkle.sortedUnique queries
  if !Spec.Merkle.validIndices blockLog indices then none
  else
    let width := Spec.Pcs.Commit.rowWords lanes
    let nVecs := width / 8
    let table := Model.Pcs.Ntt.evals blockLog
    let st1 := Model.Pcs.Commit.zeroPrefixState 1
    let st2 := Model.Pcs.Commit.zeroPrefixState 2
    let st3 := Model.Pcs.Commit.zeroPrefixState 3
    let subK := min logRows 10
    streamCosetsOpen (1 <<< logInvRate) logRows subK blockLog indices
      (fun curC =>
        let first := firstCosetFromBytes bytes lanes nVecs logRows
        Model.Pcs.Ntt.encodeCosetVec8 table first nVecs logRows logInvRate curC)
      (fun encoded loc => extractL0Row encoded lanes width nVecs loc)
      (fun encoded loc => Model.Pcs.Commit.hashLeafVec8From st1 st2 st3 encoded nVecs loc)
      (fun encoded k base => Model.Pcs.Commit.subtreeRootBuf st1 st2 st3 encoded nVecs k base)

def samePaths (a b : Option Spec.Merkle.PrunedMerklePaths) : Bool :=
  match a, b with
  | none, none => true
  | some x, some y => putPhaseBytesFast x == putPhaseBytesFast y
  | _, _ => false

def roots : IO Unit := do
  let st1 := Model.Pcs.Commit.zeroPrefixState 1
  let st2 := Model.Pcs.Commit.zeroPrefixState 2
  let st3 := Model.Pcs.Commit.zeroPrefixState 3
  for nVecs in [0,1,2,3,4,5,6,7,8,9] do
    for k in [0,1,3,4,10,11] do
      for pattern in [0,1,2,3] do
        let rows := 1 <<< k
        -- Both exact and truncated buffers exercise the model's default reads.
        for missing in [0,3] do
          let encoded := vectors pattern ((rows + 3) * nVecs - missing)
          for base in [0,3] do
            let ref := Model.Pcs.Commit.subtreeRootBuf st1 st2 st3 encoded nVecs k base
            let got := Model.Pcs.MerkleBatch.subtreeRootBuf st1 st2 st3 encoded nVecs k base
            assertOk s!"root nVecs={nVecs} k={k} pattern={pattern} base={base} missing={missing}"
              (ref.toBytesFast == got.toBytesFast)
  IO.println "PASS|subtree_roots_widths_padding_highbits_defaults_fallbacks"

def packing : IO Unit := do
  for nVecs in [0,1,7,8,9] do
    for rows in [0,4,1025] do
      for pattern in [0,1,2,3] do
        let encoded := vectors pattern (5*nVecs-1)
        let packed := Model.Pcs.MerkleBatch.packVec8Rows encoded nVecs 2 rows
        let reference := Model.Pcs.MerkleBatch.packVec8RowsPush encoded nVecs 2 rows
        assertOk "complete bytes vs original push packer, including large fallback"
          (packed == reference)
        assertOk "packed byte count" (packed.size == rows*nVecs*64)
        for i in [:rows*nVecs] do
          let v := encoded.getD (2*nVecs+i) default
          for lane in [:8] do
            let w := Native.Kernels.Ntt.loadU64 packed (USize.ofNat (i*64+lane*8))
            assertOk "packed lane order / zero tail / template isolation" (w == v.lane lane)
  IO.println "PASS|packed_all_lanes_zero_tail_template_isolation_and_large_fallback"

def paths : IO Unit := do
  for lanes in [1,7,8,9,16,37,51,56,64,65] do
    for logRows in [0,3,4,11] do
      let rows := 1 <<< logRows
      let bytes := foldRange (lanes*rows) (fun b i =>
        Native.Kernels.Ntt.pushU64LE b (word 3 i)) ByteArray.empty
      for rate in [1,2] do
        let total := rows <<< rate
        for qs in [#[], #[0], #[total-1], #[0,rows-1,rows,total-1,rows,0],
                   #[1,0], #[total], #[0,total]] do
          assertOk s!"complete paths lanes={lanes} logRows={logRows} rate={rate} queries={qs}"
            (samePaths (openScalar bytes lanes logRows rate qs)
              (openL0Cosets bytes lanes logRows rate qs))
  IO.println "PASS|complete_pruned_rows_ordered_siblings_duplicates_boundaries_invalid_queries"

end PcsOpeningBatchTest

def main : IO Unit := do
  PcsOpeningBatchTest.packing
  PcsOpeningBatchTest.roots
  PcsOpeningBatchTest.paths
  IO.println "ALL_PCS_OPENING_BATCH_TESTS_PASSED"
