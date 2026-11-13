import Model.Pcs.FlatWhir

open LeanVmXmss
open LeanVmXmss.Model.Pcs.Ntt (Vec8)
open LeanVmXmss.Model.Pcs.FlatWhir

namespace ExtOpeningBatchTest

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

def samePaths (a b : Option Spec.Merkle.PrunedMerklePaths) : Bool :=
  match a, b with
  | none, none => true
  | some x, some y => putPhaseBytesFast x == putPhaseBytesFast y
  | _, _ => false


def openScalar (prep : @& ExtPrepared) (queries : @& Array Nat) :
    Option Spec.Merkle.PrunedMerklePaths := do
  let blockLog := prep.logRows + prep.logInvRate
  let indices := Spec.Merkle.sortedUnique queries
  if !Spec.Merkle.validIndices blockLog indices then none
  else
    let width := 3 * (1 <<< prep.logNumInterleaved)
    let nVecs := (width + 7) / 8
    let table := Model.Pcs.Ntt.evals blockLog
    streamCosetsOpen (1 <<< prep.logInvRate) prep.logRows (min prep.logRows 10) blockLog indices
      (fun c => Model.Pcs.Ntt.encodeCosetVec8 table prep.first nVecs prep.logRows prep.logInvRate c)
      (fun encoded loc => extractExtRow encoded width nVecs loc)
      (fun encoded loc => hashLeafExtVec8 encoded width nVecs loc)
      (fun encoded k base => subtreeRootExtVec8 encoded width nVecs k base)

def leaves : IO Unit := do
  for pattern in [0,1,2,3] do
    for rows in [0,1,7,8,9,16] do
      for missing in [0,3] do
        let encoded := vectors pattern ((rows+3)*6-missing)
        let bytes := Model.Pcs.MerkleBatch.packVec8Rows encoded 6 0 (rows+3)
        for base in [0,3] do
          let hashes := Native.Kernels.KeccakExt48.hashLeaves bytes base rows
          assertOk "48-word leaf output length" (hashes.size == rows*32)
          for i in [:rows] do
            assertOk s!"48-word exact leaf pattern={pattern} rows={rows} base={base} i={i}"
              (hashes.extract (i*32) ((i+1)*32) == (hashLeafExtVec8 encoded 48 6 (base+i)).toBytesFast)
  IO.println "PASS|48_word_leaves_all_lanes_zero_allones_highbits_random_tails"

def roots : IO Unit := do
  for width in [24,48,96] do
    let nVecs := (width+7)/8
    for k in [0,1,3,4,10,11] do
      for pattern in [0,1,2,3] do
        let encoded := vectors pattern (((1 <<< k)+3)*nVecs-3)
        for base in [0,3] do
          assertOk s!"extension subtree width={width} k={k} pattern={pattern} base={base}"
            ((subtreeRootExtVec8 encoded width nVecs k base).toBytesFast ==
             (subtreeRootExtVec8Batch encoded width nVecs k base).toBytesFast)
  IO.println "PASS|48_word_roots_and_format_depth_fallbacks"

def paths : IO Unit := do
  for foldLog in [1,4,5] do
    for logRows in [0,3,4,11] do
      for rate in [1,2] do
        let nVecs := (3*(1 <<< foldLog)+7)/8
        let prep : ExtPrepared := ⟨vectors 3 ((1 <<< logRows)*nVecs),logRows,foldLog,rate⟩
        let total := 1 <<< (logRows+rate)
        for qs in [#[],#[0],#[total-1],#[0,total/2-1,total/2,total-1,0],#[1,0],#[total]] do
          assertOk s!"extension complete paths fold={foldLog} logRows={logRows} rate={rate}"
            (samePaths (openScalar prep qs) (openExtCosets prep qs))
  IO.println "PASS|extension_complete_rows_ordered_siblings_queries_fallbacks"

end ExtOpeningBatchTest

def main : IO Unit := do
  ExtOpeningBatchTest.leaves
  ExtOpeningBatchTest.roots
  ExtOpeningBatchTest.paths
  IO.println "ALL_EXTENSION_OPENING_BATCH_TESTS_PASSED"
