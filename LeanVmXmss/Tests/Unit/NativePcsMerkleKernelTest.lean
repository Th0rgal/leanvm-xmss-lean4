import Spec.Field.Basic
import Spec.Keccak.Basic
import Spec.Merkle.Basic
import Spec.Pcs.Ntt
import Spec.Pcs.Commit
import Spec.Pcs.Whir
import Model.Pcs.Ntt
import Model.Pcs.Commit
import Model.Pcs.Whir
import Native.Kernels.Ntt
import Native.Kernels.Keccak8x

open LeanVmXmss
open LeanVmXmss.Spec.Field (K E)

#print axioms LeanVmXmss.Native.Kernels.Ntt.usize_lt_size
#print axioms LeanVmXmss.Native.Kernels.Ntt.usize_uset_size
#print axioms LeanVmXmss.Native.Kernels.Ntt.usize_ofNat_le_seven
#print axioms LeanVmXmss.Native.Kernels.Ntt.usize_add_lt_size
#print axioms LeanVmXmss.Native.Kernels.Ntt.loadU64
#print axioms LeanVmXmss.Native.Kernels.Ntt.storeU64
#print axioms LeanVmXmss.Native.Kernels.Ntt.buildTwiddleSlab
#print axioms LeanVmXmss.Native.Kernels.Ntt.butterflyU
#print axioms LeanVmXmss.Native.Kernels.Ntt.butterflyV
#print axioms LeanVmXmss.Native.Kernels.Ntt.whirFoldC0
#print axioms LeanVmXmss.Native.Kernels.Ntt.whirFoldC1
#print axioms LeanVmXmss.Native.Kernels.Ntt.whirFoldC2
#print axioms LeanVmXmss.Native.Kernels.Ntt.lean_xmss_ntt_stage_high
#print axioms LeanVmXmss.Native.Kernels.Ntt.lean_xmss_ntt_tile_low
#print axioms LeanVmXmss.Native.Kernels.Ntt.encodeBytes
#print axioms LeanVmXmss.Native.Kernels.Ntt.encodeCosetBytes
#print axioms LeanVmXmss.Native.Kernels.Ntt.lean_xmss_whir_fold_even_odd
#print axioms LeanVmXmss.Native.Kernels.Ntt.lean_xmss_whir_fold_blocks
#print axioms LeanVmXmss.Native.Kernels.Ntt.lean_xmss_whir_fold_batch
#print axioms LeanVmXmss.Native.Kernels.Ntt.lean_xmss_whir_sumcheck_even_odd
#print axioms LeanVmXmss.Native.Kernels.Keccak8x.round25x8
#print axioms LeanVmXmss.Native.Kernels.Keccak8x.rounds25x8
#print axioms LeanVmXmss.Native.Kernels.Keccak8x.keccakF1600_25x8
#print axioms LeanVmXmss.Native.Kernels.Keccak8x.keccakF1600_8x
#print axioms LeanVmXmss.Native.Kernels.Keccak8x.lean_xmss_merkle_compress_level
#print axioms LeanVmXmss.Native.Kernels.Keccak8x.lean_xmss_merkle_hash_leaves
#print axioms LeanVmXmss.Native.Kernels.Keccak8x.lean_xmss_merkle_build_flat
#print axioms LeanVmXmss.Native.Kernels.Keccak8x.lean_xmss_merkle_root_from_flat
#print axioms LeanVmXmss.Native.Kernels.Keccak8x.lean_xmss_merkle_root_from_leaves
#print axioms LeanVmXmss.Native.Kernels.Keccak8x.lean_xmss_pcs_commit_root
#print axioms LeanVmXmss.Native.Kernels.Keccak8x.lean_xmss_pcs_commit_root_parallel

def hexDigit (n : Nat) : Char :=
  let digits : Array Char :=
    #['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f']
  digits.getD (n % 16) '0'

def hexBytes (bytes : ByteArray) : String :=
  String.ofList <|
    Model.Pcs.Ntt.foldRange bytes.size
      (fun acc i =>
        let b := (bytes.data.getD i 0).toNat
        acc ++ [hexDigit (b >>> 4), hexDigit b])
      []

def eqBytes (a b : ByteArray) : Bool :=
  if a.size = b.size then
    Model.Pcs.Ntt.foldRange a.size
      (fun ok i => ok && decide ((a.data.getD i 0).toNat = (b.data.getD i 0).toNat))
      true
  else false

def eqWords (a b : Array K) : Bool :=
  if a.size = b.size then
    Model.Pcs.Ntt.foldRange a.size
      (fun ok i => ok && decide ((a.getD i 0).toNat = (b.getD i 0).toNat))
      true
  else false

def eqExt (a b : Array E) : Bool :=
  if a.size = b.size then
    Model.Pcs.Ntt.foldRange a.size
      (fun ok i =>
        let x := a.getD i Spec.Field.zero
        let y := b.getD i Spec.Field.zero
        ok &&
          decide (x.c0.toNat = y.c0.toNat) &&
          decide (x.c1.toNat = y.c1.toNat) &&
          decide (x.c2.toNat = y.c2.toNat))
      true
  else false

def genWords (n : Nat) (seed : UInt64) : Array K :=
  Model.Pcs.Ntt.foldRange n
    (fun acc i =>
      let v := (UInt64.ofNat i + 1) * 0x9e3779b97f4a7c15 + seed * 0xbf58476d1ce4e5b9
      acc.push v)
    (Array.emptyWithCapacity n)

def genExt (n : Nat) (seed : UInt64) : Array E :=
  Model.Pcs.Ntt.foldRange n
    (fun acc i =>
      let base := UInt64.ofNat i + 1 + seed * 131
      acc.push
        ⟨base * 0x9e3779b97f4a7c15 + 1,
         base * 0xbf58476d1ce4e5b9 + 3,
         base * 0x94d049bb133111eb + 7⟩)
    (Array.emptyWithCapacity n)

def assertCond (label : String) (cond : Bool) : IO Unit := do
  if !cond then
    throw (IO.userError ("FAIL: " ++ label))

def testKeccak8xPerm : IO Unit := do
  let states : Array Model.Keccak.State25 :=
    Model.Pcs.Ntt.foldRange 8
      (fun acc k =>
        let ws := genWords 25 (UInt64.ofNat (k + 10))
        acc.push
          ⟨ws.getD 0 0, ws.getD 1 0, ws.getD 2 0, ws.getD 3 0, ws.getD 4 0,
           ws.getD 5 0, ws.getD 6 0, ws.getD 7 0, ws.getD 8 0, ws.getD 9 0,
           ws.getD 10 0, ws.getD 11 0, ws.getD 12 0, ws.getD 13 0, ws.getD 14 0,
           ws.getD 15 0, ws.getD 16 0, ws.getD 17 0, ws.getD 18 0, ws.getD 19 0,
           ws.getD 20 0, ws.getD 21 0, ws.getD 22 0, ws.getD 23 0, ws.getD 24 0⟩)
      #[]
  let expected : Array (Array UInt64) :=
    states.map (fun s => (Model.Keccak.keccakF1600 s).toSpec)
  let interleaved :=
    Model.Pcs.Ntt.foldRange 25
      (fun acc lane =>
        Model.Pcs.Ntt.foldRange 8
          (fun acc2 k =>
            let stVec := (states.getD k Native.Kernels.Keccak8x.zeroState25).toSpec
            Native.Kernels.Ntt.pushU64LE acc2 (stVec.getD lane 0))
          acc)
      (ByteArray.emptyWithCapacity 1600)
  let outBytes := Native.Kernels.Keccak8x.keccakF1600_8x interleaved
  let ok :=
    Model.Pcs.Ntt.foldRange 25
      (fun ok1 lane =>
        Model.Pcs.Ntt.foldRange 8
          (fun ok2 k =>
            let got := Native.Kernels.Ntt.loadU64 outBytes (USize.ofNat ((lane * 8 + k) * 8))
            let exp := (expected.getD k #[]).getD lane 0
            ok2 && decide (got.toNat = exp.toNat))
          ok1)
      true
  assertCond "keccakF1600_8x vs Model.Keccak.keccakF1600" ok
  IO.println "PASS|keccakF1600_8x"

def testNttDifferential : IO Unit := do
  for logD in [4, 12, 14] do
    let lanesList := if logD = 4 then [1, 3, 8, 13, 16, 24] else [8, 16]
    for lanes in lanesList do
      for startLayer in [0, 1] do
        let rows := 1 <<< logD
        let words := genWords (rows * lanes) (UInt64.ofNat (logD * 100 + lanes + startLayer))
        let refOut :=
          if logD = 4 then Spec.Pcs.Ntt.encode words lanes startLayer
          else Model.Pcs.Ntt.encode words lanes startLayer
        let inBytes := Native.Kernels.Ntt.packWordsLE words
        let gotBytes := Native.Kernels.Ntt.encodeBytes inBytes lanes startLayer
        let gotWords := Native.Kernels.Ntt.unpackWordsLE gotBytes
        assertCond s!"NTT logD={logD} lanes={lanes} start={startLayer}" (eqWords refOut gotWords)
  IO.println "PASS|ntt_differential_2^4_2^12_2^14"

def testMerkleDifferential : IO Unit := do
  for logRows in [2, 3, 4, 12, 14] do
    let rows := 1 <<< logRows
    let widths := if logRows ≤ 4 then [8, 16, 24, 56, 64] else [16, 56]
    for width in widths do
      let codeword := genWords (rows * width) (UInt64.ofNat (logRows * 77 + width))
      let cwBytes := Native.Kernels.Ntt.packWordsLE codeword
      let nativeLeaves := Native.Kernels.Keccak8x.lean_xmss_merkle_hash_leaves cwBytes width 64
      let nativeRoot := Native.Kernels.Keccak8x.lean_xmss_merkle_root_from_leaves nativeLeaves
      let flatTree := Native.Kernels.Keccak8x.lean_xmss_merkle_build_flat nativeLeaves
      let flatRoot := Native.Kernels.Keccak8x.lean_xmss_merkle_root_from_flat flatTree
      assertCond s!"Merkle flat root match logRows={logRows} width={width}"
        (eqBytes nativeRoot flatRoot)
      let modelDigests := Model.Pcs.Commit.leafDigests codeword width
      let modelRoot :=
        (Model.Pcs.Commit.subtreeRoot (fun i => modelDigests.getD i default) logRows 0).toBytes
      assertCond s!"Merkle root vs Model logRows={logRows} width={width}"
        (eqBytes nativeRoot modelRoot)
      if logRows ≤ 4 then
        let specLeaves := Spec.Pcs.Commit.leaves codeword width
        let specTree := Spec.Merkle.build specLeaves
        let specRoot := Spec.Merkle.digestBytes (Spec.Merkle.treeRoot specTree)
        assertCond s!"Merkle root vs Spec logRows={logRows} width={width}"
          (eqBytes nativeRoot specRoot)
  for lanes in [1, 7, 8, 16, 32, 51, 64] do
    let msg := genWords (lanes * 16) (UInt64.ofNat (lanes + 900))
    let specRoot := Spec.Pcs.Commit.root msg lanes 4 1
    let nativeRoot :=
      Native.Kernels.Keccak8x.lean_xmss_pcs_commit_root
        (Native.Kernels.Ntt.packWordsLE msg) lanes 4 1
    assertCond s!"PCS commit root vs Spec lanes={lanes}" (eqBytes specRoot nativeRoot)
  IO.println "PASS|merkle_and_pcs_commit_2^4_2^12_2^14"

def testWhirDifferential : IO Unit := do
  for logN in [4, 12, 14] do
    let n := 1 <<< logN
    let xs := genExt n (UInt64.ofNat (logN + 500))
    let bs := genExt n (UInt64.ofNat (logN + 600))
    let pt := genExt 3 (UInt64.ofNat (logN + 700))
    let r0 := pt.getD 0 Spec.Field.zero
    let xsBytes := Native.Kernels.Ntt.packExtLE xs
    let bsBytes := Native.Kernels.Ntt.packExtLE bs
    let ptBytes := Native.Kernels.Ntt.packExtLE pt
    let refFold1 := Model.Pcs.Whir.foldEvenOdd xs r0
    let gotFold1 :=
      Native.Kernels.Ntt.unpackExtLE
        (Native.Kernels.Ntt.lean_xmss_whir_fold_even_odd xsBytes r0.c0 r0.c1 r0.c2)
    assertCond s!"WHIR foldEvenOdd logN={logN}" (eqExt refFold1 gotFold1)
    let refBatch :=
      Model.Pcs.Ntt.foldRange pt.size
        (fun cur k => Model.Pcs.Whir.foldEvenOdd cur (pt.getD k Spec.Field.zero))
        xs
    let gotBatch :=
      Native.Kernels.Ntt.unpackExtLE
        (Native.Kernels.Ntt.lean_xmss_whir_fold_batch xsBytes ptBytes)
    assertCond s!"WHIR foldBatch logN={logN}" (eqExt refBatch gotBatch)
    if logN = 4 then
      let specBatch :=
        Model.Pcs.Ntt.foldRange pt.size
          (fun cur k => Spec.Pcs.Whir.foldEvenOdd cur (pt.getD k Spec.Field.zero))
          xs
      assertCond "WHIR foldBatch vs Spec 2^4" (eqExt specBatch gotBatch)
    for blk in [1, 4, 7] do
      let refBlk := Model.Pcs.Whir.foldBlocks blk xs r0
      let gotBlk :=
        Native.Kernels.Ntt.unpackExtLE
          (Native.Kernels.Ntt.lean_xmss_whir_fold_blocks blk xsBytes r0.c0 r0.c1 r0.c2)
      assertCond s!"WHIR foldBlocks logN={logN} blk={blk}" (eqExt refBlk gotBlk)
    let (u0Ref, u2Ref) := Model.Pcs.Whir.sumcheckMsgEvenOdd xs bs
    let scBytes := Native.Kernels.Ntt.lean_xmss_whir_sumcheck_even_odd xsBytes bsBytes
    let scArr := Native.Kernels.Ntt.unpackExtLE scBytes
    assertCond s!"WHIR sumcheckEvenOdd logN={logN}" (eqExt #[u0Ref, u2Ref] scArr)
  IO.println "PASS|whir_fold_and_sumcheck_2^4_2^12_2^14"

def runBenchmarks : IO Unit := do
  let nttWords14 ← IO.lazyPure (fun () =>
    Native.Kernels.Ntt.packWordsLE (genWords ((1 <<< 14) * 56) 0x1234))
  let t0 ← IO.monoNanosNow
  let nttOut14 ← IO.lazyPure (fun () => Native.Kernels.Ntt.encodeBytes nttWords14 56 0)
  let t1 ← IO.monoNanosNow
  let nttUs14 := (t1 - t0) / 1000
  IO.println s!"BENCH|ntt_encode_2^14x56_us={nttUs14}|bytes={nttOut14.size}"

  let t2 ← IO.monoNanosNow
  let leaves14 ← IO.lazyPure (fun () =>
    Native.Kernels.Keccak8x.lean_xmss_merkle_hash_leaves nttOut14 56 64)
  let t3 ← IO.monoNanosNow
  let leavesUs14 := (t3 - t2) / 1000
  IO.println s!"BENCH|merkle_leaves_8x_2^14x56_us={leavesUs14}|bytes={leaves14.size}"

  let t4 ← IO.monoNanosNow
  let flatTree14 ← IO.lazyPure (fun () =>
    Native.Kernels.Keccak8x.lean_xmss_merkle_build_flat leaves14)
  let t5 ← IO.monoNanosNow
  let treeUs14 := (t5 - t4) / 1000
  let root14 := Native.Kernels.Keccak8x.lean_xmss_merkle_root_from_flat flatTree14
  IO.println s!"BENCH|merkle_flat_8x_2^14_us={treeUs14}|root={hexBytes root14}"

  let whirIn14 ← IO.lazyPure (fun () =>
    Native.Kernels.Ntt.packExtLE (genExt (1 <<< 14) 0x5678))
  let whirPt4 ← IO.lazyPure (fun () =>
    Native.Kernels.Ntt.packExtLE (genExt 4 0x9abc))
  let t6 ← IO.monoNanosNow
  let whirOut14 ← IO.lazyPure (fun () =>
    Native.Kernels.Ntt.lean_xmss_whir_fold_batch whirIn14 whirPt4)
  let t7 ← IO.monoNanosNow
  let whirUs14 := (t7 - t6) / 1000
  IO.println s!"BENCH|whir_fold_batch_2^14_4rounds_us={whirUs14}|bytes={whirOut14.size}"

  let msg15 ← IO.lazyPure (fun () =>
    Native.Kernels.Ntt.packWordsLE (genWords ((1 <<< 15) * 51) 0xdef0))
  let t8 ← IO.monoMsNow
  let commit15 ← IO.lazyPure (fun () =>
    Native.Kernels.Keccak8x.lean_xmss_pcs_commit_root msg15 51 15 1)
  let t9 ← IO.monoMsNow
  IO.println s!"BENCH|pcs_commit_1thread_log15_lanes51_ms={t9 - t8}|root={hexBytes commit15}"

  let t10 ← IO.monoMsNow
  let parRoot ← IO.lazyPure (fun () =>
    Native.Kernels.Keccak8x.lean_xmss_pcs_commit_root_parallel msg15 51 15 1)
  let t11 ← IO.monoMsNow
  assertCond "parallel 16-core commit root parity" (eqBytes commit15 parRoot)
  IO.println s!"BENCH|pcs_commit_16core_log15_lanes51_ms={t11 - t10}|root={hexBytes parRoot}"

def main : IO Unit := do
  testKeccak8xPerm
  testNttDifferential
  testMerkleDifferential
  testWhirDifferential
  runBenchmarks
  IO.println "ALL_TESTS_PASSED"
