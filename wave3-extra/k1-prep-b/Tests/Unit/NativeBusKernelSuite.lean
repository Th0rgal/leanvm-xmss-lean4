import Model.Bus.Scalar
import Native.Kernels

namespace LeanVmXmss.Tests.Unit

open LeanVmXmss.Spec.Field (K E zero one)
open LeanVmXmss.Model.Prim.Slice64
open LeanVmXmss.Model.Field
open LeanVmXmss.Model.Bus
open LeanVmXmss.Native.Kernels

def eqK (a b : K) : Bool := decide (a.toNat = b.toNat)

def eqE (a b : E) : Bool :=
  eqK a.c0 b.c0 && eqK a.c1 b.c1 && eqK a.c2 b.c2

def eqPairE (a b : E × E) : Bool :=
  eqE a.1 b.1 && eqE a.2 b.2

def eqMsg4 (a b : E × E × E × E) : Bool :=
  eqE a.1 b.1 && eqE a.2.1 b.2.1 && eqE a.2.2.1 b.2.2.1 && eqE a.2.2.2 b.2.2.2

def eqArrayK (xs ys : Array K) : Bool :=
  decide (xs.size = ys.size) &&
  foldNat xs.size
    (fun ok i => ok && eqK (xs[i]?.getD 0) (ys[i]?.getD 0))
    true

def eqArrayE (xs ys : Array E) : Bool :=
  decide (xs.size = ys.size) &&
  foldNat xs.size
    (fun ok i => ok && eqE (xs[i]?.getD zero) (ys[i]?.getD zero))
    true

def eqStateE (xs ys : Array (Array E)) : Bool :=
  decide (xs.size = ys.size) &&
  foldNat xs.size
    (fun ok i => ok && eqArrayE (xs[i]?.getD #[]) (ys[i]?.getD #[]))
    true

def splitmix64 (x : UInt64) : UInt64 :=
  let z := x + 0x9e3779b97f4a7c15
  let z := (z ^^^ (z >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  z ^^^ (z >>> 31)

def genArrayK (n : Nat) (seed : UInt64) : Array K :=
  foldNat n
    (fun acc i => acc.push (splitmix64 (seed + i.toUInt64 * 17)))
    (Array.emptyWithCapacity n)

def genE (seed : UInt64) : E :=
  ⟨splitmix64 seed, splitmix64 (seed + 1), splitmix64 (seed + 2)⟩

def genArrayE (n : Nat) (seed : UInt64) : Array E :=
  foldNat n
    (fun acc i => acc.push (genE (seed + i.toUInt64 * 31)))
    (Array.emptyWithCapacity n)

def unpackStateSlice (st : Array SliceE) : Array (Array E) :=
  foldNat st.size
    (fun acc i => acc.push (unpackSliceE (st[i]?.getD (sliceEEmpty 0))))
    (Array.emptyWithCapacity st.size)

def packStateSlice (st : Array (Array E)) : Array SliceE :=
  foldNat st.size
    (fun acc i => acc.push (packSliceE (st[i]?.getD #[])))
    (Array.emptyWithCapacity st.size)

def packColsK (cols : Array (Array K)) : Array ByteArray :=
  foldNat cols.size
    (fun acc i => acc.push (packU64Array (cols[i]?.getD #[])))
    (Array.emptyWithCapacity cols.size)

def checkSlice64Codecs (_ : Unit) : Bool :=
  let ks := genArrayK 257 0x1001
  let bs := packU64Array ks
  let ks2 := unpackU64Array bs
  let es := genArrayE 257 0x2002
  let se := packSliceE es
  let es2 := unpackSliceE se
  eqArrayK ks ks2 && eqArrayE es es2

def checkScalarParity (_ : Unit) : Bool :=
  foldNat 256
    (fun ok i =>
      let s := (i + 1).toUInt64 * 0x123456789abcdef
      let a := genE s
      let b := genE (s + 7)
      let r := genE (s + 19)
      let k0 := splitmix64 (s + 41)
      let k1 := splitmix64 (s + 59)
      let mulOk := eqK (busGf64Mul k0 k1) (mul k0 k1)
      let addOk := eqE (busEadd a b) (eadd a b)
      let emulOk := eqE (busEmul a b) (karatsubaMul a b)
      let mbaseOk := eqE (busMulBase a k0) (mulBase a k0)
      let interpRef := eadd a (karatsubaMul r (eadd a b))
      let interpOk := eqE (busInterp a b r) interpRef
      let interpKRef := eadd ⟨k0, 0, 0⟩ (mulBase r (k0 ^^^ k1))
      let interpKOk := eqE (busInterpK k0 k1 r) interpKRef
      let qA := busQuarticSummand a b r a b r a b r
      let qB := quarticSummand a b r a b r a b r
      let qOk := eqMsg4 qA qB
      ok && mulOk && addOk && emulOk && mbaseOk && interpOk && interpKOk && qOk)
    true

def checkTreeKernels (storedRows : Nat) (seed : UInt64) : BaseIO Bool := do
  let nVals := 4 * storedRows
  let nWeights := (storedRows + 1) / 2
  let vals := genArrayE nVals seed
  let eqW := genArrayE nWeights (seed + 0x5555)
  let ch := genE (seed + 0x9999)
  let valsSlice := packSliceE vals
  let eqWSlice := packSliceE eqW
  let refMsg := treeRoundMessage vals eqW
  let slMsg := busTreeRoundMessageSlice valsSlice eqWSlice
  let parMsg ← busTreeRoundMessagePar valsSlice eqWSlice
  let refFold := foldTreeScalar vals ch
  let slFold := unpackSliceE (busFoldTreeSlice valsSlice ch)
  let parFoldSlice ← busFoldTreePar valsSlice ch
  let parFold := unpackSliceE parFoldSlice
  let refNext := nextLevel vals
  let slNext := unpackSliceE (busNextLevelSlice valsSlice)
  let parNextSlice ← busNextLevelPar valsSlice
  let parNext := unpackSliceE parNextSlice
  return (eqMsg4 refMsg slMsg && eqMsg4 refMsg parMsg &&
    eqArrayE refFold slFold && eqArrayE refFold parFold &&
    eqArrayE refNext slNext && eqArrayE refNext parNext)

def sampleGroupedForm (seed : UInt64) : GroupedForm :=
  let c := genE seed
  let lin := #[(0, genE (seed + 10)), (2, genE (seed + 20)), (4, genE (seed + 30))]
  let g0Right := #[(1, genE (seed + 40)), (3, genE (seed + 50))]
  let g1Right := #[(2, genE (seed + 60)), (5, genE (seed + 70))]
  { constant := c, lin := lin, groups := #[(0, g0Right), (4, g1Right)] }

def checkTableKernels (half : Nat) (seed : UInt64) : BaseIO Bool := do
  let rows := 2 * half
  let gf := sampleGroupedForm seed
  let cols : Array (Array K) :=
    foldNat 6
      (fun acc c => acc.push (genArrayK rows (seed + (c + 1).toUInt64 * 1009)))
      (Array.emptyWithCapacity 6)
  let colsSlice := packColsK cols
  let eqr := genArrayE half (seed + 0x7777)
  let eqrSlice := packSliceE eqr
  let r := genE (seed + 0x8888)
  let refK0 := tableMessageK gf cols 0 eqr half false
  let slK0 := busTableMessageKSlice gf colsSlice 0 eqrSlice half false
  let parK0 ← busTableMessageKPar gf colsSlice 0 eqrSlice half false
  let refK1 := tableMessageK gf cols 0 eqr half true
  let slK1 := busTableMessageKSlice gf colsSlice 0 eqrSlice half true
  let parK1 ← busTableMessageKPar gf colsSlice 0 eqrSlice half true
  let refJoined := joinTableState gf cols 0 r half
  let slJoinedSlice := busJoinTableStateSlice gf colsSlice 0 r half
  let parJoinedSlice ← busJoinTableStatePar gf colsSlice 0 r half
  let slJoined := unpackStateSlice slJoinedSlice
  let parJoined := unpackStateSlice parJoinedSlice
  let half2 := half / 2
  let eqr2 := genArrayE half2 (seed + 0xaaaa)
  let eqr2Slice := packSliceE eqr2
  let r2 := genE (seed + 0xbbbb)
  let refE0 := tableMessageE gf.constant refJoined eqr2 half2 false
  let slE0 := busTableMessageESlice gf.constant slJoinedSlice eqr2Slice half2 false
  let parE0 ← busTableMessageEPar gf.constant slJoinedSlice eqr2Slice half2 false
  let refE1 := tableMessageE gf.constant refJoined eqr2 half2 true
  let slE1 := busTableMessageESlice gf.constant slJoinedSlice eqr2Slice half2 true
  let parE1 ← busTableMessageEPar gf.constant slJoinedSlice eqr2Slice half2 true
  let refFolded := foldTableState refJoined r2 half2
  let slFolded := unpackStateSlice (busFoldTableStateSlice slJoinedSlice r2 half2)
  let parFoldedSlice ← busFoldTableStatePar slJoinedSlice r2 half2
  let parFolded := unpackStateSlice parFoldedSlice
  return (eqPairE refK0 slK0 && eqPairE refK0 parK0 &&
    eqPairE refK1 slK1 && eqPairE refK1 parK1 &&
    eqStateE refJoined slJoined && eqStateE refJoined parJoined &&
    eqPairE refE0 slE0 && eqPairE refE0 parE0 &&
    eqPairE refE1 slE1 && eqPairE refE1 parE1 &&
    eqStateE refFolded slFolded && eqStateE refFolded parFolded)

def checkMleKernels (dim : Nat) (seed : UInt64) : BaseIO Bool := do
  let n := 1 <<< dim
  let tbl := genArrayK n seed
  let pt := genArrayE dim (seed + 0xcccc)
  let eqs := eqTable pt
  let tblSlice := packU64Array tbl
  let eqsSlice := packSliceE eqs
  let refVal := mleEval tbl pt
  let slVal := busMleEvalSlice tblSlice eqsSlice
  let parVal ← busMleEvalPar tblSlice eqsSlice
  return (eqE refVal slVal && eqE refVal parVal)

def runBenchmarks : IO Unit := do
  let nTreeRows := 524288
  let vals := genArrayE (4 * nTreeRows) 0xbeef01
  let eqW := genArrayE (nTreeRows / 2) 0xbeef02
  let ch := genE 0xbeef03
  let valsSlice := packSliceE vals
  let eqWSlice := packSliceE eqW

  let t0 ← IO.monoMsNow
  let mRef ← IO.lazyPure (fun _ => treeRoundMessage vals eqW)
  let t1 ← IO.monoMsNow
  let mSl ← IO.lazyPure (fun _ => busTreeRoundMessageSlice valsSlice eqWSlice)
  let t2 ← IO.monoMsNow
  let mPar ← busTreeRoundMessagePar valsSlice eqWSlice
  let t3 ← IO.monoMsNow

  let f0 ← IO.monoMsNow
  let fRef ← IO.lazyPure (fun _ => foldTreeScalar vals ch)
  let f1 ← IO.monoMsNow
  let fSl ← IO.lazyPure (fun _ => busFoldTreeSlice valsSlice ch)
  let f2 ← IO.monoMsNow
  let fPar ← busFoldTreePar valsSlice ch
  let f3 ← IO.monoMsNow

  let half := 524288
  let stArr : Array (Array E) :=
    #[genArrayE (2 * half) 0xcafe01, genArrayE (2 * half) 0xcafe02, genArrayE (2 * half) 0xcafe03]
  let stSlice := packStateSlice stArr
  let eqr := genArrayE half 0xcafe04
  let eqrSlice := packSliceE eqr

  let s0 ← IO.monoMsNow
  let sRef ← IO.lazyPure (fun _ => foldTableState stArr ch half)
  let s1 ← IO.monoMsNow
  let sSl ← IO.lazyPure (fun _ => busFoldTableStateSlice stSlice ch half)
  let s2 ← IO.monoMsNow
  let sPar ← busFoldTableStatePar stSlice ch half
  let s3 ← IO.monoMsNow

  let e0 ← IO.monoMsNow
  let eRef ← IO.lazyPure (fun _ => tableMessageE ch stArr eqr half true)
  let e1 ← IO.monoMsNow
  let eSl ← IO.lazyPure (fun _ => busTableMessageESlice ch stSlice eqrSlice half true)
  let e2 ← IO.monoMsNow
  let ePar ← busTableMessageEPar ch stSlice eqrSlice half true
  let e3 ← IO.monoMsNow

  let logN := 20
  let tblK := genArrayK (1 <<< logN) 0xdada01
  let tblKSlice := packU64Array tblK
  let ptBench := genArrayE logN 0xdada02
  let eqsFull := eqTable ptBench
  let eqsFullSlice := packSliceE eqsFull

  let m0 ← IO.monoMsNow
  let mleRef ← IO.lazyPure (fun _ =>
    foldNat eqsFull.size
      (fun acc z => eadd acc (nativeMulBase (eqsFull[z]?.getD zero) (tblK[z]?.getD 0)))
      zero)
  let m1 ← IO.monoMsNow
  let mleSl ← IO.lazyPure (fun _ => busMleEvalSlice tblKSlice eqsFullSlice)
  let m2 ← IO.monoMsNow
  let mlePar ← busMleEvalPar tblKSlice eqsFullSlice
  let m3 ← IO.monoMsNow

  let benchParity :=
    eqMsg4 mRef mSl && eqMsg4 mRef mPar &&
    decide (fRef.size = sliceESize fSl) && decide (fRef.size = sliceESize fPar) &&
    decide (sRef.size = sSl.size) && decide (sRef.size = sPar.size) &&
    eqPairE eRef eSl && eqPairE eRef ePar &&
    eqE mleRef mleSl && eqE mleRef mlePar

  IO.println s!"BENCH_TREE_MSG rows={nTreeRows} scalar_ms={t1 - t0} slice1_ms={t2 - t1} slice16_ms={t3 - t2}"
  IO.println s!"BENCH_FOLD_TREE rows={nTreeRows} scalar_ms={f1 - f0} slice1_ms={f2 - f1} slice16_ms={f3 - f2}"
  IO.println s!"BENCH_FOLD_TABLE half={half} cols=3 scalar_ms={s1 - s0} slice1_ms={s2 - s1} slice16_ms={s3 - s2}"
  IO.println s!"BENCH_TABLE_MSG_E half={half} cols=3 scalar_ms={e1 - e0} slice1_ms={e2 - e1} slice16_ms={e3 - e2}"
  IO.println s!"BENCH_MLE_EVAL n={1 <<< logN} scalar_ms={m1 - m0} slice1_ms={m2 - m1} slice16_ms={m3 - m2}"
  IO.println s!"BENCH_PARITY_OK={benchParity}"
  if !benchParity then
    throw (IO.userError "benchmark parity mismatch")

def runNativeBusKernelSuite : IO Unit := do
  let c0 := checkSlice64Codecs ()
  IO.println s!"SLICE64_CODECS_OK={c0}"
  let c1 := checkScalarParity ()
  IO.println s!"SCALAR_KERNELS_OK={c1}"
  let tEven ← checkTreeKernels 64 0x3001
  let tOdd ← checkTreeKernels 63 0x3002
  let tSmall ← checkTreeKernels 1 0x3003
  IO.println s!"TREE_KERNELS_OK={tEven && tOdd && tSmall}"
  let tb1 ← checkTableKernels 64 0x4001
  let tb2 ← checkTableKernels 128 0x4002
  IO.println s!"TABLE_KERNELS_OK={tb1 && tb2}"
  let ml1 ← checkMleKernels 8 0x5001
  let ml2 ← checkMleKernels 10 0x5002
  IO.println s!"MLE_KERNELS_OK={ml1 && ml2}"
  let allOk := c0 && c1 && tEven && tOdd && tSmall && tb1 && tb2 && ml1 && ml2
  IO.println s!"ALL_UNIT_TESTS_OK={allOk}"
  if !allOk then
    throw (IO.userError "unit differential test failed")
  runBenchmarks

end LeanVmXmss.Tests.Unit
