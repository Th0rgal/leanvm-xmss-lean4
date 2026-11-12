import Lean
import Spec.Field.Basic
import Spec.Keccak.Basic
import Spec.KeccakGkr.Basic
import Model.Field.NativeKernel
import Model.KeccakGkr.Scalar
import Native.Kernels.KeccakGkr

open Lean Elab Command

def hasSubstr (haystack needle : String) : Bool :=
  match haystack.splitOn needle with
  | _ :: _ :: _ => true
  | _ => false

run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  let mut rejected : Nat := 0
  for (name, info) in env.constants.toList do
    let text := name.toString
    if hasSubstr text "LeanVmXmss.Native.Kernels.KeccakGkr" then
      if hasSubstr text "._unsafe_rec" then
        logError m!"Forbidden generated name: {name}"
        rejected := rejected + 1
      if info.isUnsafe then
        logError m!"Unsafe declaration: {name}"
        rejected := rejected + 1
      if Lean.isExtern env name then
        logError m!"External declaration: {name}"
        rejected := rejected + 1
      let dependencies ← Lean.collectAxioms name
      for dependency in dependencies do
        unless #[`propext, `Quot.sound].contains dependency do
          logError m!"Forbidden transitive dependency in {name}: {dependency}"
          rejected := rejected + 1
      count := count + 1
  if count = 0 then throwError "Empty Native.Kernels.KeccakGkr declaration inventory"
  if rejected > 0 then throwError "Strict Native.Kernels.KeccakGkr audit rejected {rejected} declarations"
  logInfo m!"NATIVE_KECCAK_GKR_STRICT_AUDIT_COUNT {count}"
  logInfo m!"NATIVE_KECCAK_GKR_STRICT_AUDIT_REJECTIONS {rejected}"

#print axioms LeanVmXmss.Native.Kernels.KeccakGkr.keccakChiPlanes
#print axioms LeanVmXmss.Native.Kernels.KeccakGkr.keccakThetaRhoPiIotaPlanes
#print axioms LeanVmXmss.Native.Kernels.KeccakGkr.rmfePackBatch
#print axioms LeanVmXmss.Native.Kernels.KeccakGkr.rmfeUnpackBatch
#print axioms LeanVmXmss.Native.Kernels.KeccakGkr.gkrFoldEvenOdd
#print axioms LeanVmXmss.Native.Kernels.KeccakGkr.bitTranspose64x64

namespace LeanVmXmss.Tests.Unit.NativeKeccakGkrKernelTest

open Spec.Field (E eadd)
open Model.Field (nativeKaratsuba)
open Model.Pcs.Ntt (foldRange)
open Native.Kernels.KeccakGkr

def prngNext (state : UInt64) : UInt64 :=
  let s1 := state ^^^ (state <<< 13)
  let s2 := s1 ^^^ (s1 >>> 7)
  s2 ^^^ (s2 <<< 17)

def genWords (seed : UInt64) (count : Nat) : Array UInt64 :=
  let (arr, _) := foldRange count
    (fun (acc, st) _ =>
      let next := prngNext st
      (acc.push next, next))
    (Array.emptyWithCapacity count, seed)
  arr

def sliceStatesToBlock (states : Array (Array UInt64)) (nWords : Nat) : ByteArray :=
  let nInst := states.size
  foldRange 1600
    (fun acc pos =>
      let lane := pos / 64
      let z := UInt64.ofNat (pos % 64)
      foldRange nWords
        (fun cur w =>
          let word := foldRange 64
            (fun wAcc b =>
              let instIdx := 64 * w + b
              if instIdx < nInst then
                let st := states[instIdx]?.getD Spec.Keccak.zero
                let laneWord := st[lane]?.getD 0
                let bit := (laneWord >>> z) &&& 1
                wAcc ||| (bit <<< UInt64.ofNat b)
              else wAcc)
            (0 : UInt64)
          pushU64LE cur word)
        acc)
    (ByteArray.emptyWithCapacity (1600 * nWords * 8))

def unsliceBlockToStates (block : ByteArray) (nWords nInst : Nat) : Array (Array UInt64) :=
  foldRange nInst
    (fun acc instIdx =>
      let w := instIdx / 64
      let b := UInt64.ofNat (instIdx % 64)
      let st := foldRange 25
        (fun sAcc lane =>
          let laneWord := foldRange 64
            (fun lAcc z =>
              let pos := 64 * lane + z
              let pw := readWordAt block (USize.ofNat (nWords * pos + w))
              let bit := (pw >>> b) &&& 1
              lAcc ||| (bit <<< UInt64.ofNat z))
            (0 : UInt64)
          sAcc.push laneWord)
        (Array.emptyWithCapacity 25)
      acc.push st)
    (Array.emptyWithCapacity nInst)

def applyFinalIotaPlanes (block : ByteArray) (n : USize) (rc : UInt64) : ByteArray :=
  foldRange 1600
    (fun acc pos =>
      let upos := USize.ofNat pos
      let mask := iotaMaskWord rc upos
      let base := n * upos
      foldRange n.toNat
        (fun cur w =>
          let v := readWordAt block (base + USize.ofNat w) ^^^ mask
          pushU64LE cur v)
        acc)
    (ByteArray.emptyWithCapacity block.size)

def runBitSlicedKeccak24 (block0 : ByteArray) (n : USize) : ByteArray :=
  let s24 := foldRange 24
    (fun cur r =>
      let prevRc := if r = 0 then (0 : UInt64) else Spec.Keccak.rc[r - 1]?.getD 0
      let u := keccakThetaRhoPiIotaPlanes cur n prevRc
      keccakChiPlanes u n)
    block0
  let lastRc := Spec.Keccak.rc[23]?.getD 0
  applyFinalIotaPlanes s24 n lastRc

def checkTernaryD2 : Bool :=
  let words := genWords 0x13579bdf2468ace1 96
  foldRange 32
    (fun ok i =>
      let a := words[3 * i]?.getD 0
      let b := words[3 * i + 1]?.getD 0
      let c := words[3 * i + 2]?.getD 0
      let t := ternaryLogic64 a b c 0xD2
      let d := a ^^^ ((~~~b) &&& c)
      ok && decide (t = d))
    true

def checkKeccakPlanesDifferential : Bool :=
  let nWords : Nat := 2
  let nInst : Nat := 128
  let rawWords := genWords 0xdeadbeefcafebabe (nInst * 25)
  let states := foldRange nInst
    (fun acc i =>
      let st := foldRange 25
        (fun s l => s.push (rawWords[25 * i + l]?.getD 0))
        (Array.emptyWithCapacity 25)
      acc.push st)
    (Array.emptyWithCapacity nInst)
  let block0 := sliceStatesToBlock states nWords
  let blockOut := runBitSlicedKeccak24 block0 (USize.ofNat nWords)
  let gotStates := unsliceBlockToStates blockOut nWords nInst
  foldRange nInst
    (fun ok i =>
      let expected := Spec.Keccak.keccakF1600 (states[i]?.getD Spec.Keccak.zero)
      let got := gotStates[i]?.getD Spec.Keccak.zero
      let laneOk := foldRange 25
        (fun lOk l =>
          let ew := expected[l]?.getD 0
          let gw := got[l]?.getD 0
          lOk && decide (ew = gw))
        true
      ok && laneOk)
    true

def checkRmfePackUnpackDifferential : Bool :=
  let count : Nat := 256
  let words := genWords 0x0123456789abcdef (count * 2)
  let u16A := foldRange count (fun acc i => acc.push ((words[2 * i]?.getD 0) &&& 0xffff)) #[]
  let u16B := foldRange count (fun acc i => acc.push ((words[2 * i + 1]?.getD 0) &&& 0xffff)) #[]
  let bytesA := foldRange count (fun b i => pushU16LE b (u16A[i]?.getD 0)) (ByteArray.emptyWithCapacity (count * 2))
  let bytesB := foldRange count (fun b i => pushU16LE b (u16B[i]?.getD 0)) (ByteArray.emptyWithCapacity (count * 2))
  let packedA := rmfePackBatch bytesA (USize.ofNat count)
  let packedB := rmfePackBatch bytesB (USize.ofNat count)
  let packOk := foldRange count
    (fun ok i =>
      let a := u16A[i]?.getD 0
      let gotA := readU32LE packedA (USize.ofNat (4 * i))
      let refA := Spec.KeccakGkr.embedUnit a
      ok && decide (gotA = refA))
    true
  let prodBytes := foldRange count
    (fun b i =>
      let ea := readU32LE packedA (USize.ofNat (4 * i))
      let eb := readU32LE packedB (USize.ofNat (4 * i))
      let prod := Spec.KeccakGkr.carryless ea eb
      pushU64LE b prod)
    (ByteArray.emptyWithCapacity (count * 8))
  let unpacked := rmfeUnpackBatch prodBytes (USize.ofNat count)
  let unpackOk := foldRange count
    (fun ok i =>
      let a := u16A[i]?.getD 0
      let b := u16B[i]?.getD 0
      let got := readU16LE unpacked (USize.ofNat (2 * i))
      let expected := a &&& b
      ok && decide (got = expected))
    true
  packOk && unpackOk

def checkGkrFoldDifferential : Bool :=
  let count : Nat := 256
  let words := genWords 0xfedcba9876543210 (count * 6 + 3)
  let ch : E := ⟨words[0]?.getD 0, words[1]?.getD 0, words[2]?.getD 0⟩
  let (loBytes, hiBytes, table) := foldRange count
    (fun (lb, hb, tb) i =>
      let base := 3 + 6 * i
      let loE : E := ⟨words[base]?.getD 0, words[base + 1]?.getD 0, words[base + 2]?.getD 0⟩
      let hiE : E := ⟨words[base + 3]?.getD 0, words[base + 4]?.getD 0, words[base + 5]?.getD 0⟩
      let lb1 := pushU64LE (pushU64LE (pushU64LE lb loE.c0) loE.c1) loE.c2
      let hb1 := pushU64LE (pushU64LE (pushU64LE hb hiE.c0) hiE.c1) hiE.c2
      (lb1, hb1, (tb.push loE).push hiE))
    (ByteArray.emptyWithCapacity (count * 24),
     ByteArray.emptyWithCapacity (count * 24),
     Array.emptyWithCapacity (count * 2))
  let expected := Model.KeccakGkr.fold1 table ch
  let gotBytes := gkrFoldEvenOdd loBytes hiBytes (USize.ofNat count) ch.c0 ch.c1 ch.c2
  foldRange count
    (fun ok i =>
      let expE := expected[i]?.getD Spec.Field.zero
      let g0 := readWordAt gotBytes (USize.ofNat (3 * i))
      let g1 := readWordAt gotBytes (USize.ofNat (3 * i + 1))
      let g2 := readWordAt gotBytes (USize.ofNat (3 * i + 2))
      ok && decide (g0 = expE.c0) && decide (g1 = expE.c1) && decide (g2 = expE.c2))
    true

def refBitTranspose64Block (inp : ByteArray) (blockBase : Nat) : ByteArray :=
  foldRange 8
    (fun acc b =>
      foldRange 8
        (fun cur t =>
          let byteVal := foldRange 8
            (fun bv x =>
              let inByte := byteAt inp (USize.ofNat (blockBase + 8 * x + b))
              let bit := (inByte.toUInt64 >>> UInt64.ofNat t) &&& 1
              bv ||| (bit <<< UInt64.ofNat x))
            (0 : UInt64)
          cur.push byteVal.toUInt8)
        acc)
    (ByteArray.emptyWithCapacity 64)

def checkBitTranspose64x64Differential : Bool :=
  let nBlocks : Nat := 16
  let words := genWords 0x8877665544332211 (nBlocks * 8)
  let inp := foldRange (nBlocks * 8)
    (fun b i => pushU64LE b (words[i]?.getD 0))
    (ByteArray.emptyWithCapacity (nBlocks * 64))
  let got := bitTranspose64x64 inp (USize.ofNat nBlocks)
  foldRange nBlocks
    (fun ok blk =>
      let refBlk := refBitTranspose64Block inp (64 * blk)
      let blkOk := foldRange 64
        (fun bOk off =>
          let gByte := byteAt got (USize.ofNat (64 * blk + off))
          let rByte := byteAt refBlk (USize.ofNat off)
          bOk && decide (gByte = rByte))
        true
      ok && blkOk)
    true

end LeanVmXmss.Tests.Unit.NativeKeccakGkrKernelTest

open LeanVmXmss.Tests.Unit.NativeKeccakGkrKernelTest
open LeanVmXmss.Native.Kernels.KeccakGkr

def runBenchIters (iters : Nat) (step : UInt64 → ByteArray) : IO (Nat × UInt64) := do
  let warm := step 0
  let t0 ← IO.monoNanosNow
  let mut acc : UInt64 := readWordAt warm 0
  for i in [:iters] do
    let out := step (UInt64.ofNat i)
    acc := acc ^^^ readWordAt out (USize.ofNat (i % 4))
  let t1 ← IO.monoNanosNow
  let elapsed := t1 - t0
  return (elapsed / iters, acc)

def main : IO Unit := do
  unless checkTernaryD2 do
    throw (IO.userError "checkTernaryD2 failed")
  IO.println "PASS: checkTernaryD2 (vpternlogq 0xD2 matches a xor not-b-and-c)"
  unless checkKeccakPlanesDifferential do
    throw (IO.userError "checkKeccakPlanesDifferential failed")
  IO.println "PASS: checkKeccakPlanesDifferential (128 instances x 24 rounds bit-sliced vs Spec.Keccak.keccakF1600)"
  unless checkRmfePackUnpackDifferential do
    throw (IO.userError "checkRmfePackUnpackDifferential failed")
  IO.println "PASS: checkRmfePackUnpackDifferential (256 packs gf2Affine64 8-matrix embed + project vs Spec.KeccakGkr)"
  unless checkGkrFoldDifferential do
    throw (IO.userError "checkGkrFoldDifferential failed")
  IO.println "PASS: checkGkrFoldDifferential (256 F192 pairs planar fold vs Model.KeccakGkr.fold1)"
  unless checkBitTranspose64x64Differential do
    throw (IO.userError "checkBitTranspose64x64Differential failed")
  IO.println "PASS: checkBitTranspose64x64Differential (16x64-byte 64x64 bit transpose vs bit-by-bit reference)"

  let blockWords : USize := 8
  let benchBlock := ByteArray.mk (Array.replicate 102408 0xa5)
  let (chiNs, chiChk) ← runBenchIters 20
    (fun k => keccakChiPlanes (benchBlock.push k.toUInt8) blockWords)
  let (triNs, triChk) ← runBenchIters 20
    (fun k => keccakThetaRhoPiIotaPlanes benchBlock blockWords (0x800000008000808b ^^^ k))

  let rmfeCount : USize := 4096
  let rmfeIn := ByteArray.mk (Array.replicate 8192 0x5a)
  let (packNs, packChk) ← runBenchIters 20
    (fun k => rmfePackBatch (rmfeIn.push k.toUInt8) rmfeCount)
  let rmfeProdIn := ByteArray.mk (Array.replicate 32768 0x3c)
  let (unpackNs, unpackChk) ← runBenchIters 20
    (fun k => rmfeUnpackBatch (rmfeProdIn.push k.toUInt8) rmfeCount)

  let foldCount : USize := 2048
  let foldLo := ByteArray.mk (Array.replicate 49152 0x11)
  let foldHi := ByteArray.mk (Array.replicate 49152 0x22)
  let (foldNs, foldChk) ← runBenchIters 20
    (fun k => gkrFoldEvenOdd foldLo foldHi foldCount (0x123456789abcdef0 ^^^ k) 0xfedcba9876543210 0x0f1e2d3c4b5a6978)

  let trBlocks : USize := 256
  let trIn := ByteArray.mk (Array.replicate 16384 0x9c)
  let (trNs, trChk) ← runBenchIters 20
    (fun k => bitTranspose64x64 (trIn.push k.toUInt8) trBlocks)

  IO.println s!"BENCH_NS lean_xmss_keccak_chi_planes (1600x8 words): {chiNs} ns/iter (chk={chiChk})"
  IO.println s!"BENCH_NS lean_xmss_keccak_theta_rho_pi_iota_planes (1600x8 words): {triNs} ns/iter (chk={triChk})"
  IO.println s!"BENCH_NS lean_xmss_rmfe_pack_batch (4096 u16): {packNs} ns/iter (chk={packChk})"
  IO.println s!"BENCH_NS lean_xmss_rmfe_unpack_batch (4096 u64): {unpackNs} ns/iter (chk={unpackChk})"
  IO.println s!"BENCH_NS lean_xmss_gkr_fold_even_odd (2048 F192): {foldNs} ns/iter (chk={foldChk})"
  IO.println s!"BENCH_NS lean_xmss_bit_transpose_64x64 (256x64B blocks): {trNs} ns/iter (chk={trChk})"
  IO.println "ALL_NATIVE_KECCAK_GKR_KERNEL_TESTS_PASSED"
