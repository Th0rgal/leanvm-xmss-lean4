### Summary & Timings

All pure-Lean K3 Umbrella Kernel Island modules (`LeanVmXmss/Native/Kernels/Ntt.lean`, `LeanVmXmss/Native/Kernels/Keccak8x.lean`, and `LeanVmXmss/Tests/Unit/NativePcsMerkleKernelTest.lean`) compiled cleanly via `turbo-lean` and `lean-native v0.5.0`, passed differential verification against `Spec` and `Model` at sizes `2^4`, `2^12`, and `2^14`, passed the whole-module strict axiom audit (`173` declarations checked, `0` rejections, `0` `@[extern]`/`unsafe`/`sorry`/`native_decide`, all axioms `⊆ {propext, Quot.sound}`), and were saved with `manifest.json` under `/var/lib/orb-node/work/caches/xmss-hub-v3/wave3/k3-prep/`.

#### `#print axioms` & Strict Audit Output
```text
NATIVE_KERNELS_STRICT_AUDIT_COUNT 173
NATIVE_KERNELS_STRICT_AUDIT_REJECTIONS 0
'LeanVmXmss.Native.Kernels.Ntt.usize_lt_size' depends on axioms: [propext]
'LeanVmXmss.Native.Kernels.Ntt.usize_uset_size' depends on axioms: [propext]
'LeanVmXmss.Native.Kernels.Ntt.usize_ofNat_le_seven' depends on axioms: [propext, Quot.sound]
'LeanVmXmss.Native.Kernels.Ntt.usize_add_lt_size' depends on axioms: [propext, Quot.sound]
'LeanVmXmss.Native.Kernels.Ntt.loadU64' depends on axioms: [propext, Quot.sound]
'LeanVmXmss.Native.Kernels.Ntt.storeU64' depends on axioms: [propext, Quot.sound]
'LeanVmXmss.Native.Kernels.Ntt.buildTwiddleSlab' depends on axioms: [propext, Quot.sound]
'LeanVmXmss.Native.Kernels.Ntt.butterflyU' depends on axioms: [propext, Quot.sound]
'LeanVmXmss.Native.Kernels.Ntt.butterflyV' depends on axioms: [propext, Quot.sound]
'LeanVmXmss.Native.Kernels.Ntt.whirFoldC0' depends on axioms: [propext, Quot.sound]
'LeanVmXmss.Native.Kernels.Ntt.whirFoldC1' depends on axioms: [propext, Quot.sound]
'LeanVmXmss.Native.Kernels.Ntt.whirFoldC2' depends on axioms: [propext, Quot.sound]
'LeanVmXmss.Native.Kernels.Ntt.lean_xmss_ntt_stage_high' depends on axioms: [propext, Quot.sound]
'LeanVmXmss.Native.Kernels.Ntt.lean_xmss_ntt_tile_low' depends on axioms: [propext, Quot.sound]
'LeanVmXmss.Native.Kernels.Ntt.encodeBytes' depends on axioms: [propext, Quot.sound]
'LeanVmXmss.Native.Kernels.Ntt.encodeCosetBytes' depends on axioms: [propext, Quot.sound]
'LeanVmXmss.Native.Kernels.Ntt.lean_xmss_whir_fold_even_odd' depends on axioms: [propext, Quot.sound]
'LeanVmXmss.Native.Kernels.Ntt.lean_xmss_whir_fold_blocks' depends on axioms: [propext, Quot.sound]
'LeanVmXmss.Native.Kernels.Ntt.lean_xmss_whir_fold_batch' depends on axioms: [propext, Quot.sound]
'LeanVmXmss.Native.Kernels.Ntt.lean_xmss_whir_sumcheck_even_odd' depends on axioms: [propext, Quot.sound]
'LeanVmXmss.Native.Kernels.Keccak8x.round25x8' depends on axioms: [propext, Quot.sound]
'LeanVmXmss.Native.Kernels.Keccak8x.rounds25x8' depends on axioms: [propext, Quot.sound]
'LeanVmXmss.Native.Kernels.Keccak8x.keccakF1600_25x8' depends on axioms: [propext, Quot.sound]
'LeanVmXmss.Native.Kernels.Keccak8x.keccakF1600_8x' depends on axioms: [propext, Quot.sound]
'LeanVmXmss.Native.Kernels.Keccak8x.lean_xmss_merkle_compress_level' depends on axioms: [propext, Quot.sound]
'LeanVmXmss.Native.Kernels.Keccak8x.lean_xmss_merkle_hash_leaves' depends on axioms: [propext, Quot.sound]
'LeanVmXmss.Native.Kernels.Keccak8x.lean_xmss_merkle_build_flat' depends on axioms: [propext, Quot.sound]
'LeanVmXmss.Native.Kernels.Keccak8x.lean_xmss_merkle_root_from_flat' does not depend on any axioms
'LeanVmXmss.Native.Kernels.Keccak8x.lean_xmss_merkle_root_from_leaves' depends on axioms: [propext, Quot.sound]
'LeanVmXmss.Native.Kernels.Keccak8x.lean_xmss_pcs_commit_root' depends on axioms: [propext, Quot.sound]
'LeanVmXmss.Native.Kernels.Keccak8x.lean_xmss_pcs_commit_root_parallel' depends on axioms: [propext, Quot.sound]
```

#### Differential Tests & Microbenchmarks (`Zen 5`, 16 cores)
```text
PASS|keccakF1600_8x
PASS|ntt_differential_2^4_2^12_2^14
PASS|merkle_and_pcs_commit_2^4_2^12_2^14
PASS|whir_fold_and_sumcheck_2^4_2^12_2^14
BENCH|ntt_encode_2^14x56_us=48467|bytes=7340032
BENCH|merkle_leaves_8x_2^14x56_us=102362|bytes=524288
BENCH|merkle_flat_8x_2^14_us=26927|root=cb42d481e7b6ada2dc3100cd8dc9bd184ff91b60a2a52940d835be4b028ab030
BENCH|whir_fold_batch_2^14_4rounds_us=1250|bytes=24576
BENCH|pcs_commit_1thread_log15_lanes51_ms=793|root=09be9237bcb43c88335e928ac9a670b890918071458e01754f7d9769471ee434
BENCH|pcs_commit_16core_log15_lanes51_ms=132|root=09be9237bcb43c88335e928ac9a670b890918071458e01754f7d9769471ee434
ALL_TESTS_PASSED
```
(`132 ms` full `logRows=15, lanes=51, logInvRate=1` PCS commit + `~1.25 ms` WHIR 4-round fold batch = `~134 ms`, well inside the `<= 270 ms` 16-core K3 budget.)

---

### `LeanVmXmss/Native/Kernels/Ntt.lean`
```lean
import Spec.Field.Basic
import Model.Field.NativeKernel
import Model.Pcs.Ntt

namespace LeanVmXmss.Native.Kernels.Ntt

open Spec.Field (K E)
open Model.Field (nativeMul nativeKaratsuba0 nativeKaratsuba1 nativeKaratsuba2)

theorem usize_lt_size {b : ByteArray} {i : USize} (h : i < b.usize) : i.toNat < b.size := by
  have h1 : i.toNat < b.usize.toNat := USize.lt_iff_toNat_lt.mp h
  have h2 : b.usize.toNat ≤ b.size := by
    simp [ByteArray.usize, USize.toNat_ofNat']
    exact Nat.mod_le _ _
  exact Nat.lt_of_lt_of_le h1 h2

theorem usize_uset_size (b : ByteArray) (i : USize) (v : UInt8) (h : i.toNat < b.size) :
    (b.uset i v h).size = b.size := by
  cases b
  simp [ByteArray.uset, ByteArray.size]

theorem usize_ofNat_le_seven (k : Nat) (hk : k ≤ 7) :
    (USize.ofNat k).toNat ≤ (7 : USize).toNat := by
  cases System.Platform.numBits_eq with
  | inl h32 =>
    have hpow : 2 ^ System.Platform.numBits = 4294967296 := by rw [h32]
    simp [USize.toNat_ofNat', hpow]
    omega
  | inr h64 =>
    have hpow : 2 ^ System.Platform.numBits = 18446744073709551616 := by rw [h64]
    simp [USize.toNat_ofNat', hpow]
    omega

theorem usize_add_lt_size {b : ByteArray} {off : USize} (k : Nat) (hk : k ≤ 7)
    (hle : off ≤ off + 7) (hlt : off + 7 < b.usize) :
    (off + USize.ofNat k).toNat < b.size := by
  have h1 : off.toNat ≤ (off + 7).toNat := USize.le_iff_toNat_le.mp hle
  have h2 : (USize.ofNat k).toNat ≤ (7 : USize).toNat := usize_ofNat_le_seven k hk
  have hm : (off + 7).toNat = off.toNat + (7 : USize).toNat := by
    have hmod : (off + 7).toNat = (off.toNat + (7 : USize).toNat) % (2 ^ System.Platform.numBits) :=
      USize.toNat_add off 7
    by_cases hov : off.toNat + (7 : USize).toNat < 2 ^ System.Platform.numBits
    · rw [hmod, Nat.mod_eq_of_lt hov]
    · have hb : (7 : USize).toNat < 2 ^ System.Platform.numBits :=
        (7 : USize).toNat_lt_two_pow_numBits
      have ho : off.toNat < 2 ^ System.Platform.numBits := off.toNat_lt_two_pow_numBits
      rw [hmod, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h1
      omega
  have hob : (off + 7).toNat < 2 ^ System.Platform.numBits :=
    (off + 7).toNat_lt_two_pow_numBits
  have hk_eq : (off + USize.ofNat k).toNat = off.toNat + (USize.ofNat k).toNat := by
    rw [USize.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hsz : (off + 7).toNat < b.size := usize_lt_size hlt
  omega

@[inline] def foldUSizeLoop {α : Type} (f : α → USize → α) (rem : Nat) (idx : USize) (acc : α) : α :=
  Fin.foldl rem (fun a k => f a (idx + USize.ofNat k.val)) acc

@[inline] def foldUSize {α : Type} (n : Nat) (f : α → USize → α) (init : α) : α :=
  foldUSizeLoop f n 0 init

@[inline] def loadU64 (buf : @& ByteArray) (off : USize) : UInt64 :=
  if hle : off ≤ off + 7 then
    if hlt : off + 7 < buf.usize then
      (buf.uget (off + 0) (usize_add_lt_size 0 (by decide) hle hlt)).toUInt64 |||
      ((buf.uget (off + 1) (usize_add_lt_size 1 (by decide) hle hlt)).toUInt64 <<< 8) |||
      ((buf.uget (off + 2) (usize_add_lt_size 2 (by decide) hle hlt)).toUInt64 <<< 16) |||
      ((buf.uget (off + 3) (usize_add_lt_size 3 (by decide) hle hlt)).toUInt64 <<< 24) |||
      ((buf.uget (off + 4) (usize_add_lt_size 4 (by decide) hle hlt)).toUInt64 <<< 32) |||
      ((buf.uget (off + 5) (usize_add_lt_size 5 (by decide) hle hlt)).toUInt64 <<< 40) |||
      ((buf.uget (off + 6) (usize_add_lt_size 6 (by decide) hle hlt)).toUInt64 <<< 48) |||
      ((buf.uget (off + 7) (usize_add_lt_size 7 (by decide) hle hlt)).toUInt64 <<< 56)
    else 0
  else 0

@[inline] def storeU64 (buf : ByteArray) (off : USize) (val : UInt64) : ByteArray :=
  if hle : off ≤ off + 7 then
    if hlt : off + 7 < buf.usize then
      let b0 := buf.uset (off + 0) val.toUInt8 (usize_add_lt_size 0 (by decide) hle hlt)
      have s0 : b0.size = buf.size := usize_uset_size _ _ _ _
      let b1 := b0.uset (off + 1) (val >>> 8).toUInt8
        (s0.symm ▸ usize_add_lt_size 1 (by decide) hle hlt)
      have s1 : b1.size = buf.size := (usize_uset_size _ _ _ _).trans s0
      let b2 := b1.uset (off + 2) (val >>> 16).toUInt8
        (s1.symm ▸ usize_add_lt_size 2 (by decide) hle hlt)
      have s2 : b2.size = buf.size := (usize_uset_size _ _ _ _).trans s1
      let b3 := b2.uset (off + 3) (val >>> 24).toUInt8
        (s2.symm ▸ usize_add_lt_size 3 (by decide) hle hlt)
      have s3 : b3.size = buf.size := (usize_uset_size _ _ _ _).trans s2
      let b4 := b3.uset (off + 4) (val >>> 32).toUInt8
        (s3.symm ▸ usize_add_lt_size 4 (by decide) hle hlt)
      have s4 : b4.size = buf.size := (usize_uset_size _ _ _ _).trans s3
      let b5 := b4.uset (off + 5) (val >>> 40).toUInt8
        (s4.symm ▸ usize_add_lt_size 5 (by decide) hle hlt)
      have s5 : b5.size = buf.size := (usize_uset_size _ _ _ _).trans s4
      let b6 := b5.uset (off + 6) (val >>> 48).toUInt8
        (s5.symm ▸ usize_add_lt_size 6 (by decide) hle hlt)
      have s6 : b6.size = buf.size := (usize_uset_size _ _ _ _).trans s5
      b6.uset (off + 7) (val >>> 56).toUInt8
        (s6.symm ▸ usize_add_lt_size 7 (by decide) hle hlt)
    else buf
  else buf

@[inline] def pushU64LE (buf : ByteArray) (val : UInt64) : ByteArray :=
  let b0 := buf.push val.toUInt8
  let b1 := b0.push (val >>> 8).toUInt8
  let b2 := b1.push (val >>> 16).toUInt8
  let b3 := b2.push (val >>> 24).toUInt8
  let b4 := b3.push (val >>> 32).toUInt8
  let b5 := b4.push (val >>> 40).toUInt8
  let b6 := b5.push (val >>> 48).toUInt8
  b6.push (val >>> 56).toUInt8

def zeroByteArray (numBytes : Nat) : ByteArray :=
  Model.Pcs.Ntt.foldRange numBytes (fun acc _ => acc.push 0) (ByteArray.emptyWithCapacity numBytes)

def packWordsLE (words : @& Array K) : ByteArray :=
  let cap := words.size * 8
  Model.Pcs.Ntt.foldRange words.size
    (fun acc i => pushU64LE acc (words.getD i 0))
    (ByteArray.emptyWithCapacity cap)

def unpackWordsLE (bytes : @& ByteArray) : Array K :=
  let count := bytes.size / 8
  Model.Pcs.Ntt.foldRange count
    (fun acc i => acc.push (loadU64 bytes (USize.ofNat (i * 8))))
    (Array.emptyWithCapacity count)

def packExtLE (elems : @& Array E) : ByteArray :=
  let cap := elems.size * 24
  Model.Pcs.Ntt.foldRange elems.size
    (fun acc i =>
      let e := elems.getD i Spec.Field.zero
      let acc := pushU64LE acc e.c0
      let acc := pushU64LE acc e.c1
      pushU64LE acc e.c2)
    (ByteArray.emptyWithCapacity cap)

def unpackExtLE (bytes : @& ByteArray) : Array E :=
  let count := bytes.size / 24
  Model.Pcs.Ntt.foldRange count
    (fun acc i =>
      let base := USize.ofNat (i * 24)
      let c0 := loadU64 bytes base
      let c1 := loadU64 bytes (base + 8)
      let c2 := loadU64 bytes (base + 16)
      acc.push ⟨c0, c1, c2⟩)
    (Array.emptyWithCapacity count)

def buildTwiddleSlab (logD : Nat) : ByteArray :=
  let table := Model.Pcs.Ntt.evals logD
  let totalTwiddles := (1 <<< logD) - 1
  let out := ByteArray.emptyWithCapacity (totalTwiddles * 8)
  Model.Pcs.Ntt.foldRange logD
    (fun acc layer =>
      let blocks := 1 <<< layer
      let values := Model.Pcs.Ntt.rowFromEvals table logD (logD - layer - 1)
      Model.Pcs.Ntt.foldRange blocks
        (fun acc2 block =>
          pushU64LE acc2 (Model.Pcs.Ntt.twiddleFromRow values block))
        acc)
    out

@[inline] def twiddleAt (twiddles : @& ByteArray) (layer block : USize) : K :=
  let idx := ((1 : USize) <<< layer) - 1 + block
  loadU64 twiddles (idx <<< 3)

@[export lean_xmss_ntt_bfly_u]
def butterflyU (top bot t : UInt64) : UInt64 :=
  top ^^^ nativeMul bot t

@[export lean_xmss_ntt_bfly_v]
def butterflyV (bot u : UInt64) : UInt64 :=
  bot ^^^ u

@[export lean_xmss_whir_fold_c0]
def whirFoldC0 (l0 l1 l2 h0 h1 h2 r0 r1 r2 : UInt64) : UInt64 :=
  l0 ^^^ nativeKaratsuba0 r0 r1 r2 (l0 ^^^ h0) (l1 ^^^ h1) (l2 ^^^ h2)

@[export lean_xmss_whir_fold_c1]
def whirFoldC1 (l0 l1 l2 h0 h1 h2 r0 r1 r2 : UInt64) : UInt64 :=
  l1 ^^^ nativeKaratsuba1 r0 r1 r2 (l0 ^^^ h0) (l1 ^^^ h1) (l2 ^^^ h2)

@[export lean_xmss_whir_fold_c2]
def whirFoldC2 (l0 l1 l2 h0 h1 h2 r0 r1 r2 : UInt64) : UInt64 :=
  l2 ^^^ nativeKaratsuba2 r0 r1 r2 (l0 ^^^ h0) (l1 ^^^ h1) (l2 ^^^ h2)

@[inline] def butterflyPairBytes (data : ByteArray) (topOff botOff : USize) (t : K) : ByteArray :=
  let top := loadU64 data topOff
  let bot := loadU64 data botOff
  let u := butterflyU top bot t
  let v := butterflyV bot u
  let data := storeU64 data topOff u
  storeU64 data botOff v

@[inline] def butterflyVec8Bytes (data : ByteArray) (topOff botOff : USize) (t : K) : ByteArray :=
  let t0 := loadU64 data topOff
  let t1 := loadU64 data (topOff + 8)
  let t2 := loadU64 data (topOff + 16)
  let t3 := loadU64 data (topOff + 24)
  let t4 := loadU64 data (topOff + 32)
  let t5 := loadU64 data (topOff + 40)
  let t6 := loadU64 data (topOff + 48)
  let t7 := loadU64 data (topOff + 56)
  let b0 := loadU64 data botOff
  let b1 := loadU64 data (botOff + 8)
  let b2 := loadU64 data (botOff + 16)
  let b3 := loadU64 data (botOff + 24)
  let b4 := loadU64 data (botOff + 32)
  let b5 := loadU64 data (botOff + 40)
  let b6 := loadU64 data (botOff + 48)
  let b7 := loadU64 data (botOff + 56)
  let u0 := butterflyU t0 b0 t
  let u1 := butterflyU t1 b1 t
  let u2 := butterflyU t2 b2 t
  let u3 := butterflyU t3 b3 t
  let u4 := butterflyU t4 b4 t
  let u5 := butterflyU t5 b5 t
  let u6 := butterflyU t6 b6 t
  let u7 := butterflyU t7 b7 t
  let data := storeU64 data topOff u0
  let data := storeU64 data (topOff + 8) u1
  let data := storeU64 data (topOff + 16) u2
  let data := storeU64 data (topOff + 24) u3
  let data := storeU64 data (topOff + 32) u4
  let data := storeU64 data (topOff + 40) u5
  let data := storeU64 data (topOff + 48) u6
  let data := storeU64 data (topOff + 56) u7
  let data := storeU64 data botOff (butterflyV b0 u0)
  let data := storeU64 data (botOff + 8) (butterflyV b1 u1)
  let data := storeU64 data (botOff + 16) (butterflyV b2 u2)
  let data := storeU64 data (botOff + 24) (butterflyV b3 u3)
  let data := storeU64 data (botOff + 32) (butterflyV b4 u4)
  let data := storeU64 data (botOff + 40) (butterflyV b5 u5)
  let data := storeU64 data (botOff + 48) (butterflyV b6 u6)
  storeU64 data (botOff + 56) (butterflyV b7 u7)

@[inline] def butterflyRowBytes (data : ByteArray) (topByteBase botByteBase : USize)
    (lanes : Nat) (t : K) : ByteArray :=
  let vec8Count := lanes / 8
  let remLanes := lanes % 8
  let data := foldUSize vec8Count
    (fun d v =>
      let off := v <<< 6
      butterflyVec8Bytes d (topByteBase + off) (botByteBase + off) t)
    data
  let tailBase := USize.ofNat (vec8Count * 64)
  foldUSize remLanes
    (fun d remIdx =>
      let off := tailBase + (remIdx <<< 3)
      butterflyPairBytes d (topByteBase + off) (botByteBase + off) t)
    data

def lean_xmss_ntt_stage_high (data : ByteArray) (twiddles : @& ByteArray)
    (lanes layer logD : Nat) : ByteArray :=
  if layer < logD then
    let blocks := 1 <<< layer
    let half := 1 <<< (logD - layer - 1)
    let lanesUS := USize.ofNat lanes
    let halfUS := USize.ofNat half
    let twoHalfUS := halfUS <<< 1
    let halfStrideBytes := (halfUS * lanesUS) <<< 3
    let layerUS := USize.ofNat layer
    foldUSize blocks
      (fun d block =>
        let t := twiddleAt twiddles layerUS block
        let blockRowBase := block * twoHalfUS
        foldUSize half
          (fun d2 rowIdx =>
            let topByteBase := ((blockRowBase + rowIdx) * lanesUS) <<< 3
            let botByteBase := topByteBase + halfStrideBytes
            butterflyRowBytes d2 topByteBase botByteBase lanes t)
          d)
      data
  else data

def lean_xmss_ntt_tile_low (data : ByteArray) (twiddles : @& ByteArray)
    (lanes startLayer layerCount logD : Nat) : ByteArray :=
  if startLayer < logD then
    let endLayer := min logD (startLayer + layerCount)
    let actualCount := endLayer - startLayer
    if actualCount = 0 then data
    else
      let numTiles := 1 <<< startLayer
      let tileRows := 1 <<< (logD - startLayer)
      let lanesUS := USize.ofNat lanes
      let tileRowsUS := USize.ofNat tileRows
      let tileStrideBytes := (tileRowsUS * lanesUS) <<< 3
      foldUSize numTiles
        (fun d tileIdx =>
          let tileByteBase := tileIdx * tileStrideBytes
          Model.Pcs.Ntt.foldRange actualCount
            (fun dStep step =>
              let curLayer := startLayer + step
              let localBlocks := 1 <<< step
              let half := 1 <<< (logD - curLayer - 1)
              let halfUS := USize.ofNat half
              let twoHalfUS := halfUS <<< 1
              let halfStrideBytes := (halfUS * lanesUS) <<< 3
              let curLayerUS := USize.ofNat curLayer
              let globalBlockBase := tileIdx <<< (USize.ofNat step)
              foldUSize localBlocks
                (fun dBlk localBlk =>
                  let t := twiddleAt twiddles curLayerUS (globalBlockBase + localBlk)
                  let localRowBase := localBlk * twoHalfUS
                  foldUSize half
                    (fun dRow rowIdx =>
                      let topByteBase := tileByteBase + (((localRowBase + rowIdx) * lanesUS) <<< 3)
                      let botByteBase := topByteBase + halfStrideBytes
                      butterflyRowBytes dRow topByteBase botByteBase lanes t)
                    dBlk)
                dStep)
            d)
        data
  else data

@[inline] def extractSlice (buf : @& ByteArray) (start len : Nat) : ByteArray :=
  buf.extract start (start + len)

@[inline] def copySlice (dst : ByteArray) (src : @& ByteArray) (dstStart : Nat) : ByteArray :=
  let words := src.size / 8
  let dstBase := USize.ofNat dstStart
  foldUSize words
    (fun acc i =>
      let off := i <<< 3
      storeU64 acc (dstBase + off) (loadU64 src off))
    dst

def encodeBytes (data : ByteArray) (lanes startLayer : Nat) : ByteArray :=
  if lanes = 0 then data
  else
    let totalWords := data.size / 8
    let rows := totalWords / lanes
    let logD := rows.log2
    if logD ≤ startLayer then data
    else
      let twiddles := buildTwiddleSlab logD
      let tileThreshold := if logD > 8 then logD - 8 else startLayer
      let splitLayer := max startLayer tileThreshold
      let highCount := splitLayer - startLayer
      let data := Model.Pcs.Ntt.foldRange highCount
        (fun d step => lean_xmss_ntt_stage_high d twiddles lanes (startLayer + step) logD)
        data
      let lowCount := logD - splitLayer
      lean_xmss_ntt_tile_low data twiddles lanes splitLayer lowCount logD

def encodeCosetBytes (firstCoset : @& ByteArray) (twiddles : @& ByteArray)
    (lanes logRows logInvRate coset : Nat) : ByteArray :=
  let buf := firstCoset.extract 0 firstCoset.size
  let logD := logRows + logInvRate
  let lanesUS := USize.ofNat lanes
  let cosetUS := USize.ofNat coset
  let tileThreshold := if logRows > 8 then logRows - 8 else 0
  let buf := Model.Pcs.Ntt.foldRange tileThreshold
    (fun d step =>
      let curLayer := logInvRate + step
      let localBlocks := 1 <<< step
      let half := 1 <<< (logRows - step - 1)
      let halfUS := USize.ofNat half
      let twoHalfUS := halfUS <<< 1
      let halfStrideBytes := (halfUS * lanesUS) <<< 3
      let curLayerUS := USize.ofNat curLayer
      let blockBase := cosetUS <<< (USize.ofNat step)
      foldUSize localBlocks
        (fun dBlk localBlk =>
          let t := twiddleAt twiddles curLayerUS (blockBase + localBlk)
          let blockRowBase := localBlk * twoHalfUS
          foldUSize half
            (fun dRow rowIdx =>
              let topByteBase := ((blockRowBase + rowIdx) * lanesUS) <<< 3
              let botByteBase := topByteBase + halfStrideBytes
              butterflyRowBytes dRow topByteBase botByteBase lanes t)
            dBlk)
        d)
    buf
  let remSteps := logRows - tileThreshold
  if remSteps = 0 then buf
  else
    let numTiles := 1 <<< tileThreshold
    let tileRows := 1 <<< remSteps
    let tileStrideBytes := (USize.ofNat (tileRows * lanes)) <<< 3
    foldUSize numTiles
      (fun d tileIdx =>
        let tileByteBase := tileIdx * tileStrideBytes
        let baseGlobalTile := (cosetUS <<< (USize.ofNat tileThreshold)) + tileIdx
        Model.Pcs.Ntt.foldRange remSteps
          (fun dStep step =>
            let curStep := tileThreshold + step
            let curLayer := logInvRate + curStep
            let localBlocks := 1 <<< step
            let half := 1 <<< (logRows - curStep - 1)
            let halfUS := USize.ofNat half
            let twoHalfUS := halfUS <<< 1
            let halfStrideBytes := (halfUS * lanesUS) <<< 3
            let curLayerUS := USize.ofNat curLayer
            let globalBlockBase := baseGlobalTile <<< (USize.ofNat step)
            foldUSize localBlocks
              (fun dBlk localBlk =>
                let t := twiddleAt twiddles curLayerUS (globalBlockBase + localBlk)
                let localRowBase := localBlk * twoHalfUS
                foldUSize half
                  (fun dRow rowIdx =>
                    let topByteBase := tileByteBase + (((localRowBase + rowIdx) * lanesUS) <<< 3)
                    let botByteBase := topByteBase + halfStrideBytes
                    butterflyRowBytes dRow topByteBase botByteBase lanes t)
                  dBlk)
              dStep)
          d)
      buf

def lean_xmss_whir_fold_even_odd (xs : @& ByteArray) (r0 r1 r2 : UInt64) : ByteArray :=
  let totalElems := xs.size / 24
  let halfElems := totalElems / 2
  let out := zeroByteArray (halfElems * 24)
  foldUSize halfElems
    (fun acc i =>
      let inOff := i * (48 : USize)
      let outOff := i * (24 : USize)
      let l0 := loadU64 xs inOff
      let l1 := loadU64 xs (inOff + 8)
      let l2 := loadU64 xs (inOff + 16)
      let h0 := loadU64 xs (inOff + 24)
      let h1 := loadU64 xs (inOff + 32)
      let h2 := loadU64 xs (inOff + 40)
      let o0 := whirFoldC0 l0 l1 l2 h0 h1 h2 r0 r1 r2
      let o1 := whirFoldC1 l0 l1 l2 h0 h1 h2 r0 r1 r2
      let o2 := whirFoldC2 l0 l1 l2 h0 h1 h2 r0 r1 r2
      let acc := storeU64 acc outOff o0
      let acc := storeU64 acc (outOff + 8) o1
      storeU64 acc (outOff + 16) o2)
    out

def lean_xmss_whir_fold_blocks (blockLen : Nat) (xs : @& ByteArray) (r0 r1 r2 : UInt64) : ByteArray :=
  if blockLen = 0 then ByteArray.empty
  else
    let totalElems := xs.size / 24
    let nBlocks := totalElems / blockLen
    let pairs := (nBlocks + 1) / 2
    let out := zeroByteArray (pairs * blockLen * 24)
    let blockBytes := USize.ofNat (blockLen * 24)
    let o0r := (1 : UInt64) ^^^ r0
    Model.Pcs.Ntt.foldRange pairs
      (fun acc p =>
        let pUS := USize.ofNat p
        let base0 := (pUS * 2) * blockBytes
        let base1 := (pUS * 2 + 1) * blockBytes
        let outBase := pUS * blockBytes
        if 2 * p + 1 < nBlocks then
          foldUSize blockLen
            (fun acc2 k =>
              let off := k * (24 : USize)
              let in0 := base0 + off
              let in1 := base1 + off
              let dst := outBase + off
              let l0 := loadU64 xs in0
              let l1 := loadU64 xs (in0 + 8)
              let l2 := loadU64 xs (in0 + 16)
              let h0 := loadU64 xs in1
              let h1 := loadU64 xs (in1 + 8)
              let h2 := loadU64 xs (in1 + 16)
              let c0 := whirFoldC0 l0 l1 l2 h0 h1 h2 r0 r1 r2
              let c1 := whirFoldC1 l0 l1 l2 h0 h1 h2 r0 r1 r2
              let c2 := whirFoldC2 l0 l1 l2 h0 h1 h2 r0 r1 r2
              let acc2 := storeU64 acc2 dst c0
              let acc2 := storeU64 acc2 (dst + 8) c1
              storeU64 acc2 (dst + 16) c2)
            acc
        else
          foldUSize blockLen
            (fun acc2 k =>
              let off := k * (24 : USize)
              let in0 := base0 + off
              let dst := outBase + off
              let l0 := loadU64 xs in0
              let l1 := loadU64 xs (in0 + 8)
              let l2 := loadU64 xs (in0 + 16)
              let c0 := nativeKaratsuba0 o0r r1 r2 l0 l1 l2
              let c1 := nativeKaratsuba1 o0r r1 r2 l0 l1 l2
              let c2 := nativeKaratsuba2 o0r r1 r2 l0 l1 l2
              let acc2 := storeU64 acc2 dst c0
              let acc2 := storeU64 acc2 (dst + 8) c1
              storeU64 acc2 (dst + 16) c2)
            acc)
      out

def lean_xmss_whir_fold_batch (tableBytes : ByteArray) (pointBytes : @& ByteArray) : ByteArray :=
  let rounds := pointBytes.size / 24
  Model.Pcs.Ntt.foldRange rounds
    (fun cur step =>
      let off := USize.ofNat (step * 24)
      let r0 := loadU64 pointBytes off
      let r1 := loadU64 pointBytes (off + 8)
      let r2 := loadU64 pointBytes (off + 16)
      lean_xmss_whir_fold_even_odd cur r0 r1 r2)
    tableBytes

def lean_xmss_whir_sumcheck_even_odd (fBytes bBytes : @& ByteArray) : ByteArray :=
  let pairs := min ((fBytes.size / 24) / 2) ((bBytes.size / 24) / 2)
  let init : UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 := (0, 0, 0, 0, 0, 0)
  let (u00, u01, u02, u20, u21, u22) :=
    foldUSize pairs
      (fun (u00, u01, u02, u20, u21, u22) i =>
        let off := i * (48 : USize)
        let f00 := loadU64 fBytes off
        let f01 := loadU64 fBytes (off + 8)
        let f02 := loadU64 fBytes (off + 16)
        let f10 := loadU64 fBytes (off + 24)
        let f11 := loadU64 fBytes (off + 32)
        let f12 := loadU64 fBytes (off + 40)
        let b00 := loadU64 bBytes off
        let b01 := loadU64 bBytes (off + 8)
        let b02 := loadU64 bBytes (off + 16)
        let b10 := loadU64 bBytes (off + 24)
        let b11 := loadU64 bBytes (off + 32)
        let b12 := loadU64 bBytes (off + 40)
        let sf0 := f00 ^^^ f10
        let sf1 := f01 ^^^ f11
        let sf2 := f02 ^^^ f12
        let sb0 := b00 ^^^ b10
        let sb1 := b01 ^^^ b11
        let sb2 := b02 ^^^ b12
        (u00 ^^^ nativeKaratsuba0 f00 f01 f02 b00 b01 b02,
         u01 ^^^ nativeKaratsuba1 f00 f01 f02 b00 b01 b02,
         u02 ^^^ nativeKaratsuba2 f00 f01 f02 b00 b01 b02,
         u20 ^^^ nativeKaratsuba0 sf0 sf1 sf2 sb0 sb1 sb2,
         u21 ^^^ nativeKaratsuba1 sf0 sf1 sf2 sb0 sb1 sb2,
         u22 ^^^ nativeKaratsuba2 sf0 sf1 sf2 sb0 sb1 sb2))
      init
  let out := ByteArray.emptyWithCapacity 48
  let out := pushU64LE out u00
  let out := pushU64LE out u01
  let out := pushU64LE out u02
  let out := pushU64LE out u20
  let out := pushU64LE out u21
  pushU64LE out u22

end LeanVmXmss.Native.Kernels.Ntt
```

---

### `LeanVmXmss/Native/Kernels/Keccak8x.lean`
```lean
import Model.Keccak.Registers
import Model.Pcs.Ntt
import Native.Kernels.Ntt

namespace LeanVmXmss.Native.Kernels.Keccak8x

open LeanVmXmss.Native.Kernels.Ntt (loadU64 storeU64 pushU64LE zeroByteArray foldUSize)

structure Lane8 where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64
  w4 : UInt64
  w5 : UInt64
  w6 : UInt64
  w7 : UInt64
  deriving Inhabited

structure State25x8 where
  a00 : Lane8
  a01 : Lane8
  a02 : Lane8
  a03 : Lane8
  a04 : Lane8
  a05 : Lane8
  a06 : Lane8
  a07 : Lane8
  a08 : Lane8
  a09 : Lane8
  a10 : Lane8
  a11 : Lane8
  a12 : Lane8
  a13 : Lane8
  a14 : Lane8
  a15 : Lane8
  a16 : Lane8
  a17 : Lane8
  a18 : Lane8
  a19 : Lane8
  a20 : Lane8
  a21 : Lane8
  a22 : Lane8
  a23 : Lane8
  a24 : Lane8
  deriving Inhabited

@[inline] def zeroLane8 : Lane8 := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

@[inline] def splatLane8 (v : UInt64) : Lane8 := ⟨v, v, v, v, v, v, v, v⟩

@[inline] def xor8 (x y : Lane8) : Lane8 :=
  ⟨x.w0 ^^^ y.w0, x.w1 ^^^ y.w1, x.w2 ^^^ y.w2, x.w3 ^^^ y.w3,
   x.w4 ^^^ y.w4, x.w5 ^^^ y.w5, x.w6 ^^^ y.w6, x.w7 ^^^ y.w7⟩

@[inline] def xor5_8 (a b c d e : Lane8) : Lane8 :=
  xor8 (xor8 (xor8 a b) (xor8 c d)) e

@[inline] def chi8 (b0 b1 b2 : Lane8) : Lane8 :=
  ⟨b0.w0 ^^^ ((~~~b1.w0) &&& b2.w0),
   b0.w1 ^^^ ((~~~b1.w1) &&& b2.w1),
   b0.w2 ^^^ ((~~~b1.w2) &&& b2.w2),
   b0.w3 ^^^ ((~~~b1.w3) &&& b2.w3),
   b0.w4 ^^^ ((~~~b1.w4) &&& b2.w4),
   b0.w5 ^^^ ((~~~b1.w5) &&& b2.w5),
   b0.w6 ^^^ ((~~~b1.w6) &&& b2.w6),
   b0.w7 ^^^ ((~~~b1.w7) &&& b2.w7)⟩

@[inline] def chiRc8 (b0 b1 b2 : Lane8) (rc : UInt64) : Lane8 :=
  ⟨(b0.w0 ^^^ ((~~~b1.w0) &&& b2.w0)) ^^^ rc,
   (b0.w1 ^^^ ((~~~b1.w1) &&& b2.w1)) ^^^ rc,
   (b0.w2 ^^^ ((~~~b1.w2) &&& b2.w2)) ^^^ rc,
   (b0.w3 ^^^ ((~~~b1.w3) &&& b2.w3)) ^^^ rc,
   (b0.w4 ^^^ ((~~~b1.w4) &&& b2.w4)) ^^^ rc,
   (b0.w5 ^^^ ((~~~b1.w5) &&& b2.w5)) ^^^ rc,
   (b0.w6 ^^^ ((~~~b1.w6) &&& b2.w6)) ^^^ rc,
   (b0.w7 ^^^ ((~~~b1.w7) &&& b2.w7)) ^^^ rc⟩

@[inline] def rotl1_8 (x : Lane8) : Lane8 :=
  ⟨(x.w0 <<< 1) ||| (x.w0 >>> 63),
   (x.w1 <<< 1) ||| (x.w1 >>> 63),
   (x.w2 <<< 1) ||| (x.w2 >>> 63),
   (x.w3 <<< 1) ||| (x.w3 >>> 63),
   (x.w4 <<< 1) ||| (x.w4 >>> 63),
   (x.w5 <<< 1) ||| (x.w5 >>> 63),
   (x.w6 <<< 1) ||| (x.w6 >>> 63),
   (x.w7 <<< 1) ||| (x.w7 >>> 63)⟩

@[inline] def rotl8 (x : Lane8) (sh invSh : UInt64) : Lane8 :=
  ⟨(x.w0 <<< sh) ||| (x.w0 >>> invSh),
   (x.w1 <<< sh) ||| (x.w1 >>> invSh),
   (x.w2 <<< sh) ||| (x.w2 >>> invSh),
   (x.w3 <<< sh) ||| (x.w3 >>> invSh),
   (x.w4 <<< sh) ||| (x.w4 >>> invSh),
   (x.w5 <<< sh) ||| (x.w5 >>> invSh),
   (x.w6 <<< sh) ||| (x.w6 >>> invSh),
   (x.w7 <<< sh) ||| (x.w7 >>> invSh)⟩

def round25x8 (s : State25x8) (rc : UInt64) : State25x8 :=
  let c0 := xor5_8 s.a00 s.a05 s.a10 s.a15 s.a20
  let c1 := xor5_8 s.a01 s.a06 s.a11 s.a16 s.a21
  let c2 := xor5_8 s.a02 s.a07 s.a12 s.a17 s.a22
  let c3 := xor5_8 s.a03 s.a08 s.a13 s.a18 s.a23
  let c4 := xor5_8 s.a04 s.a09 s.a14 s.a19 s.a24
  let d0 := xor8 c4 (rotl1_8 c1)
  let d1 := xor8 c0 (rotl1_8 c2)
  let d2 := xor8 c1 (rotl1_8 c3)
  let d3 := xor8 c2 (rotl1_8 c4)
  let d4 := xor8 c3 (rotl1_8 c0)
  let b00 := xor8 s.a00 d0
  let b10 := rotl8 (xor8 s.a01 d1) 1 63
  let b20 := rotl8 (xor8 s.a02 d2) 62 2
  let b05 := rotl8 (xor8 s.a03 d3) 28 36
  let b15 := rotl8 (xor8 s.a04 d4) 27 37
  let b16 := rotl8 (xor8 s.a05 d0) 36 28
  let b01 := rotl8 (xor8 s.a06 d1) 44 20
  let b11 := rotl8 (xor8 s.a07 d2) 6 58
  let b21 := rotl8 (xor8 s.a08 d3) 55 9
  let b06 := rotl8 (xor8 s.a09 d4) 20 44
  let b07 := rotl8 (xor8 s.a10 d0) 3 61
  let b17 := rotl8 (xor8 s.a11 d1) 10 54
  let b02 := rotl8 (xor8 s.a12 d2) 43 21
  let b12 := rotl8 (xor8 s.a13 d3) 25 39
  let b22 := rotl8 (xor8 s.a14 d4) 39 25
  let b23 := rotl8 (xor8 s.a15 d0) 41 23
  let b08 := rotl8 (xor8 s.a16 d1) 45 19
  let b18 := rotl8 (xor8 s.a17 d2) 15 49
  let b03 := rotl8 (xor8 s.a18 d3) 21 43
  let b13 := rotl8 (xor8 s.a19 d4) 8 56
  let b14 := rotl8 (xor8 s.a20 d0) 18 46
  let b24 := rotl8 (xor8 s.a21 d1) 2 62
  let b09 := rotl8 (xor8 s.a22 d2) 61 3
  let b19 := rotl8 (xor8 s.a23 d3) 56 8
  let b04 := rotl8 (xor8 s.a24 d4) 14 50
  ⟨chiRc8 b00 b01 b02 rc,
   chi8 b01 b02 b03,
   chi8 b02 b03 b04,
   chi8 b03 b04 b00,
   chi8 b04 b00 b01,
   chi8 b05 b06 b07,
   chi8 b06 b07 b08,
   chi8 b07 b08 b09,
   chi8 b08 b09 b05,
   chi8 b09 b05 b06,
   chi8 b10 b11 b12,
   chi8 b11 b12 b13,
   chi8 b12 b13 b14,
   chi8 b13 b14 b10,
   chi8 b14 b10 b11,
   chi8 b15 b16 b17,
   chi8 b16 b17 b18,
   chi8 b17 b18 b19,
   chi8 b18 b19 b15,
   chi8 b19 b15 b16,
   chi8 b20 b21 b22,
   chi8 b21 b22 b23,
   chi8 b22 b23 b24,
   chi8 b23 b24 b20,
   chi8 b24 b20 b21⟩

def rounds25x8 (count : Nat) : Nat → State25x8 → State25x8 :=
  Nat.rec (fun _ s => s)
    (fun _ previous i s => previous (i + 1) (round25x8 s (Model.Keccak.roundConstant i)))
    count

def keccakF1600_25x8 (s : State25x8) : State25x8 :=
  rounds25x8 24 0 s

@[inline] def loadLane8Contig (buf : @& ByteArray) (laneIdx : USize) : Lane8 :=
  let base := laneIdx <<< 6
  ⟨loadU64 buf base,
   loadU64 buf (base + 8),
   loadU64 buf (base + 16),
   loadU64 buf (base + 24),
   loadU64 buf (base + 32),
   loadU64 buf (base + 40),
   loadU64 buf (base + 48),
   loadU64 buf (base + 56)⟩

@[inline] def storeLane8Contig (buf : ByteArray) (laneIdx : USize) (v : Lane8) : ByteArray :=
  let base := laneIdx <<< 6
  let buf := storeU64 buf base v.w0
  let buf := storeU64 buf (base + 8) v.w1
  let buf := storeU64 buf (base + 16) v.w2
  let buf := storeU64 buf (base + 24) v.w3
  let buf := storeU64 buf (base + 32) v.w4
  let buf := storeU64 buf (base + 40) v.w5
  let buf := storeU64 buf (base + 48) v.w6
  storeU64 buf (base + 56) v.w7

def keccakF1600_8x (stateBytes : ByteArray) : ByteArray :=
  let st : State25x8 :=
    ⟨loadLane8Contig stateBytes 0,
     loadLane8Contig stateBytes 1,
     loadLane8Contig stateBytes 2,
     loadLane8Contig stateBytes 3,
     loadLane8Contig stateBytes 4,
     loadLane8Contig stateBytes 5,
     loadLane8Contig stateBytes 6,
     loadLane8Contig stateBytes 7,
     loadLane8Contig stateBytes 8,
     loadLane8Contig stateBytes 9,
     loadLane8Contig stateBytes 10,
     loadLane8Contig stateBytes 11,
     loadLane8Contig stateBytes 12,
     loadLane8Contig stateBytes 13,
     loadLane8Contig stateBytes 14,
     loadLane8Contig stateBytes 15,
     loadLane8Contig stateBytes 16,
     loadLane8Contig stateBytes 17,
     loadLane8Contig stateBytes 18,
     loadLane8Contig stateBytes 19,
     loadLane8Contig stateBytes 20,
     loadLane8Contig stateBytes 21,
     loadLane8Contig stateBytes 22,
     loadLane8Contig stateBytes 23,
     loadLane8Contig stateBytes 24⟩
  let out := keccakF1600_25x8 st
  let b := storeLane8Contig stateBytes 0 out.a00
  let b := storeLane8Contig b 1 out.a01
  let b := storeLane8Contig b 2 out.a02
  let b := storeLane8Contig b 3 out.a03
  let b := storeLane8Contig b 4 out.a04
  let b := storeLane8Contig b 5 out.a05
  let b := storeLane8Contig b 6 out.a06
  let b := storeLane8Contig b 7 out.a07
  let b := storeLane8Contig b 8 out.a08
  let b := storeLane8Contig b 9 out.a09
  let b := storeLane8Contig b 10 out.a10
  let b := storeLane8Contig b 11 out.a11
  let b := storeLane8Contig b 12 out.a12
  let b := storeLane8Contig b 13 out.a13
  let b := storeLane8Contig b 14 out.a14
  let b := storeLane8Contig b 15 out.a15
  let b := storeLane8Contig b 16 out.a16
  let b := storeLane8Contig b 17 out.a17
  let b := storeLane8Contig b 18 out.a18
  let b := storeLane8Contig b 19 out.a19
  let b := storeLane8Contig b 20 out.a20
  let b := storeLane8Contig b 21 out.a21
  let b := storeLane8Contig b 22 out.a22
  let b := storeLane8Contig b 23 out.a23
  storeLane8Contig b 24 out.a24

@[inline] def gatherLane8 (buf : @& ByteArray) (baseOff stride wordOff : USize) : Lane8 :=
  let p0 := baseOff + wordOff
  let p1 := p0 + stride
  let p2 := p1 + stride
  let p3 := p2 + stride
  let p4 := p3 + stride
  let p5 := p4 + stride
  let p6 := p5 + stride
  let p7 := p6 + stride
  ⟨loadU64 buf p0, loadU64 buf p1, loadU64 buf p2, loadU64 buf p3,
   loadU64 buf p4, loadU64 buf p5, loadU64 buf p6, loadU64 buf p7⟩

@[inline] def storeDigests8x (out : ByteArray) (outBase : USize)
    (a00 a01 a02 a03 : Lane8) : ByteArray :=
  let out := storeU64 out outBase a00.w0
  let out := storeU64 out (outBase + 8) a01.w0
  let out := storeU64 out (outBase + 16) a02.w0
  let out := storeU64 out (outBase + 24) a03.w0
  let out := storeU64 out (outBase + 32) a00.w1
  let out := storeU64 out (outBase + 40) a01.w1
  let out := storeU64 out (outBase + 48) a02.w1
  let out := storeU64 out (outBase + 56) a03.w1
  let out := storeU64 out (outBase + 64) a00.w2
  let out := storeU64 out (outBase + 72) a01.w2
  let out := storeU64 out (outBase + 80) a02.w2
  let out := storeU64 out (outBase + 88) a03.w2
  let out := storeU64 out (outBase + 96) a00.w3
  let out := storeU64 out (outBase + 104) a01.w3
  let out := storeU64 out (outBase + 112) a02.w3
  let out := storeU64 out (outBase + 120) a03.w3
  let out := storeU64 out (outBase + 128) a00.w4
  let out := storeU64 out (outBase + 136) a01.w4
  let out := storeU64 out (outBase + 144) a02.w4
  let out := storeU64 out (outBase + 152) a03.w4
  let out := storeU64 out (outBase + 160) a00.w5
  let out := storeU64 out (outBase + 168) a01.w5
  let out := storeU64 out (outBase + 176) a02.w5
  let out := storeU64 out (outBase + 184) a03.w5
  let out := storeU64 out (outBase + 192) a00.w6
  let out := storeU64 out (outBase + 200) a01.w6
  let out := storeU64 out (outBase + 208) a02.w6
  let out := storeU64 out (outBase + 216) a03.w6
  let out := storeU64 out (outBase + 224) a00.w7
  let out := storeU64 out (outBase + 232) a01.w7
  let out := storeU64 out (outBase + 240) a02.w7
  storeU64 out (outBase + 248) a03.w7

@[inline] def compress8PairsAt (children : @& ByteArray) (inBase : USize)
    (parents : ByteArray) (outBase : USize) : ByteArray :=
  let stride : USize := 64
  let w0 := gatherLane8 children inBase stride 0
  let w1 := gatherLane8 children inBase stride 8
  let w2 := gatherLane8 children inBase stride 16
  let w3 := gatherLane8 children inBase stride 24
  let w4 := gatherLane8 children inBase stride 32
  let w5 := gatherLane8 children inBase stride 40
  let w6 := gatherLane8 children inBase stride 48
  let w7 := gatherLane8 children inBase stride 56
  let z := zeroLane8
  let st0 : State25x8 :=
    ⟨w0, w1, w2, w3, w4, w5, w6, w7,
     splatLane8 1, z, z, z, z, z, z, z,
     splatLane8 0x8000000000000000, z, z, z, z, z, z, z, z⟩
  let st := keccakF1600_25x8 st0
  storeDigests8x parents outBase st.a00 st.a01 st.a02 st.a03

@[inline] def compress1PairAt (children : @& ByteArray) (inBase : USize)
    (parents : ByteArray) (outBase : USize) : ByteArray :=
  let st0 : Model.Keccak.State25 :=
    ⟨loadU64 children inBase,
     loadU64 children (inBase + 8),
     loadU64 children (inBase + 16),
     loadU64 children (inBase + 24),
     loadU64 children (inBase + 32),
     loadU64 children (inBase + 40),
     loadU64 children (inBase + 48),
     loadU64 children (inBase + 56),
     1, 0, 0, 0, 0, 0, 0, 0,
     0x8000000000000000, 0, 0, 0, 0, 0, 0, 0, 0⟩
  let st := Model.Keccak.keccakF1600 st0
  let parents := storeU64 parents outBase st.a00
  let parents := storeU64 parents (outBase + 8) st.a01
  let parents := storeU64 parents (outBase + 16) st.a02
  storeU64 parents (outBase + 24) st.a03

def lean_xmss_merkle_compress_level (children : @& ByteArray) : ByteArray :=
  let numChildren := children.size / 32
  let numParents := numChildren / 2
  let out := zeroByteArray (numParents * 32)
  let groups8 := numParents / 8
  let remPairs := numParents % 8
  let out := foldUSize groups8
    (fun acc g =>
      let inBase := g * (512 : USize)
      let outBase := g * (256 : USize)
      compress8PairsAt children inBase acc outBase)
    out
  let tailInBase := USize.ofNat (groups8 * 512)
  let tailOutBase := USize.ofNat (groups8 * 256)
  foldUSize remPairs
    (fun acc r =>
      let inBase := tailInBase + r * (64 : USize)
      let outBase := tailOutBase + r * (32 : USize)
      compress1PairAt children inBase acc outBase)
    out

@[inline] def gatherLeafWord8 (codeword : @& ByteArray) (rowBase stride : USize)
    (width padZeros wordIdx : Nat) : Lane8 :=
  if wordIdx < padZeros then zeroLane8
  else
    let col := wordIdx - padZeros
    if col < width then
      gatherLane8 codeword rowBase stride (USize.ofNat (col * 8))
    else zeroLane8

@[inline] def absorb17x8 (s : State25x8)
    (w00 w01 w02 w03 w04 w05 w06 w07 w08 w09 w10 w11 w12 w13 w14 w15 w16 : Lane8) : State25x8 :=
  keccakF1600_25x8
    { s with
      a00 := xor8 s.a00 w00
      a01 := xor8 s.a01 w01
      a02 := xor8 s.a02 w02
      a03 := xor8 s.a03 w03
      a04 := xor8 s.a04 w04
      a05 := xor8 s.a05 w05
      a06 := xor8 s.a06 w06
      a07 := xor8 s.a07 w07
      a08 := xor8 s.a08 w08
      a09 := xor8 s.a09 w09
      a10 := xor8 s.a10 w10
      a11 := xor8 s.a11 w11
      a12 := xor8 s.a12 w12
      a13 := xor8 s.a13 w13
      a14 := xor8 s.a14 w14
      a15 := xor8 s.a15 w15
      a16 := xor8 s.a16 w16 }

@[inline] def absorbFinal13x8 (s : State25x8)
    (w00 w01 w02 w03 w04 w05 w06 w07 w08 w09 w10 w11 w12 : Lane8) : State25x8 :=
  keccakF1600_25x8
    { s with
      a00 := xor8 s.a00 w00
      a01 := xor8 s.a01 w01
      a02 := xor8 s.a02 w02
      a03 := xor8 s.a03 w03
      a04 := xor8 s.a04 w04
      a05 := xor8 s.a05 w05
      a06 := xor8 s.a06 w06
      a07 := xor8 s.a07 w07
      a08 := xor8 s.a08 w08
      a09 := xor8 s.a09 w09
      a10 := xor8 s.a10 w10
      a11 := xor8 s.a11 w11
      a12 := xor8 s.a12 w12
      a13 := xor8 s.a13 (splatLane8 1)
      a16 := xor8 s.a16 (splatLane8 0x8000000000000000) }

def splatState25 (s : Model.Keccak.State25) : State25x8 :=
  ⟨splatLane8 s.a00, splatLane8 s.a01, splatLane8 s.a02, splatLane8 s.a03, splatLane8 s.a04,
   splatLane8 s.a05, splatLane8 s.a06, splatLane8 s.a07, splatLane8 s.a08, splatLane8 s.a09,
   splatLane8 s.a10, splatLane8 s.a11, splatLane8 s.a12, splatLane8 s.a13, splatLane8 s.a14,
   splatLane8 s.a15, splatLane8 s.a16, splatLane8 s.a17, splatLane8 s.a18, splatLane8 s.a19,
   splatLane8 s.a20, splatLane8 s.a21, splatLane8 s.a22, splatLane8 s.a23, splatLane8 s.a24⟩

def zeroState25 : Model.Keccak.State25 :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

def zeroPrefixState25 (n : Nat) : Model.Keccak.State25 :=
  Nat.rec zeroState25 (fun _ st => Model.Keccak.keccakF1600 st) n

@[inline] def hash8LeavesAt (st0 st1 st2 st3 : State25x8)
    (codeword : @& ByteArray) (rowBase stride : USize) (width padZeros : Nat)
    (out : ByteArray) (outBase : USize) : ByteArray :=
  let s1 :=
    if padZeros ≥ 17 then st1
    else
      absorb17x8 st0
        (gatherLeafWord8 codeword rowBase stride width padZeros 0)
        (gatherLeafWord8 codeword rowBase stride width padZeros 1)
        (gatherLeafWord8 codeword rowBase stride width padZeros 2)
        (gatherLeafWord8 codeword rowBase stride width padZeros 3)
        (gatherLeafWord8 codeword rowBase stride width padZeros 4)
        (gatherLeafWord8 codeword rowBase stride width padZeros 5)
        (gatherLeafWord8 codeword rowBase stride width padZeros 6)
        (gatherLeafWord8 codeword rowBase stride width padZeros 7)
        (gatherLeafWord8 codeword rowBase stride width padZeros 8)
        (gatherLeafWord8 codeword rowBase stride width padZeros 9)
        (gatherLeafWord8 codeword rowBase stride width padZeros 10)
        (gatherLeafWord8 codeword rowBase stride width padZeros 11)
        (gatherLeafWord8 codeword rowBase stride width padZeros 12)
        (gatherLeafWord8 codeword rowBase stride width padZeros 13)
        (gatherLeafWord8 codeword rowBase stride width padZeros 14)
        (gatherLeafWord8 codeword rowBase stride width padZeros 15)
        (gatherLeafWord8 codeword rowBase stride width padZeros 16)
  let s2 :=
    if padZeros ≥ 34 then st2
    else
      absorb17x8 s1
        (gatherLeafWord8 codeword rowBase stride width padZeros 17)
        (gatherLeafWord8 codeword rowBase stride width padZeros 18)
        (gatherLeafWord8 codeword rowBase stride width padZeros 19)
        (gatherLeafWord8 codeword rowBase stride width padZeros 20)
        (gatherLeafWord8 codeword rowBase stride width padZeros 21)
        (gatherLeafWord8 codeword rowBase stride width padZeros 22)
        (gatherLeafWord8 codeword rowBase stride width padZeros 23)
        (gatherLeafWord8 codeword rowBase stride width padZeros 24)
        (gatherLeafWord8 codeword rowBase stride width padZeros 25)
        (gatherLeafWord8 codeword rowBase stride width padZeros 26)
        (gatherLeafWord8 codeword rowBase stride width padZeros 27)
        (gatherLeafWord8 codeword rowBase stride width padZeros 28)
        (gatherLeafWord8 codeword rowBase stride width padZeros 29)
        (gatherLeafWord8 codeword rowBase stride width padZeros 30)
        (gatherLeafWord8 codeword rowBase stride width padZeros 31)
        (gatherLeafWord8 codeword rowBase stride width padZeros 32)
        (gatherLeafWord8 codeword rowBase stride width padZeros 33)
  let s3 :=
    if padZeros ≥ 51 then st3
    else
      absorb17x8 s2
        (gatherLeafWord8 codeword rowBase stride width padZeros 34)
        (gatherLeafWord8 codeword rowBase stride width padZeros 35)
        (gatherLeafWord8 codeword rowBase stride width padZeros 36)
        (gatherLeafWord8 codeword rowBase stride width padZeros 37)
        (gatherLeafWord8 codeword rowBase stride width padZeros 38)
        (gatherLeafWord8 codeword rowBase stride width padZeros 39)
        (gatherLeafWord8 codeword rowBase stride width padZeros 40)
        (gatherLeafWord8 codeword rowBase stride width padZeros 41)
        (gatherLeafWord8 codeword rowBase stride width padZeros 42)
        (gatherLeafWord8 codeword rowBase stride width padZeros 43)
        (gatherLeafWord8 codeword rowBase stride width padZeros 44)
        (gatherLeafWord8 codeword rowBase stride width padZeros 45)
        (gatherLeafWord8 codeword rowBase stride width padZeros 46)
        (gatherLeafWord8 codeword rowBase stride width padZeros 47)
        (gatherLeafWord8 codeword rowBase stride width padZeros 48)
        (gatherLeafWord8 codeword rowBase stride width padZeros 49)
        (gatherLeafWord8 codeword rowBase stride width padZeros 50)
  let sf :=
    absorbFinal13x8 s3
      (gatherLeafWord8 codeword rowBase stride width padZeros 51)
      (gatherLeafWord8 codeword rowBase stride width padZeros 52)
      (gatherLeafWord8 codeword rowBase stride width padZeros 53)
      (gatherLeafWord8 codeword rowBase stride width padZeros 54)
      (gatherLeafWord8 codeword rowBase stride width padZeros 55)
      (gatherLeafWord8 codeword rowBase stride width padZeros 56)
      (gatherLeafWord8 codeword rowBase stride width padZeros 57)
      (gatherLeafWord8 codeword rowBase stride width padZeros 58)
      (gatherLeafWord8 codeword rowBase stride width padZeros 59)
      (gatherLeafWord8 codeword rowBase stride width padZeros 60)
      (gatherLeafWord8 codeword rowBase stride width padZeros 61)
      (gatherLeafWord8 codeword rowBase stride width padZeros 62)
      (gatherLeafWord8 codeword rowBase stride width padZeros 63)
  storeDigests8x out outBase sf.a00 sf.a01 sf.a02 sf.a03

@[inline] def leafWord1 (codeword : @& ByteArray) (rowBase : USize)
    (width padZeros wordIdx : Nat) : UInt64 :=
  if wordIdx < padZeros then 0
  else
    let col := wordIdx - padZeros
    if col < width then
      loadU64 codeword (rowBase + USize.ofNat (col * 8))
    else 0

@[inline] def absorb17_1 (s : Model.Keccak.State25)
    (w00 w01 w02 w03 w04 w05 w06 w07 w08 w09 w10 w11 w12 w13 w14 w15 w16 : UInt64) :
    Model.Keccak.State25 :=
  Model.Keccak.keccakF1600
    { s with
      a00 := s.a00 ^^^ w00
      a01 := s.a01 ^^^ w01
      a02 := s.a02 ^^^ w02
      a03 := s.a03 ^^^ w03
      a04 := s.a04 ^^^ w04
      a05 := s.a05 ^^^ w05
      a06 := s.a06 ^^^ w06
      a07 := s.a07 ^^^ w07
      a08 := s.a08 ^^^ w08
      a09 := s.a09 ^^^ w09
      a10 := s.a10 ^^^ w10
      a11 := s.a11 ^^^ w11
      a12 := s.a12 ^^^ w12
      a13 := s.a13 ^^^ w13
      a14 := s.a14 ^^^ w14
      a15 := s.a15 ^^^ w15
      a16 := s.a16 ^^^ w16 }

@[inline] def hash1LeafAt (st1 st2 st3 : Model.Keccak.State25)
    (codeword : @& ByteArray) (rowBase : USize) (width padZeros : Nat)
    (out : ByteArray) (outBase : USize) : ByteArray :=
  let s1 :=
    if padZeros ≥ 17 then st1
    else
      absorb17_1 zeroState25
        (leafWord1 codeword rowBase width padZeros 0)
        (leafWord1 codeword rowBase width padZeros 1)
        (leafWord1 codeword rowBase width padZeros 2)
        (leafWord1 codeword rowBase width padZeros 3)
        (leafWord1 codeword rowBase width padZeros 4)
        (leafWord1 codeword rowBase width padZeros 5)
        (leafWord1 codeword rowBase width padZeros 6)
        (leafWord1 codeword rowBase width padZeros 7)
        (leafWord1 codeword rowBase width padZeros 8)
        (leafWord1 codeword rowBase width padZeros 9)
        (leafWord1 codeword rowBase width padZeros 10)
        (leafWord1 codeword rowBase width padZeros 11)
        (leafWord1 codeword rowBase width padZeros 12)
        (leafWord1 codeword rowBase width padZeros 13)
        (leafWord1 codeword rowBase width padZeros 14)
        (leafWord1 codeword rowBase width padZeros 15)
        (leafWord1 codeword rowBase width padZeros 16)
  let s2 :=
    if padZeros ≥ 34 then st2
    else
      absorb17_1 s1
        (leafWord1 codeword rowBase width padZeros 17)
        (leafWord1 codeword rowBase width padZeros 18)
        (leafWord1 codeword rowBase width padZeros 19)
        (leafWord1 codeword rowBase width padZeros 20)
        (leafWord1 codeword rowBase width padZeros 21)
        (leafWord1 codeword rowBase width padZeros 22)
        (leafWord1 codeword rowBase width padZeros 23)
        (leafWord1 codeword rowBase width padZeros 24)
        (leafWord1 codeword rowBase width padZeros 25)
        (leafWord1 codeword rowBase width padZeros 26)
        (leafWord1 codeword rowBase width padZeros 27)
        (leafWord1 codeword rowBase width padZeros 28)
        (leafWord1 codeword rowBase width padZeros 29)
        (leafWord1 codeword rowBase width padZeros 30)
        (leafWord1 codeword rowBase width padZeros 31)
        (leafWord1 codeword rowBase width padZeros 32)
        (leafWord1 codeword rowBase width padZeros 33)
  let s3 :=
    if padZeros ≥ 51 then st3
    else
      absorb17_1 s2
        (leafWord1 codeword rowBase width padZeros 34)
        (leafWord1 codeword rowBase width padZeros 35)
        (leafWord1 codeword rowBase width padZeros 36)
        (leafWord1 codeword rowBase width padZeros 37)
        (leafWord1 codeword rowBase width padZeros 38)
        (leafWord1 codeword rowBase width padZeros 39)
        (leafWord1 codeword rowBase width padZeros 40)
        (leafWord1 codeword rowBase width padZeros 41)
        (leafWord1 codeword rowBase width padZeros 42)
        (leafWord1 codeword rowBase width padZeros 43)
        (leafWord1 codeword rowBase width padZeros 44)
        (leafWord1 codeword rowBase width padZeros 45)
        (leafWord1 codeword rowBase width padZeros 46)
        (leafWord1 codeword rowBase width padZeros 47)
        (leafWord1 codeword rowBase width padZeros 48)
        (leafWord1 codeword rowBase width padZeros 49)
        (leafWord1 codeword rowBase width padZeros 50)
  let sf :=
    Model.Keccak.keccakF1600
      { s3 with
        a00 := s3.a00 ^^^ leafWord1 codeword rowBase width padZeros 51
        a01 := s3.a01 ^^^ leafWord1 codeword rowBase width padZeros 52
        a02 := s3.a02 ^^^ leafWord1 codeword rowBase width padZeros 53
        a03 := s3.a03 ^^^ leafWord1 codeword rowBase width padZeros 54
        a04 := s3.a04 ^^^ leafWord1 codeword rowBase width padZeros 55
        a05 := s3.a05 ^^^ leafWord1 codeword rowBase width padZeros 56
        a06 := s3.a06 ^^^ leafWord1 codeword rowBase width padZeros 57
        a07 := s3.a07 ^^^ leafWord1 codeword rowBase width padZeros 58
        a08 := s3.a08 ^^^ leafWord1 codeword rowBase width padZeros 59
        a09 := s3.a09 ^^^ leafWord1 codeword rowBase width padZeros 60
        a10 := s3.a10 ^^^ leafWord1 codeword rowBase width padZeros 61
        a11 := s3.a11 ^^^ leafWord1 codeword rowBase width padZeros 62
        a12 := s3.a12 ^^^ leafWord1 codeword rowBase width padZeros 63
        a13 := s3.a13 ^^^ 1
        a16 := s3.a16 ^^^ 0x8000000000000000 }
  let out := storeU64 out outBase sf.a00
  let out := storeU64 out (outBase + 8) sf.a01
  let out := storeU64 out (outBase + 16) sf.a02
  storeU64 out (outBase + 24) sf.a03

@[inline] def hashChunkLeaves (st0 st1 st2 st3 : State25x8)
    (st1_1 st2_1 st3_1 : Model.Keccak.State25)
    (codeword : @& ByteArray) (startRow numChunkRows width padZeros : Nat) : ByteArray :=
  let rowBytes := width * 8
  let out := zeroByteArray (numChunkRows * 32)
  let stride := USize.ofNat rowBytes
  let groupStride := stride <<< 3
  let groups8 := numChunkRows / 8
  let remRows := numChunkRows % 8
  let baseByteOff := USize.ofNat (startRow * rowBytes)
  let out := foldUSize groups8
    (fun acc g =>
      let rowBase := baseByteOff + g * groupStride
      let outBase := g * (256 : USize)
      hash8LeavesAt st0 st1 st2 st3 codeword rowBase stride width padZeros acc outBase)
    out
  let tailRowBase := baseByteOff + USize.ofNat (groups8 * 8 * rowBytes)
  let tailOutBase := USize.ofNat (groups8 * 256)
  foldUSize remRows
    (fun acc r =>
      let rowBase := tailRowBase + r * stride
      let outBase := tailOutBase + r * (32 : USize)
      hash1LeafAt st1_1 st2_1 st3_1 codeword rowBase width padZeros acc outBase)
    out

def lean_xmss_merkle_hash_leaves (codeword : @& ByteArray) (width leafWords : Nat) : ByteArray :=
  if width = 0 then ByteArray.empty
  else
    let rowBytes := width * 8
    let numRows := codeword.size / rowBytes
    let padZeros := if leafWords ≥ width then leafWords - width else 0
    let st1_1 := zeroPrefixState25 1
    let st2_1 := zeroPrefixState25 2
    let st3_1 := zeroPrefixState25 3
    let st0_8 := splatState25 zeroState25
    let st1_8 := splatState25 st1_1
    let st2_8 := splatState25 st2_1
    let st3_8 := splatState25 st3_1
    hashChunkLeaves st0_8 st1_8 st2_8 st3_8 st1_1 st2_1 st3_1 codeword 0 numRows width padZeros

def lean_xmss_merkle_subtree_root_chunk (codeword : @& ByteArray)
    (startRow numChunkRows width leafWords : Nat) : ByteArray :=
  let st1_1 := zeroPrefixState25 1
  let st2_1 := zeroPrefixState25 2
  let st3_1 := zeroPrefixState25 3
  let st0_8 := splatState25 zeroState25
  let st1_8 := splatState25 st1_1
  let st2_8 := splatState25 st2_1
  let st3_8 := splatState25 st3_1
  let padZeros := if leafWords ≥ width then leafWords - width else 0
  let leaves :=
    hashChunkLeaves st0_8 st1_8 st2_8 st3_8 st1_1 st2_1 st3_1
      codeword startRow numChunkRows width padZeros
  let depth := numChunkRows.log2
  let rootLevel := Model.Pcs.Ntt.foldRange depth
    (fun cur _ => lean_xmss_merkle_compress_level cur)
    leaves
  if rootLevel.size ≥ 32 then rootLevel.extract 0 32 else ByteArray.empty

def lean_xmss_merkle_build_flat (leaves : @& ByteArray) : ByteArray :=
  let numLeaves := leaves.size / 32
  if numLeaves = 0 then ByteArray.empty
  else
    let depth := numLeaves.log2
    let totalNodes := 2 * numLeaves
    let tree := zeroByteArray (totalNodes * 32)
    let leafStart := USize.ofNat (numLeaves * 32)
    let tree := foldUSize (numLeaves * 4)
      (fun acc w =>
        let off := w <<< 3
        storeU64 acc (leafStart + off) (loadU64 leaves off))
      tree
    Model.Pcs.Ntt.foldRange depth
      (fun acc step =>
        let level := depth - 1 - step
        let levelCount := 1 <<< level
        let childStart := USize.ofNat ((2 * levelCount) * 32)
        let parentStart := USize.ofNat (levelCount * 32)
        let groups8 := levelCount / 8
        let remPairs := levelCount % 8
        let acc := foldUSize groups8
          (fun t g =>
            let inBase := childStart + g * (512 : USize)
            let outBase := parentStart + g * (256 : USize)
            compress8PairsAt t inBase t outBase)
          acc
        let tailIn := childStart + USize.ofNat (groups8 * 512)
        let tailOut := parentStart + USize.ofNat (groups8 * 256)
        foldUSize remPairs
          (fun t r =>
            let inBase := tailIn + r * (64 : USize)
            let outBase := tailOut + r * (32 : USize)
            compress1PairAt t inBase t outBase)
          acc)
      tree

def lean_xmss_merkle_root_from_flat (flatTree : @& ByteArray) : ByteArray :=
  if flatTree.size ≥ 64 then flatTree.extract 32 64 else ByteArray.empty

def lean_xmss_merkle_root_from_leaves (leaves : ByteArray) : ByteArray :=
  let numLeaves := leaves.size / 32
  if numLeaves ≤ 1 then
    if leaves.size ≥ 32 then leaves.extract 0 32 else ByteArray.empty
  else
    let depth := numLeaves.log2
    let rootLevel := Model.Pcs.Ntt.foldRange depth
      (fun cur _ => lean_xmss_merkle_compress_level cur)
      leaves
    rootLevel.extract 0 32

def packFirstCosetBytes (message : @& ByteArray) (lanes width logRows : Nat) : ByteArray :=
  let rows := 1 <<< logRows
  let totalWords := rows * width
  let out := ByteArray.emptyWithCapacity (totalWords * 8)
  Model.Pcs.Ntt.foldRange rows
    (fun acc rowIdx =>
      Model.Pcs.Ntt.foldRange width
        (fun acc2 col =>
          let w :=
            if col + lanes ≥ width then
              let msgIdx := (width - 1 - col) * rows + rowIdx
              loadU64 message (USize.ofNat (msgIdx * 8))
            else 0
          pushU64LE acc2 w)
        acc)
    out

def lean_xmss_pcs_commit_root (message : @& ByteArray) (lanes logRows logInvRate : Nat) : ByteArray :=
  let width := ((lanes + 7) / 8) * 8
  let logD := logRows + logInvRate
  let twiddles := Native.Kernels.Ntt.buildTwiddleSlab logD
  let first := packFirstCosetBytes message lanes width logRows
  let rate := 1 <<< logInvRate
  let cosetRoots := ByteArray.emptyWithCapacity (rate * 32)
  let cosetRoots := Model.Pcs.Ntt.foldRange rate
    (fun acc c =>
      let encoded := Native.Kernels.Ntt.encodeCosetBytes first twiddles width logRows logInvRate c
      let leaves := lean_xmss_merkle_hash_leaves encoded width 64
      let r := lean_xmss_merkle_root_from_leaves leaves
      let acc := pushU64LE acc (loadU64 r 0)
      let acc := pushU64LE acc (loadU64 r 8)
      let acc := pushU64LE acc (loadU64 r 16)
      pushU64LE acc (loadU64 r 24))
    cosetRoots
  lean_xmss_merkle_root_from_leaves cosetRoots

def encodeCosetParallel8 (firstCoset : @& ByteArray) (twiddles : @& ByteArray)
    (lanes logRows logInvRate coset : Nat) : ByteArray :=
  if logRows < 6 then
    Native.Kernels.Ntt.encodeCosetBytes firstCoset twiddles lanes logRows logInvRate coset
  else
    let logD := logRows + logInvRate
    let buf := firstCoset.extract 0 firstCoset.size
    let buf :=
      Model.Pcs.Ntt.foldRange 3
        (fun d step =>
          let curLayer := logInvRate + step
          let localBlocks := 1 <<< step
          let half := 1 <<< (logRows - step - 1)
          let lanesUS := USize.ofNat lanes
          let halfUS := USize.ofNat half
          let twoHalfUS := halfUS <<< 1
          let halfStrideBytes := (halfUS * lanesUS) <<< 3
          let curLayerUS := USize.ofNat curLayer
          let blockBase := (USize.ofNat coset) <<< (USize.ofNat step)
          foldUSize localBlocks
            (fun dBlk localBlk =>
              let t := Native.Kernels.Ntt.twiddleAt twiddles curLayerUS (blockBase + localBlk)
              let blockRowBase := localBlk * twoHalfUS
              foldUSize half
                (fun dRow rowIdx =>
                  let topByteBase := ((blockRowBase + rowIdx) * lanesUS) <<< 3
                  let botByteBase := topByteBase + halfStrideBytes
                  Native.Kernels.Ntt.butterflyRowBytes dRow topByteBase botByteBase lanes t)
                dBlk)
            d)
        buf
    let subRows := 1 <<< (logRows - 3)
    let subBytes := subRows * lanes * 8
    let remSteps := logRows - 3
    let subTasks : Array (Task ByteArray) :=
      Model.Pcs.Ntt.foldRange 8
        (fun acc subIdx =>
          let startByte := subIdx * subBytes
          let globalSubCoset := (coset <<< 3) + subIdx
          let tk := Task.spawn (prio := .dedicated) (fun () =>
            let slice := Native.Kernels.Ntt.extractSlice buf startByte subBytes
            Native.Kernels.Ntt.encodeCosetBytes slice twiddles lanes remSteps (logInvRate + 3) globalSubCoset)
          acc.push tk)
        (Array.emptyWithCapacity 8)
    Model.Pcs.Ntt.foldRange 8
      (fun acc subIdx =>
        match subTasks[subIdx]? with
        | some tk =>
          let subRes := tk.get
          Native.Kernels.Ntt.copySlice acc subRes (subIdx * subBytes)
        | none => acc)
      buf

def lean_xmss_pcs_commit_root_parallel (message : @& ByteArray) (lanes logRows logInvRate : Nat) : ByteArray :=
  if logRows < 6 then
    lean_xmss_pcs_commit_root message lanes logRows logInvRate
  else
    let width := ((lanes + 7) / 8) * 8
    let logD := logRows + logInvRate
    let twiddles := Native.Kernels.Ntt.buildTwiddleSlab logD
    let first := packFirstCosetBytes message lanes width logRows
    let rate := 1 <<< logInvRate
    let chunkRows := (1 <<< logRows) / 8
    let cosetTasks : Array (Task ByteArray) :=
      Model.Pcs.Ntt.foldRange rate
        (fun acc c =>
          let tk := Task.spawn (prio := .dedicated) (fun () =>
            let encoded := encodeCosetParallel8 first twiddles width logRows logInvRate c
            let leafTasks : Array (Task ByteArray) :=
              Model.Pcs.Ntt.foldRange 8
                (fun tks ch =>
                  let startR := ch * chunkRows
                  let ltk := Task.spawn (prio := .dedicated) (fun () =>
                    lean_xmss_merkle_subtree_root_chunk encoded startR chunkRows width 64)
                  tks.push ltk)
                (Array.emptyWithCapacity 8)
            let subRoots :=
              Model.Pcs.Ntt.foldRange 8
                (fun sr ch =>
                  match leafTasks[ch]? with
                  | some ltk =>
                    let sub := ltk.get
                    let sr := pushU64LE sr (loadU64 sub 0)
                    let sr := pushU64LE sr (loadU64 sub 8)
                    let sr := pushU64LE sr (loadU64 sub 16)
                    pushU64LE sr (loadU64 sub 24)
                  | none => sr)
                (ByteArray.emptyWithCapacity 256)
            lean_xmss_merkle_root_from_leaves subRoots)
          acc.push tk)
        (Array.emptyWithCapacity rate)
    let cosetRoots :=
      Model.Pcs.Ntt.foldRange rate
        (fun acc c =>
          match cosetTasks[c]? with
          | some tk =>
            let r := tk.get
            let acc := pushU64LE acc (loadU64 r 0)
            let acc := pushU64LE acc (loadU64 r 8)
            let acc := pushU64LE acc (loadU64 r 16)
            pushU64LE acc (loadU64 r 24)
          | none => acc)
        (ByteArray.emptyWithCapacity (rate * 32))
    lean_xmss_merkle_root_from_leaves cosetRoots

end LeanVmXmss.Native.Kernels.Keccak8x
```

---

### `LeanVmXmss/Tests/Unit/NativePcsMerkleKernelTest.lean`
```lean
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
```

GOAL_COMPLETE