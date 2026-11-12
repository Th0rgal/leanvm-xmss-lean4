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
