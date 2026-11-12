import Spec.Witness.Basic
import Model.Keccak.Fast

/-!
# Parallel `ByteArray`-backed VM execution, witness generation, and L0 commit

Pure-Lean, axiom-clean (`{propext, Quot.sound}` only) Phase-1 + L0 commit
implementation (`W3-K4-ZMM-PAR-A`):
* Planar `ByteArray` VM memory (`mc0`, `mc1`, `mc2`, `mState`, `mAccess`) with
  3-state write/link cells (`0 = Unwritten`, `1 = Written`, `2 = Linked`) and
  cold link propagation;
* Pre-built `FastGPow` (`ByteArray` powers + open-addressed `ByteArray` discrete
  log index) and pre-decoded `FastProg` (`ByteArray` op table + dense `hintAt`
  index + integer-indexed witness streams);
* Register-direct `Model.Keccak.keccakF1600Fast` in the VM `KECCAK` opcode;
* Compact `UInt32` per-table trace `ByteArray`s (`Xrow/Srow/Drow/Jrow/Krow`),
  never allocating boxed `StepTrace` or `Array Nat` rows on the hot path;
* 16-task parallel bytecode IV (`ivOfPar`), stacked witness + `qKeccak`
  generation (`buildWitnessPar`), and 16-task parallel L0 PCS commitment
  (`l0RootPar`).
-/

namespace LeanVmXmss.Model.Witness

open Spec.Field (K E)
open Spec.Vm
open Spec.Witness
open Spec.Layout
open Model.Keccak (State25 keccakF1600Fast rounds12Fast zeroState25Fast keccak256FastStream)
open Model.Pcs.Ntt (foldRange foldRangeLoop)

/-! ## Unboxed `ByteArray` `u8` / `u32` / `u64` primitives -/

theorem usizeLtImpSizeLt {n : Nat} {i : USize} (h : i < n.toUSize) : i.toNat < n := by
  rw [USize.lt_iff_toNat_lt] at h
  exact Nat.lt_of_lt_of_le h (Nat.mod_le n USize.size)

theorem byteArraySizeUset (b : ByteArray) (i : USize) (v : UInt8) (h : i.toNat < b.size) :
    (b.uset i v h).size = b.size := by
  cases b
  simp [ByteArray.uset, ByteArray.size, Array.uset]

theorem natMul4OrEqAdd (q k : Nat) (hk : k < 4) : (4 * q) ||| k = 4 * q + k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  have hpow : (2 ^ 2 : Nat) = 4 := rfl
  rw [← hpow]
  have hk2 : k < 2 ^ 2 := hk
  rw [Nat.testBit_two_pow_mul_add _ hk2, Nat.mul_comm (2 ^ 2) q, Nat.testBit_mul_two_pow]
  by_cases hi : i < 2
  · have hge : ¬ (2 ≤ i) := by omega
    simp [hi, hge]
  · have hge : 2 ≤ i := by omega
    have hki : k < 2 ^ i := Nat.lt_of_lt_of_le hk2 (Nat.pow_le_pow_right (by omega) hge)
    simp [hi, hge, Nat.testBit_lt_two_pow hki]

theorem usizeShift2OrLtSize {idx : USize} {n : Nat} (k : Nat) (hk : k ≤ 3)
    (h3 : ((idx <<< 2) ||| 3) < n.toUSize) :
    ((idx <<< 2) ||| USize.ofNat k).toNat < n := by
  have hlt : ((idx <<< 2) ||| 3).toNat < n := usizeLtImpSizeLt h3
  have hsh : (idx <<< 2).toNat = 4 * (idx.toNat % (2 ^ (System.Platform.numBits - 2))) := by
    rw [USize.toNat_shiftLeft]
    rcases System.Platform.numBits_eq with h32 | h64
    · rw [h32]; simp [Nat.shiftLeft_eq]; omega
    · rw [h64]; simp [Nat.shiftLeft_eq]; omega
  have hor3 : ((idx <<< 2) ||| 3).toNat = (idx <<< 2).toNat + 3 := by
    rw [USize.toNat_or]
    have h3nat : (3 : USize).toNat = 3 := by
      change (USize.ofNat 3).toNat = 3
      rw [USize.toNat_ofNat']
      rcases System.Platform.numBits_eq with h32 | h64
      · simp [h32]
      · simp [h64]
    rw [h3nat, hsh]
    exact natMul4OrEqAdd _ 3 (by omega)
  have hork : ((idx <<< 2) ||| USize.ofNat k).toNat = (idx <<< 2).toNat + k := by
    rw [USize.toNat_or]
    have hknat : (USize.ofNat k).toNat = k := by
      rw [USize.toNat_ofNat']
      rcases System.Platform.numBits_eq with h32 | h64
      · simp [h32]; omega
      · simp [h64]; omega
    rw [hknat, hsh]
    exact natMul4OrEqAdd _ k (by omega)
  omega

theorem natMul8OrEqAdd (q k : Nat) (hk : k < 8) : (8 * q) ||| k = 8 * q + k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  have hpow : (2 ^ 3 : Nat) = 8 := rfl
  rw [← hpow]
  have hk3 : k < 2 ^ 3 := hk
  rw [Nat.testBit_two_pow_mul_add _ hk3, Nat.mul_comm (2 ^ 3) q, Nat.testBit_mul_two_pow]
  by_cases hi : i < 3
  · have hge : ¬ (3 ≤ i) := by omega
    simp [hi, hge]
  · have hge : 3 ≤ i := by omega
    have hki : k < 2 ^ i := Nat.lt_of_lt_of_le hk3 (Nat.pow_le_pow_right (by omega) hge)
    simp [hi, hge, Nat.testBit_lt_two_pow hki]

theorem usizeShift3OrLtSize {idx : USize} {n : Nat} (k : Nat) (hk : k ≤ 7)
    (h7 : ((idx <<< 3) ||| 7) < n.toUSize) :
    ((idx <<< 3) ||| USize.ofNat k).toNat < n := by
  have hlt : ((idx <<< 3) ||| 7).toNat < n := usizeLtImpSizeLt h7
  have hsh : (idx <<< 3).toNat = 8 * (idx.toNat % (2 ^ (System.Platform.numBits - 3))) := by
    rw [USize.toNat_shiftLeft]
    rcases System.Platform.numBits_eq with h32 | h64
    · rw [h32]; simp [Nat.shiftLeft_eq]; omega
    · rw [h64]; simp [Nat.shiftLeft_eq]; omega
  have hor7 : ((idx <<< 3) ||| 7).toNat = (idx <<< 3).toNat + 7 := by
    rw [USize.toNat_or]
    have h7nat : (7 : USize).toNat = 7 := by
      change (USize.ofNat 7).toNat = 7
      rw [USize.toNat_ofNat']
      rcases System.Platform.numBits_eq with h32 | h64
      · simp [h32]
      · simp [h64]
    rw [h7nat, hsh]
    exact natMul8OrEqAdd _ 7 (by omega)
  have hork : ((idx <<< 3) ||| USize.ofNat k).toNat = (idx <<< 3).toNat + k := by
    rw [USize.toNat_or]
    have hknat : (USize.ofNat k).toNat = k := by
      rw [USize.toNat_ofNat']
      rcases System.Platform.numBits_eq with h32 | h64
      · simp [h32]; omega
      · simp [h64]; omega
    rw [hknat, hsh]
    exact natMul8OrEqAdd _ k (by omega)
  omega

@[inline] def getU8Fast (b : @& ByteArray) (idx : USize) : UInt8 :=
  if h : idx < b.usize then b.uget idx (usizeLtImpSizeLt h) else 0

@[inline] def setU8Fast (b : ByteArray) (idx : USize) (v : UInt8) : ByteArray :=
  if h : idx < b.usize then b.uset idx v (usizeLtImpSizeLt h) else b

@[inline] def getU32Fast (b : @& ByteArray) (idx : USize) : UInt32 :=
  let base := idx <<< 2
  if h3 : (base ||| 3) < b.usize then
    let b0 := b.uget (base ||| 0) (usizeShift2OrLtSize 0 (by decide) h3)
    let b1 := b.uget (base ||| 1) (usizeShift2OrLtSize 1 (by decide) h3)
    let b2 := b.uget (base ||| 2) (usizeShift2OrLtSize 2 (by decide) h3)
    let b3 := b.uget (base ||| 3) (usizeLtImpSizeLt h3)
    b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)
  else 0

@[inline] def setU32Fast (b : ByteArray) (idx : USize) (v : UInt32) : ByteArray :=
  let base := idx <<< 2
  if h3 : (base ||| 3) < b.usize then
    have h0 : (base ||| 0).toNat < b.size := usizeShift2OrLtSize 0 (by decide) h3
    have h1 : (base ||| 1).toNat < b.size := usizeShift2OrLtSize 1 (by decide) h3
    have h2 : (base ||| 2).toNat < b.size := usizeShift2OrLtSize 2 (by decide) h3
    have h3' : (base ||| 3).toNat < b.size := usizeLtImpSizeLt h3
    let b0 := b.uset (base ||| 0) v.toUInt8 h0
    have s0 : b0.size = b.size := byteArraySizeUset ..
    let b1 := b0.uset (base ||| 1) (v >>> 8).toUInt8 (s0.symm ▸ h1)
    have s1 : b1.size = b.size := (byteArraySizeUset ..).trans s0
    let b2 := b1.uset (base ||| 2) (v >>> 16).toUInt8 (s1.symm ▸ h2)
    have s2 : b2.size = b.size := (byteArraySizeUset ..).trans s1
    b2.uset (base ||| 3) (v >>> 24).toUInt8 (s2.symm ▸ h3')
  else b

@[inline] def getU64Fast (b : @& ByteArray) (idx : USize) : UInt64 :=
  let base := idx <<< 3
  if h7 : (base ||| 7) < b.usize then
    let b0 := b.uget (base ||| 0) (usizeShift3OrLtSize 0 (by decide) h7)
    let b1 := b.uget (base ||| 1) (usizeShift3OrLtSize 1 (by decide) h7)
    let b2 := b.uget (base ||| 2) (usizeShift3OrLtSize 2 (by decide) h7)
    let b3 := b.uget (base ||| 3) (usizeShift3OrLtSize 3 (by decide) h7)
    let b4 := b.uget (base ||| 4) (usizeShift3OrLtSize 4 (by decide) h7)
    let b5 := b.uget (base ||| 5) (usizeShift3OrLtSize 5 (by decide) h7)
    let b6 := b.uget (base ||| 6) (usizeShift3OrLtSize 6 (by decide) h7)
    let b7 := b.uget (base ||| 7) (usizeLtImpSizeLt h7)
    b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) ||| (b3.toUInt64 <<< 24) |||
      (b4.toUInt64 <<< 32) ||| (b5.toUInt64 <<< 40) ||| (b6.toUInt64 <<< 48) ||| (b7.toUInt64 <<< 56)
  else 0

@[inline] def setU64Fast (b : ByteArray) (idx : USize) (v : UInt64) : ByteArray :=
  let base := idx <<< 3
  if h7 : (base ||| 7) < b.usize then
    have h0 : (base ||| 0).toNat < b.size := usizeShift3OrLtSize 0 (by decide) h7
    have h1 : (base ||| 1).toNat < b.size := usizeShift3OrLtSize 1 (by decide) h7
    have h2 : (base ||| 2).toNat < b.size := usizeShift3OrLtSize 2 (by decide) h7
    have h3 : (base ||| 3).toNat < b.size := usizeShift3OrLtSize 3 (by decide) h7
    have h4 : (base ||| 4).toNat < b.size := usizeShift3OrLtSize 4 (by decide) h7
    have h5 : (base ||| 5).toNat < b.size := usizeShift3OrLtSize 5 (by decide) h7
    have h6 : (base ||| 6).toNat < b.size := usizeShift3OrLtSize 6 (by decide) h7
    have h7' : (base ||| 7).toNat < b.size := usizeLtImpSizeLt h7
    let b0 := b.uset (base ||| 0) v.toUInt8 h0
    have s0 : b0.size = b.size := byteArraySizeUset ..
    let b1 := b0.uset (base ||| 1) (v >>> 8).toUInt8 (s0.symm ▸ h1)
    have s1 : b1.size = b.size := (byteArraySizeUset ..).trans s0
    let b2 := b1.uset (base ||| 2) (v >>> 16).toUInt8 (s1.symm ▸ h2)
    have s2 : b2.size = b.size := (byteArraySizeUset ..).trans s1
    let b3 := b2.uset (base ||| 3) (v >>> 24).toUInt8 (s2.symm ▸ h3)
    have s3 : b3.size = b.size := (byteArraySizeUset ..).trans s2
    let b4 := b3.uset (base ||| 4) (v >>> 32).toUInt8 (s3.symm ▸ h4)
    have s4 : b4.size = b.size := (byteArraySizeUset ..).trans s3
    let b5 := b4.uset (base ||| 5) (v >>> 40).toUInt8 (s4.symm ▸ h5)
    have s5 : b5.size = b.size := (byteArraySizeUset ..).trans s4
    let b6 := b5.uset (base ||| 6) (v >>> 48).toUInt8 (s5.symm ▸ h6)
    have s6 : b6.size = b.size := (byteArraySizeUset ..).trans s5
    b6.uset (base ||| 7) (v >>> 56).toUInt8 (s6.symm ▸ h7')
  else b

/-- Allocate a zeroed `ByteArray` of exact length `n` in O(log n) doublings
inside a single pre-allocated buffer (zero intermediate heap reallocations). -/
def zeroBytesExact (n : Nat) : ByteArray :=
  if n == 0 then ByteArray.empty
  else Id.run do
    let mut b := ByteArray.emptyWithCapacity n
    let init := min n 64
    for _ in [:init] do
      b := b.push 0
    for _ in [:64] do
      let sz := b.size
      if sz < n then
        b := b.copySlice 0 b sz (min sz (n - sz)) false
      else
        break
    return b

/-- Allocate an `8 * n`-byte `ByteArray` filled with `val` in O(log n) `copySlice` doublings. -/
def repeatU64BytesExact (n : Nat) (val : UInt64) : ByteArray :=
  if n == 0 then ByteArray.empty
  else if val == 0 then zeroBytesExact (8 * n)
  else Id.run do
    let totalBytes := 8 * n
    let mut b := zeroBytesExact 64
    let initWords := min n 8
    for i in [:initWords] do
      b := setU64Fast b i.toUSize val
    let mut out := ByteArray.emptyWithCapacity totalBytes
    out := b.copySlice 0 out 0 (8 * initWords) false
    for _ in [:64] do
      let sz := out.size
      if sz < totalBytes then
        let copyLen := min sz (totalBytes - sz)
        out := out.copySlice 0 out sz copyLen false
      else
        break
    return out

@[noinline] def growBytesCap (b : ByteArray) (target : Nat) : ByteArray :=
  let cap := max target (max (2 * b.size) 4096)
  b.copySlice 0 (zeroBytesExact cap) 0 b.size true

/-- Grow `b` to at least `target` bytes by doubling with zero fill. -/
@[inline] def ensureBytesCap (b : ByteArray) (target : Nat) : ByteArray :=
  if target <= b.size then b
  else growBytesCap b target

/-! ## `GF(2^64)` generator `g` powers & O(1) discrete log (`FastGPow`) -/

@[inline] def mulByG (x : UInt64) : UInt64 :=
  (x <<< 1) ^^^ (if (x >>> 63) == 0 then 0 else 0x1b)

@[inline] def divByG (x : UInt64) : UInt64 :=
  if (x &&& 1) == 1 then ((x ^^^ 0x1b) >>> 1) ||| ((1 : UInt64) <<< 63) else x >>> 1

@[inline] def gpowSlotOf (key : UInt64) (mask : USize) : USize :=
  ((key * 0x9E3779B97F4A7C15) >>> 32).toUSize &&& mask

def gpowTableInsertLoop (tbl : ByteArray) (mask slot : USize) (key : UInt64) (k1 : UInt32) :
    Nat → ByteArray
  | 0 => tbl
  | fuel + 1 =>
    if getU32Fast tbl slot == 0 then
      setU32Fast tbl slot k1
    else
      gpowTableInsertLoop tbl mask ((slot + 1) &&& mask) key k1 fuel

/-- Insert `(key = pow[k], k)` into an open-addressed `u32` table (`k + 1` stored, `0` empty). -/
@[inline] def gpowTableInsert (tbl : ByteArray) (mask : USize) (key : UInt64) (k : UInt32) :
    ByteArray :=
  let slot := gpowSlotOf key mask
  if getU32Fast tbl slot == 0 then
    setU32Fast tbl slot (k + 1)
  else
    gpowTableInsertLoop tbl mask ((slot + 1) &&& mask) key (k + 1) mask.toNat

/-- Slow fallback linear probe for `gpowTableFind` (`0 = not found`, `k + 1` = found `k`). -/
@[noinline] def gpowTableFindSlow (tbl : @& ByteArray) (pows : @& ByteArray) (mask slot : USize)
    (key : UInt64) : Nat → UInt64
  | 0 => 0
  | fuel + 1 =>
    let entry := getU32Fast tbl slot
    if entry == 0 then 0
    else
      let k := (entry - 1).toUSize
      if getU64Fast pows k == key then entry.toUInt64
      else gpowTableFindSlow tbl pows mask ((slot + 1) &&& mask) key fuel

/-- Unboxed open-addressed probe (`0 = not found`, `k + 1` = found `k`). -/
@[inline] def gpowTableFindRaw (tbl : @& ByteArray) (pows : @& ByteArray) (mask : USize)
    (key : UInt64) : UInt64 :=
  let slot0 := gpowSlotOf key mask
  let e0 := getU32Fast tbl slot0
  if e0 == 0 then 0
  else if getU64Fast pows (e0 - 1).toUSize == key then e0.toUInt64
  else
    let slot1 := (slot0 + 1) &&& mask
    let e1 := getU32Fast tbl slot1
    if e1 == 0 then 0
    else if getU64Fast pows (e1 - 1).toUSize == key then e1.toUInt64
    else
      let slot2 := (slot1 + 1) &&& mask
      let e2 := getU32Fast tbl slot2
      if e2 == 0 then 0
      else if getU64Fast pows (e2 - 1).toUSize == key then e2.toUInt64
      else gpowTableFindSlow tbl pows mask ((slot2 + 1) &&& mask) key mask.toNat

/-- Find `k` with `pow[k] == key` in an open-addressed `u32` table. -/
@[inline] def gpowTableFind (tbl : @& ByteArray) (pows : @& ByteArray) (mask : USize)
    (key : UInt64) : Option Nat :=
  let r := gpowTableFindRaw tbl pows mask key
  if r == 0 then none else some (r - 1).toNat

/-- Unboxed `ByteArray`-backed `g^k` table with stride-4 coarse hash index for O(1) `log`. -/
structure FastGPow where
  pows : ByteArray
  len : Nat
  coarse : ByteArray
  coarseCap : Nat
  deriving Inhabited

def buildFastGPow (upto : Nat) : FastGPow := Id.run do
  let count := upto + 1
  let nTasks := min 16 (max 1 ((count + 65535) / 65536))
  let powBySq := fun (exp : Nat) => Id.run do
    let mut res : UInt64 := 1
    let mut base : UInt64 := 2
    let mut e := exp
    for _ in [:64] do
      if e == 0 then break
      if (e &&& 1) == 1 then
        res := Model.Field.nativeMul res base
      base := Model.Field.nativeMul base base
      e := e >>> 1
    return res
  let powTasks := (Array.range nTasks).map fun tid =>
    let lo := (tid * count) / nTasks
    let hi := ((tid + 1) * count) / nTasks
    Task.spawn fun _ => Id.run do
      let cnt := hi - lo
      let mut chunk := zeroBytesExact (8 * cnt)
      let mut p := powBySq lo
      for step in [:cnt] do
        chunk := setU64Fast chunk step.toUSize p
        p := mulByG p
      return chunk
  let mut pows := ByteArray.emptyWithCapacity (8 * count)
  let mut pOff := 0
  for tk in powTasks do
    let ch := tk.get
    pows := ch.copySlice 0 pows pOff ch.size false
    pOff := pOff + ch.size
  let nCoarse := (count + 3) / 4
  let coarseLog := max 10 (log2Ceil (2 * nCoarse + 1))
  let coarseCap := 1 <<< coarseLog
  let mask := (coarseCap - 1).toUSize
  let mut coarse := zeroBytesExact (4 * coarseCap)
  let mut k := 0
  for _ in [:nCoarse] do
    if k < count then
      let p := getU64Fast pows k.toUSize
      coarse := gpowTableInsert coarse mask p k.toUInt32
      k := k + 4
  return ⟨pows, count, coarse, coarseCap⟩

@[noinline] def FastGPow.growCold (g : FastGPow) (upto : Nat) : FastGPow :=
  buildFastGPow (max (upto + 1) (2 * g.len))

@[inline] def FastGPow.grow (g : FastGPow) (upto : Nat) : FastGPow :=
  if upto < g.len then g
  else g.growCold upto

@[inline] def FastGPow.powAt (g : @& FastGPow) (k : Nat) : UInt64 :=
  getU64Fast g.pows k.toUSize

@[inline] def FastGPow.logU64Raw (g : @& FastGPow) (x : UInt64) : UInt64 :=
  let mask := (g.coarseCap - 1).toUSize
  let lenU := g.len.toUInt64
  let r0 := gpowTableFindRaw g.coarse g.pows mask x
  if r0 != 0 && r0 - 1 < lenU then r0
  else
    let y1 := divByG x
    let r1 := gpowTableFindRaw g.coarse g.pows mask y1
    if r1 != 0 && r1 < lenU then r1 + 1
    else
      let y2 := divByG y1
      let r2 := gpowTableFindRaw g.coarse g.pows mask y2
      if r2 != 0 && r2 + 1 < lenU then r2 + 2
      else
        let y3 := divByG y2
        let r3 := gpowTableFindRaw g.coarse g.pows mask y3
        if r3 != 0 && r3 + 2 < lenU then r3 + 3
        else 0

@[inline] def FastGPow.logU64 (g : @& FastGPow) (x : UInt64) : Option Nat :=
  let r := g.logU64Raw x
  if r == 0 then none else some (r - 1).toNat

@[inline] def FastGPow.logE (g : @& FastGPow) (v : E) : Except Fault Nat :=
  if v.c1 != 0 || v.c2 != 0 then .error (.notInK v)
  else
    let r := g.logU64Raw v.c0
    if r != 0 then .ok (r - 1).toNat
    else .error (.wildPointer v)

/-! ## Fast extension inverse (`GF(2^192)`) -/

@[inline] def inverseFastE (a : E) : E :=
  if a.c0 == 0 && a.c1 == 0 && a.c2 == 0 then Spec.Field.zero
  else Model.Field.nativeEinv a

/-! ## Pre-decoded guest program & schedule (`FastProg`) -/

inductive FastRHint where
  | frameAddress (offset : Nat)
  | allocFrames (ptr size endOffset : Nat) (startInverse : UInt64) (tail : Nat)
  | alloc (ptr size : Nat)
  | allocDyn (ptr size : Nat)
  | witnessStack (streamId : Nat) (base len : Nat)
  | witnessHeap (streamId : Nat) (ptr lo len : Nat)
  | log2Ceil (bits : BitsDest) (dst nbits floor : Nat)
  | bitDecompose (value : Nat) (bits : BitsDest) (nbits start : Nat)
  | bitDecomposeExp (value : Nat) (bits : BitsDest) (nbits : Nat)
  | digitDecomposeExp (value : Nat) (dst : BitsDest) (nbits ndigits digitBits start : Nat)
      (startCell : Option Nat)
  | windowsExp (value : Nat) (dest : BitsDest) (offset start width count : Nat)
  | fieldLimbs (value base len : Nat)
  | inverse (value dst : Nat)
  | print (label : String) (cell : Nat)
  deriving Inhabited

/-- Pre-decoded program & schedule, reusable across benchmark passes.
Each `pc` occupies `16` `UInt64` slots (`128` bytes) in `opWords` (`idx = pc * 16 + slot`):
* slot 0: opcode tag (`0=xor, 1=mul, 2=set, 3=deref, 4=jump, 5=keccak`)
* `xor` / `mul` / `jump`: slots `1, 2, 3 = a, b, c` (`oc, od, of`)
* `set`: slot `1 = offset`, slots `2, 3, 4 = val.c0, val.c1, val.c2`
* `deref`: slots `1, 2, 3 = o1, o2, o3`, slot `4 = mode` (`0=cell, 1=pc, 2=fp`)
* `keccak`: slots `1..4 = m[0..3]`, `5 = tail`, `6 = b8`, `7 = cap`, `8 = out`,
  `9 = inOdd (0/1)`, `10 = outOdd (0/1)`. -/
structure FastProg where
  size : Nat
  opWords : ByteArray
  hintAt : ByteArray
  hintLists : Array (Array FastRHint)
  streamNames : Array String
  deriving Inhabited

def streamIdInsert (names : Array String) (name : String) : Array String × Nat :=
  match names.findIdx? (· == name) with
  | some id => (names, id)
  | none => (names.push name, names.size)

def compileFastProg (program : @& Array Op) (schedule : @& Array (Array RHint)) : FastProg := Id.run do
  let n := program.size
  let mut opWords := zeroBytesExact (128 * n)
  for pc in [:n] do
    let base := (16 * pc).toUSize
    match program[pc]? with
    | some (.xor a b c) =>
      opWords := setU64Fast opWords base 0
      opWords := setU64Fast opWords (base + 1) a.toUInt64
      opWords := setU64Fast opWords (base + 2) b.toUInt64
      opWords := setU64Fast opWords (base + 3) c.toUInt64
    | some (.mul a b c) =>
      opWords := setU64Fast opWords base 1
      opWords := setU64Fast opWords (base + 1) a.toUInt64
      opWords := setU64Fast opWords (base + 2) b.toUInt64
      opWords := setU64Fast opWords (base + 3) c.toUInt64
    | some (.set o v) =>
      opWords := setU64Fast opWords base 2
      opWords := setU64Fast opWords (base + 1) o.toUInt64
      opWords := setU64Fast opWords (base + 2) v.c0
      opWords := setU64Fast opWords (base + 3) v.c1
      opWords := setU64Fast opWords (base + 4) v.c2
    | some (.deref o1 o2 o3 mode) =>
      let mTag : UInt64 := match mode with | .cell => 0 | .pc => 1 | .fp => 2
      opWords := setU64Fast opWords base 3
      opWords := setU64Fast opWords (base + 1) o1.toUInt64
      opWords := setU64Fast opWords (base + 2) o2.toUInt64
      opWords := setU64Fast opWords (base + 3) o3.toUInt64
      opWords := setU64Fast opWords (base + 4) mTag
    | some (.jump oc od of_) =>
      opWords := setU64Fast opWords base 4
      opWords := setU64Fast opWords (base + 1) oc.toUInt64
      opWords := setU64Fast opWords (base + 2) od.toUInt64
      opWords := setU64Fast opWords (base + 3) of_.toUInt64
    | some (.keccak m tail b8 cap out inOdd outOdd) =>
      opWords := setU64Fast opWords base 5
      opWords := setU64Fast opWords (base + 1) (m[0]?.getD 0).toUInt64
      opWords := setU64Fast opWords (base + 2) (m[1]?.getD 0).toUInt64
      opWords := setU64Fast opWords (base + 3) (m[2]?.getD 0).toUInt64
      opWords := setU64Fast opWords (base + 4) (m[3]?.getD 0).toUInt64
      opWords := setU64Fast opWords (base + 5) tail.toUInt64
      opWords := setU64Fast opWords (base + 6) b8.toUInt64
      opWords := setU64Fast opWords (base + 7) cap.toUInt64
      opWords := setU64Fast opWords (base + 8) out.toUInt64
      opWords := setU64Fast opWords (base + 9) (if inOdd then 1 else 0)
      opWords := setU64Fast opWords (base + 10) (if outOdd then 1 else 0)
    | none => pure ()
  let mut hintAt := zeroBytesExact (4 * n)
  let mut hintLists : Array (Array FastRHint) := #[]
  let mut names : Array String := #[]
  for pc in [:n] do
    let hs := schedule[pc]?.getD #[]
    if !hs.isEmpty then
      let mut fastHs := Array.emptyWithCapacity hs.size
      for h in hs do
        match h with
        | .frameAddress off => fastHs := fastHs.push (.frameAddress off)
        | .allocFrames ptr sz endOff sInv tl =>
          fastHs := fastHs.push (.allocFrames ptr sz endOff sInv tl)
        | .alloc ptr sz => fastHs := fastHs.push (.alloc ptr sz)
        | .allocDyn ptr sz => fastHs := fastHs.push (.allocDyn ptr sz)
        | .witnessStack nm base len =>
          let (ns, sid) := streamIdInsert names nm
          names := ns
          fastHs := fastHs.push (.witnessStack sid base len)
        | .witnessHeap nm ptr lo len =>
          let (ns, sid) := streamIdInsert names nm
          names := ns
          fastHs := fastHs.push (.witnessHeap sid ptr lo len)
        | .log2Ceil bits dst nbits floor =>
          fastHs := fastHs.push (.log2Ceil bits dst nbits floor)
        | .bitDecompose val bits nbits start =>
          fastHs := fastHs.push (.bitDecompose val bits nbits start)
        | .bitDecomposeExp val bits nbits =>
          fastHs := fastHs.push (.bitDecomposeExp val bits nbits)
        | .digitDecomposeExp val dst nbits ndigits dBits start sCell =>
          fastHs := fastHs.push (.digitDecomposeExp val dst nbits ndigits dBits start sCell)
        | .windowsExp val dest off start width cnt =>
          fastHs := fastHs.push (.windowsExp val dest off start width cnt)
        | .fieldLimbs val base len =>
          fastHs := fastHs.push (.fieldLimbs val base len)
        | .inverse val dst =>
          fastHs := fastHs.push (.inverse val dst)
        | .print lbl cell =>
          fastHs := fastHs.push (.print lbl cell)
      hintLists := hintLists.push fastHs
      hintAt := setU32Fast hintAt pc.toUSize hintLists.size.toUInt32
  return ⟨n, opWords, hintAt, hintLists, names⟩

/-- Integer-indexed witness streams matching `FastProg.streamNames`. -/
structure FastStreams where
  entries : Array (Array (Array E))
  next : Array Nat
  deriving Inhabited

def buildFastStreamsFromStreams (names : @& Array String) (streams : @& Array Stream) :
    FastStreams := Id.run do
  let mut entries := Array.replicate names.size #[]
  let mut next := Array.replicate names.size 0
  for sid in [:names.size] do
    let nm := names[sid]?.getD ""
    if let some s := streams.find? (fun st => st.name == nm) then
      entries := entries.setIfInBounds sid s.entries
      next := next.setIfInBounds sid s.next
  return ⟨entries, next⟩

def buildFastStreamsFromHints (names : @& Array String) (hints : @& Array Spec.Xmss.HintEntry) :
    FastStreams := Id.run do
  let mut entries : Array (Array (Array E)) := Array.replicate names.size #[]
  for h in hints do
    if let some sid := names.findIdx? (· == h.name) then
      entries := entries.modify sid (fun es => es.push h.values)
  return ⟨entries, Array.replicate names.size 0⟩

/-! ## Parallel Bytecode Fiat-Shamir IV (`ivOfPar`) -/

def ivOfParWith (gpows : @& FastGPow) (fprog : @& FastProg) : ByteArray := Id.run do
  let n := fprog.size
  let logBytecode := log2FloorPow2 n
  let stride := 1 <<< logBytecode
  let totalWords := 1 <<< (busBits + logBytecode)
  let totalBytes := 9 + 8 * totalWords
  let prefixLen := 9 + 8 * (bytecodePublicSlot * stride)
  let opWords := fprog.opWords
  let gOp0 := gpows.powAt opXor
  let gOp1 := gpows.powAt opMul
  let gOp2 := gpows.powAt opSet
  let gOp3 := gpows.powAt opDeref
  let gOp4 := gpows.powAt opJump
  let gOp5 := gpows.powAt opKeccak
  let colTasks := (Array.range nBytecodeCols).map fun s =>
    Task.spawn fun _ => Id.run do
      let mut colBytes := zeroBytesExact (8 * stride)
      let limit := min stride n
      for pc in [:limit] do
        let base := (16 * pc).toUSize
        let tag := getU64Fast opWords base
        let val : UInt64 :=
          if tag == 0 then
            match s with
            | 0 => gOp0
            | 1 => gpows.powAt (getU64Fast opWords (base + 1)).toNat
            | 2 => gpows.powAt (getU64Fast opWords (base + 2)).toNat
            | 3 => gpows.powAt (getU64Fast opWords (base + 3)).toNat
            | _ => 0
          else if tag == 1 then
            match s with
            | 0 => gOp1
            | 1 => gpows.powAt (getU64Fast opWords (base + 1)).toNat
            | 2 => gpows.powAt (getU64Fast opWords (base + 2)).toNat
            | 3 => gpows.powAt (getU64Fast opWords (base + 3)).toNat
            | _ => 0
          else if tag == 2 then
            match s with
            | 0 => gOp2
            | 1 => gpows.powAt (getU64Fast opWords (base + 1)).toNat
            | 2 => getU64Fast opWords (base + 2)
            | 3 => getU64Fast opWords (base + 3)
            | 4 => getU64Fast opWords (base + 4)
            | _ => 0
          else if tag == 3 then
            let mTag := getU64Fast opWords (base + 4)
            match s with
            | 0 => gOp3
            | 1 => gpows.powAt (getU64Fast opWords (base + 1)).toNat
            | 2 => gpows.powAt (getU64Fast opWords (base + 2)).toNat
            | 3 => gpows.powAt (getU64Fast opWords (base + 3)).toNat
            | 4 => if mTag == 1 then 1 else 0
            | 5 => if mTag == 2 then 1 else 0
            | _ => 0
          else if tag == 4 then
            match s with
            | 0 => gOp4
            | 1 => gpows.powAt (getU64Fast opWords (base + 1)).toNat
            | 2 => gpows.powAt (getU64Fast opWords (base + 2)).toNat
            | 3 => gpows.powAt (getU64Fast opWords (base + 3)).toNat
            | _ => 0
          else
            match s with
            | 0 => gOp5
            | 1 => gpows.powAt (getU64Fast opWords (base + 1)).toNat
            | 2 => gpows.powAt (getU64Fast opWords (base + 2)).toNat
            | 3 => gpows.powAt (getU64Fast opWords (base + 3)).toNat
            | 4 => gpows.powAt (getU64Fast opWords (base + 4)).toNat
            | 5 => gpows.powAt (getU64Fast opWords (base + 5)).toNat
            | 6 => gpows.powAt (getU64Fast opWords (base + 6)).toNat
            | 7 => gpows.powAt (getU64Fast opWords (base + 7)).toNat
            | 8 => gpows.powAt (getU64Fast opWords (base + 8)).toNat
            | 9 => getU64Fast opWords (base + 9)
            | 10 => getU64Fast opWords (base + 10)
            | _ => 0
        if val != 0 then
          colBytes := setU64Fast colBytes pc.toUSize val
      return colBytes
  let cols := colTasks.map Task.get
  let mut st := zeroState25Fast
  let mut carry := ByteArray.emptyWithCapacity 272
  carry := versionTag.copySlice 0 carry 0 versionTag.size false
  let zeroChunk := zeroBytesExact (min 136000 (max 136 prefixLen))
  let mut remZero := prefixLen - versionTag.size
  for _ in [:(remZero / 136000 + 2)] do
    if remZero == 0 then break
    let take := min remZero zeroChunk.size
    carry := zeroChunk.copySlice 0 carry carry.size take false
    let full := carry.size / 136
    for bi in [:full] do
      st := Model.Keccak.absorb25Fast st carry (136 * bi)
    let rem := carry.size - 136 * full
    carry := if rem == 0 then ByteArray.emptyWithCapacity 272 else carry.extract (136 * full) carry.size
    remZero := remZero - take
  for col in cols do
    let mut off := 0
    if carry.size > 0 then
      let need := min (136 - carry.size) col.size
      carry := col.copySlice 0 carry carry.size need false
      off := need
      if carry.size == 136 then
        st := Model.Keccak.absorb25Fast st carry 0
        carry := ByteArray.emptyWithCapacity 272
    let remCol := col.size - off
    let full := remCol / 136
    for bi in [:full] do
      st := Model.Keccak.absorb25Fast st col (off + 136 * bi)
    let leftOff := off + 136 * full
    if leftOff < col.size then
      carry := col.copySlice leftOff carry carry.size (col.size - leftOff) false
  let suffixLen := totalBytes - (prefixLen + nBytecodeCols * 8 * stride)
  let mut remSuf := suffixLen
  for _ in [:(remSuf / 136000 + 2)] do
    if remSuf == 0 then break
    let take := min remSuf zeroChunk.size
    carry := zeroChunk.copySlice 0 carry carry.size take false
    let full := carry.size / 136
    for bi in [:full] do
      st := Model.Keccak.absorb25Fast st carry (136 * bi)
    let rem := carry.size - 136 * full
    carry := if rem == 0 then ByteArray.emptyWithCapacity 272 else carry.extract (136 * full) carry.size
    remSuf := remSuf - take
  let blk := Spec.Keccak.finalBlock carry 1
  let stFinal := Model.Keccak.absorb25Fast st blk 0
  let out := ByteArray.emptyWithCapacity 32
  let out := Model.Keccak.pushU64BytesLE out stFinal.a00
  let out := Model.Keccak.pushU64BytesLE out stFinal.a01
  let out := Model.Keccak.pushU64BytesLE out stFinal.a02
  return Model.Keccak.pushU64BytesLE out stFinal.a03

def ivOfPar (program : @& Array Op) : ByteArray :=
  let maxOff := Model.Layout.maxProgramOffset program
  let gpows := buildFastGPow (max maxOff 16)
  let fprog := compileFastProg program #[]
  ivOfParWith gpows fprog

/-! ## Planar VM Execution State & Compact Per-Table Traces -/

/-- Planar VM execution output:
* `mc0`, `mc1`, `mc2`: `8 * memCap` bytes each;
* `mState`: `memCap` bytes (`0 = Unwritten, 1 = Written, 2 = Linked`);
* `mAccess`: `4 * memCap` bytes (`u32` access count per cell);
* `bcCounts`: `4 * progSize` bytes (`u32` execution count per `pc`);
* Compact `u32` trace buffers (`tXor/tMul/tDeref/tJump` = `6` `u32`s/row,
  `tSet` = `4` `u32`s/row, `tKeccak` = `29` `u32`s/row). -/
structure FastExec where
  mc0 : ByteArray
  mc1 : ByteArray
  mc2 : ByteArray
  mState : ByteArray
  mAccess : ByteArray
  memCap : Nat
  memUsed : Nat
  maxAccess : Nat
  maxBcCount : Nat
  cycles : Nat
  unconstrained : Nat
  bcCounts : ByteArray
  tXor : ByteArray
  nXor : Nat
  tMul : ByteArray
  nMul : Nat
  tSet : ByteArray
  nSet : Nat
  tDeref : ByteArray
  nDeref : Nat
  tJump : ByteArray
  nJump : Nat
  tKeccak : ByteArray
  nKeccak : Nat
  g : FastGPow
  deriving Inhabited

/-- Mutable planar state during `executeFastWith`.
All 14 scalar fields are `UInt64` so Lean unboxes them inside the constructor,
and every mutating helper destructures `FastVm` ONCE on entry and constructs a
single `FastVm` on return so `mc0`, `mc1`, `mc2`, `mState`, `mAccess`, `bcCounts`,
and `tXor..tKeccak` ALWAYS have `RC == 1` at `ByteArray.uset`. -/
structure FastVm where
  mc0 : ByteArray
  mc1 : ByteArray
  mc2 : ByteArray
  mState : ByteArray
  mAccess : ByteArray
  bcCounts : ByteArray
  tXor : ByteArray
  tMul : ByteArray
  tSet : ByteArray
  tDeref : ByteArray
  tJump : ByteArray
  tKeccak : ByteArray
  links : Array (Nat × Nat)
  unconstrained : Array Nat
  g : FastGPow
  streams : FastStreams
  memCap : UInt64
  memUsed : UInt64
  maxAccess : UInt64
  maxBcCount : UInt64
  pc : UInt64
  fp : UInt64
  nextFree : UInt64
  cycles : UInt64
  nXor : UInt64
  nMul : UInt64
  nSet : UInt64
  nDeref : UInt64
  nJump : UInt64
  nKeccak : UInt64
  deriving Inhabited

@[noinline] def vmGrowMemCold (vm : FastVm) (target : Nat) : FastVm :=
  let ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
       links, unconstrained, g, streams,
       memCap, memUsed, maxAccess, maxBcCount, pc, fp, nextFree, cycles,
       nXor, nMul, nSet, nDeref, nJump, nKeccak⟩ := vm
  let cap := max target (max (2 * memCap.toNat) 65536)
  let mc0 := mc0.copySlice 0 (zeroBytesExact (8 * cap)) 0 mc0.size true
  let mc1 := mc1.copySlice 0 (zeroBytesExact (8 * cap)) 0 mc1.size true
  let mc2 := mc2.copySlice 0 (zeroBytesExact (8 * cap)) 0 mc2.size true
  let mState := mState.copySlice 0 (zeroBytesExact cap) 0 mState.size true
  let mAccess := mAccess.copySlice 0 (zeroBytesExact (4 * cap)) 0 mAccess.size true
  let used1 := max memUsed.toNat target
  ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
   links, unconstrained, g, streams,
   cap.toUInt64, used1.toUInt64, maxAccess, maxBcCount, pc, fp, nextFree, cycles,
   nXor, nMul, nSet, nDeref, nJump, nKeccak⟩

@[noinline] def vmEnsureAddrCold (vm : FastVm) (addr : Nat) : Except Fault FastVm :=
  if addr >= maxCells then .error .outOfMemory
  else .ok (vmGrowMemCold vm (addr + 1))

@[inline] def vmEnsureAddr (vm : FastVm) (addr : Nat) : Except Fault FastVm :=
  let a1 := (addr + 1).toUInt64
  if a1 <= vm.memCap then
    if a1 <= vm.memUsed then .ok vm
    else
      let ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
           links, unconstrained, g, streams,
           memCap, _, maxAccess, maxBcCount, pc, fp, nextFree, cycles,
           nXor, nMul, nSet, nDeref, nJump, nKeccak⟩ := vm
      .ok ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
           links, unconstrained, g, streams,
           memCap, a1, maxAccess, maxBcCount, pc, fp, nextFree, cycles,
           nXor, nMul, nSet, nDeref, nJump, nKeccak⟩
  else vmEnsureAddrCold vm addr

@[inline] def vmGetState (vm : @& FastVm) (addr : Nat) : UInt8 :=
  if addr.toUInt64 < vm.memCap then getU8Fast vm.mState addr.toUSize else 0

@[inline] def vmIsWritten (vm : @& FastVm) (addr : Nat) : Bool :=
  vmGetState vm addr == 1

@[inline] def vmGetWord (vm : @& FastVm) (addr : Nat) : E :=
  if addr.toUInt64 < vm.memCap then
    let idx := addr.toUSize
    ⟨getU64Fast vm.mc0 idx, getU64Fast vm.mc1 idx, getU64Fast vm.mc2 idx⟩
  else Spec.Field.zero

@[noinline] def vmConflictCold (addr : Nat) (old val : E) : Except Fault (FastVm × Bool) :=
  .error (.conflict addr old val)

def vmStoreOne (vm : FastVm) (addr : Nat) (val : E) : Except Fault (FastVm × Bool) := do
  let vm ←
    if (addr + 1).toUInt64 <= vm.memCap then pure vm
    else vmEnsureAddrCold vm addr
  let ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
       links, unconstrained, g, streams,
       memCap, memUsed, maxAccess, maxBcCount, pc, fp, nextFree, cycles,
       nXor, nMul, nSet, nDeref, nJump, nKeccak⟩ := vm
  let a1 := (addr + 1).toUInt64
  let memUsed := if a1 > memUsed then a1 else memUsed
  let idx := addr.toUSize
  let st := getU8Fast mState idx
  if st == 1 then
    let old : E := ⟨getU64Fast mc0 idx, getU64Fast mc1 idx, getU64Fast mc2 idx⟩
    if old.c0 != val.c0 || old.c1 != val.c1 || old.c2 != val.c2 then
      vmConflictCold addr old val
    else
      return (⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
               links, unconstrained, g, streams,
               memCap, memUsed, maxAccess, maxBcCount, pc, fp, nextFree, cycles,
               nXor, nMul, nSet, nDeref, nJump, nKeccak⟩, false)
  else
    let mc0 := setU64Fast mc0 idx val.c0
    let mc1 := setU64Fast mc1 idx val.c1
    let mc2 := setU64Fast mc2 idx val.c2
    let mState := setU8Fast mState idx 1
    return (⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
             links, unconstrained, g, streams,
             memCap, memUsed, maxAccess, maxBcCount, pc, fp, nextFree, cycles,
             nXor, nMul, nSet, nDeref, nJump, nKeccak⟩, st == 2)

@[noinline] def vmSpreadCold (vm : FastVm) (addr : Nat) (val : E) : Except Fault FastVm := do
  let fuel := vm.links.size + 1
  let mut cur := vm
  let mut pending : List Nat := [addr]
  for _ in [:fuel] do
    match pending with
    | [] => return cur
    | a :: rest =>
      pending := rest
      let neighbors := cur.links.toList.filterMap fun (x, y) => if x == a then some y else none
      cur := { cur with links := cur.links.filter fun (x, _) => x != a }
      for b in neighbors do
        let (next, wasLinked) ← vmStoreOne cur b val
        cur := next
        if wasLinked then
          pending := b :: pending
  if pending.isEmpty then return cur else throw .badProgram

def vmPut (vm : FastVm) (addr : Nat) (val : E) : Except Fault FastVm := do
  let (vm, wasLinked) ← vmStoreOne vm addr val
  if !wasLinked then return vm
  else vmSpreadCold vm addr val

@[noinline] def vmLinkCold (vm : FastVm) (a b : Nat) : Except Fault FastVm := do
  let vm ← vmEnsureAddr vm a
  let vm ← vmEnsureAddr vm b
  let ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
       links, unconstrained, g, streams,
       memCap, memUsed, maxAccess, maxBcCount, pc, fp, nextFree, cycles,
       nXor, nMul, nSet, nDeref, nJump, nKeccak⟩ := vm
  let sa := getU8Fast mState a.toUSize
  let mState := if sa == 0 then setU8Fast mState a.toUSize 2 else mState
  let sb := getU8Fast mState b.toUSize
  let mState := if sb == 0 then setU8Fast mState b.toUSize 2 else mState
  let links := (links.push (a, b)).push (b, a)
  return ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
          links, unconstrained, g, streams,
          memCap, memUsed, maxAccess, maxBcCount, pc, fp, nextFree, cycles,
          nXor, nMul, nSet, nDeref, nJump, nKeccak⟩

def vmRead (vm : FastVm) (addr : Nat) : Except Fault (E × FastVm) := do
  let vm ←
    if (addr + 1).toUInt64 <= vm.memCap then pure vm
    else vmEnsureAddrCold vm addr
  let ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
       links, unconstrained, g, streams,
       memCap, memUsed, maxAccess, maxBcCount, pc, fp, nextFree, cycles,
       nXor, nMul, nSet, nDeref, nJump, nKeccak⟩ := vm
  let a1 := (addr + 1).toUInt64
  let memUsed := if a1 > memUsed then a1 else memUsed
  let idx := addr.toUSize
  let st := getU8Fast mState idx
  if st == 1 then
    let w : E := ⟨getU64Fast mc0 idx, getU64Fast mc1 idx, getU64Fast mc2 idx⟩
    return (w, ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
                links, unconstrained, g, streams,
                memCap, memUsed, maxAccess, maxBcCount, pc, fp, nextFree, cycles,
                nXor, nMul, nSet, nDeref, nJump, nKeccak⟩)
  else
    let mState := setU8Fast mState idx 1
    let unconstrained := unconstrained.push addr
    return (Spec.Field.zero,
            ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
             links, unconstrained, g, streams,
             memCap, memUsed, maxAccess, maxBcCount, pc, fp, nextFree, cycles,
             nXor, nMul, nSet, nDeref, nJump, nKeccak⟩)

def vmBump (vm : FastVm) (addr : Nat) : Except Fault (UInt32 × FastVm) := do
  let vm ←
    if (addr + 1).toUInt64 <= vm.memCap then pure vm
    else vmEnsureAddrCold vm addr
  let ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
       links, unconstrained, g, streams,
       memCap, memUsed, maxAccess, maxBcCount, pc, fp, nextFree, cycles,
       nXor, nMul, nSet, nDeref, nJump, nKeccak⟩ := vm
  let a1 := (addr + 1).toUInt64
  let memUsed := if a1 > memUsed then a1 else memUsed
  let idx := addr.toUSize
  let cnt := getU32Fast mAccess idx
  let cnt1 := cnt + 1
  let cnt1U := cnt1.toUInt64
  let maxAccess := if cnt1U > maxAccess then cnt1U else maxAccess
  let mAccess := setU32Fast mAccess idx cnt1
  return (cnt, ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
                links, unconstrained, g, streams,
                memCap, memUsed, maxAccess, maxBcCount, pc, fp, nextFree, cycles,
                nXor, nMul, nSet, nDeref, nJump, nKeccak⟩)

@[inline] def pushRow6 (buf : ByteArray) (n : UInt64)
    (w0 w1 w2 w3 w4 w5 : UInt32) : ByteArray × UInt64 :=
  let need := ((n + 1) * 24).toUSize
  let buf := if need <= buf.size.toUSize then buf else growBytesCap buf need.toNat
  let base := (n * 6).toUSize
  let buf := setU32Fast buf base w0
  let buf := setU32Fast buf (base + 1) w1
  let buf := setU32Fast buf (base + 2) w2
  let buf := setU32Fast buf (base + 3) w3
  let buf := setU32Fast buf (base + 4) w4
  let buf := setU32Fast buf (base + 5) w5
  (buf, n + 1)

@[inline] def pushRow4 (buf : ByteArray) (n : UInt64)
    (w0 w1 w2 w3 : UInt32) : ByteArray × UInt64 :=
  let need := ((n + 1) * 16).toUSize
  let buf := if need <= buf.size.toUSize then buf else growBytesCap buf need.toNat
  let base := (n * 4).toUSize
  let buf := setU32Fast buf base w0
  let buf := setU32Fast buf (base + 1) w1
  let buf := setU32Fast buf (base + 2) w2
  let buf := setU32Fast buf (base + 3) w3
  (buf, n + 1)

/-! ## Fast Hint Execution & Register-Direct Keccak Opcode -/

@[inline] def vmHeapBase (vm : @& FastVm) (ptr : Nat) : Except Fault Nat :=
  vm.g.logE (vmGetWord vm (vm.fp.toNat + ptr))

@[inline] def vmBitsBase (vm : @& FastVm) : BitsDest → Except Fault Nat
  | .stack base => .ok (vm.fp.toNat + base)
  | .heap ptr => vmHeapBase vm ptr

@[inline] def vmCountOf (vm : @& FastVm) (val : E) (nbits : Nat) : Except Fault Nat := do
  let idx ← vm.g.logE val
  if idx < (1 <<< nbits) then return idx else throw (.wildPointer val)

@[inline] def vmSetG (vm : FastVm) (upto : Nat) : FastVm :=
  if upto < vm.g.len then vm
  else
    let ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
         links, unconstrained, g, streams,
         memCap, memUsed, maxAccess, maxBcCount, pc, fp, nextFree, cycles,
         nXor, nMul, nSet, nDeref, nJump, nKeccak⟩ := vm
    ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
     links, unconstrained, g.growCold upto, streams,
     memCap, memUsed, maxAccess, maxBcCount, pc, fp, nextFree, cycles,
     nXor, nMul, nSet, nDeref, nJump, nKeccak⟩

def vmReserve (vm : FastVm) (ptr size : Nat) : Except Fault FastVm := do
  let cell := vm.fp.toNat + ptr
  if vmIsWritten vm cell then return vm
  let nf := vm.nextFree.toNat
  let endOffset := nf + size
  if endOffset >= maxCells then throw .outOfMemory
  let vm := vmSetG vm endOffset
  let vm ← vmEnsureAddr vm endOffset
  let pVal : E := ⟨vm.g.powAt nf, 0, 0⟩
  let vm ← vmPut vm cell pVal
  let ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
       links, unconstrained, g, streams,
       memCap, memUsed, maxAccess, maxBcCount, pc, fp, _, cycles,
       nXor, nMul, nSet, nDeref, nJump, nKeccak⟩ := vm
  return ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
          links, unconstrained, g, streams,
          memCap, memUsed, maxAccess, maxBcCount, pc, fp, endOffset.toUInt64, cycles,
          nXor, nMul, nSet, nDeref, nJump, nKeccak⟩

def vmPopWitness (vm : FastVm) (streamNames : @& Array String)
    (sid base len : Nat) : Except Fault FastVm := do
  let some entries := vm.streams.entries[sid]? | throw (.witness (streamNames[sid]?.getD ""))
  let idx := vm.streams.next[sid]?.getD 0
  let some vals := entries[idx]? | throw (.witness (streamNames[sid]?.getD ""))
  if vals.size != len then throw (.witness (streamNames[sid]?.getD ""))
  let vm ← if len > 0 then vmEnsureAddr vm (base + len - 1) else pure vm
  let ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
       links, unconstrained, g, streams,
       memCap, memUsed, maxAccess, maxBcCount, pc, fp, nextFree, cycles,
       nXor, nMul, nSet, nDeref, nJump, nKeccak⟩ := vm
  let streams : FastStreams := ⟨streams.entries, streams.next.setIfInBounds sid (idx + 1)⟩
  if len == 0 then
    return ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
            links, unconstrained, g, streams,
            memCap, memUsed, maxAccess, maxBcCount, pc, fp, nextFree, cycles,
            nXor, nMul, nSet, nDeref, nJump, nKeccak⟩
  let mut allFresh := true
  for k in [:len] do
    if getU8Fast mState (base + k).toUSize != 0 then
      allFresh := false
      break
  if allFresh then
    let mut mc0' := mc0
    let mut mc1' := mc1
    let mut mc2' := mc2
    let mut mState' := mState
    for k in [:len] do
      let v := vals[k]?.getD Spec.Field.zero
      let aIdx := (base + k).toUSize
      mc0' := setU64Fast mc0' aIdx v.c0
      mc1' := setU64Fast mc1' aIdx v.c1
      mc2' := setU64Fast mc2' aIdx v.c2
      mState' := setU8Fast mState' aIdx 1
    let end1 := (base + len).toUInt64
    let memUsed' := if end1 > memUsed then end1 else memUsed
    return ⟨mc0', mc1', mc2', mState', mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
            links, unconstrained, g, streams,
            memCap, memUsed', maxAccess, maxBcCount, pc, fp, nextFree, cycles,
            nXor, nMul, nSet, nDeref, nJump, nKeccak⟩
  else
    let mut cur : FastVm :=
      ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
       links, unconstrained, g, streams,
       memCap, memUsed, maxAccess, maxBcCount, pc, fp, nextFree, cycles,
       nXor, nMul, nSet, nDeref, nJump, nKeccak⟩
    for k in [:len] do
      let v := vals[k]?.getD Spec.Field.zero
      cur ← vmPut cur (base + k) v
    return cur

@[inline] def extractWindow192 (v : E) (bitPos width : Nat) : Nat :=
  if width == 0 then 0
  else
    let mask : UInt64 := if width >= 64 then 0xffffffffffffffff else ((1 : UInt64) <<< width.toUInt64) - 1
    let limb := bitPos / 64
    let sh := bitPos % 64
    let raw : UInt64 :=
      if limb == 0 then
        if sh == 0 then v.c0
        else (v.c0 >>> sh.toUInt64) ||| (v.c1 <<< (64 - sh).toUInt64)
      else if limb == 1 then
        if sh == 0 then v.c1
        else (v.c1 >>> sh.toUInt64) ||| (v.c2 <<< (64 - sh).toUInt64)
      else if limb == 2 then
        if sh == 0 then v.c2
        else v.c2 >>> sh.toUInt64
      else 0
    (raw &&& mask).toNat

@[inline] def testBit192 (v : E) (bitPos : Nat) : Bool :=
  let limb := bitPos / 64
  let sh := (bitPos % 64).toUInt64
  if limb == 0 then ((v.c0 >>> sh) &&& 1) == 1
  else if limb == 1 then ((v.c1 >>> sh) &&& 1) == 1
  else if limb == 2 then ((v.c2 >>> sh) &&& 1) == 1
  else false

def applyFastHint (streamNames : @& Array String) (h : FastRHint) (vm : FastVm) :
    Except Fault FastVm := do
  let fp := vm.fp.toNat
  match h with
  | .frameAddress offset =>
    return vmSetG vm (fp + offset)
  | .alloc ptr size =>
    vmReserve vm ptr size
  | .allocDyn ptr size =>
    let cnt ← vmCountOf vm (vmGetWord vm (fp + size)) 28
    vmReserve vm ptr cnt
  | .allocFrames ptr size endOffset startInverse tail =>
    let w := vmGetWord vm (fp + endOffset)
    if w.c1 != 0 || w.c2 != 0 then throw (.notInK w)
    let prod : E := ⟨Model.Field.nativeMul w.c0 startInverse, 0, 0⟩
    let cnt ← vmCountOf vm prod 28
    vmReserve vm ptr (size * cnt + tail)
  | .witnessStack sid base len =>
    vmPopWitness vm streamNames sid (fp + base) len
  | .witnessHeap sid ptr lo len =>
    let b ← vmHeapBase vm ptr
    vmPopWitness vm streamNames sid (b + lo) len
  | .log2Ceil bits dst nbits floor =>
    let base ← vmBitsBase vm bits
    let mut val : Nat := 0
    for i in [:nbits] do
      let w := vmGetWord vm (base + i)
      if w.c0 != 0 || w.c1 != 0 || w.c2 != 0 then
        val := val ||| (1 <<< i)
    let lg := if val <= 1 then 0 else (val - 1).log2 + 1
    let mu := max lg floor
    let vm := vmSetG vm mu
    let mVal : E := ⟨vm.g.powAt mu, 0, 0⟩
    vmPut vm (fp + dst) mVal
  | .bitDecompose value bits nbits start =>
    if start + nbits > 192 then throw .badProgram
    let base ← vmBitsBase vm bits
    let w := vmGetWord vm (fp + value)
    if nbits == 0 then return vm
    let vm ← vmEnsureAddr vm (base + nbits - 1)
    let mut allFresh := true
    for i in [:nbits] do
      if getU8Fast vm.mState (base + i).toUSize != 0 then
        allFresh := false
        break
    if allFresh then
      let ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
           links, unconstrained, g, streams,
           memCap, memUsed, maxAccess, maxBcCount, pc, fpU, nextFree, cycles,
           nXor, nMul, nSet, nDeref, nJump, nKeccak⟩ := vm
      let mut mc0' := mc0
      let mut mState' := mState
      for i in [:nbits] do
        let aIdx := (base + i).toUSize
        let b : UInt64 := if testBit192 w (start + i) then 1 else 0
        if b != 0 then mc0' := setU64Fast mc0' aIdx b
        mState' := setU8Fast mState' aIdx 1
      let end1 := (base + nbits).toUInt64
      let memUsed' := if end1 > memUsed then end1 else memUsed
      return ⟨mc0', mc1, mc2, mState', mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
              links, unconstrained, g, streams,
              memCap, memUsed', maxAccess, maxBcCount, pc, fpU, nextFree, cycles,
              nXor, nMul, nSet, nDeref, nJump, nKeccak⟩
    else
      let mut cur := vm
      for i in [:nbits] do
        let b : UInt64 := if testBit192 w (start + i) then 1 else 0
        cur ← vmPut cur (base + i) ⟨b, 0, 0⟩
      return cur
  | .bitDecomposeExp value bits nbits =>
    let integer ← vmCountOf vm (vmGetWord vm (fp + value)) nbits
    let base ← vmBitsBase vm bits
    if nbits == 0 then return vm
    let vm ← vmEnsureAddr vm (base + nbits - 1)
    let mut allFresh := true
    for i in [:nbits] do
      if getU8Fast vm.mState (base + i).toUSize != 0 then
        allFresh := false
        break
    if allFresh then
      let ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
           links, unconstrained, g, streams,
           memCap, memUsed, maxAccess, maxBcCount, pc, fpU, nextFree, cycles,
           nXor, nMul, nSet, nDeref, nJump, nKeccak⟩ := vm
      let mut mc0' := mc0
      let mut mState' := mState
      for i in [:nbits] do
        let aIdx := (base + i).toUSize
        let b : UInt64 := if integer.testBit i then 1 else 0
        if b != 0 then mc0' := setU64Fast mc0' aIdx b
        mState' := setU8Fast mState' aIdx 1
      let end1 := (base + nbits).toUInt64
      let memUsed' := if end1 > memUsed then end1 else memUsed
      return ⟨mc0', mc1, mc2, mState', mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
              links, unconstrained, g, streams,
              memCap, memUsed', maxAccess, maxBcCount, pc, fpU, nextFree, cycles,
              nXor, nMul, nSet, nDeref, nJump, nKeccak⟩
    else
      let mut cur := vm
      for i in [:nbits] do
        let b : UInt64 := if integer.testBit i then 1 else 0
        cur ← vmPut cur (base + i) ⟨b, 0, 0⟩
      return cur
  | .digitDecomposeExp value dst nbits ndigits digitBits start startCell =>
    let integer ← vmCountOf vm (vmGetWord vm (fp + value)) nbits
    let startActual ← match startCell with
      | none => pure start
      | some off => vmCountOf vm (vmGetWord vm (fp + off)) 7
    let base ← vmBitsBase vm dst
    let mask := (1 <<< digitBits) - 1
    let vm := vmSetG vm mask
    if ndigits == 0 then return vm
    let vm ← vmEnsureAddr vm (base + ndigits - 1)
    let mut allFresh := true
    for i in [:ndigits] do
      if getU8Fast vm.mState (base + i).toUSize != 0 then
        allFresh := false
        break
    if allFresh then
      let ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
           links, unconstrained, g, streams,
           memCap, memUsed, maxAccess, maxBcCount, pc, fpU, nextFree, cycles,
           nXor, nMul, nSet, nDeref, nJump, nKeccak⟩ := vm
      let mut mc0' := mc0
      let mut mState' := mState
      for i in [:ndigits] do
        let aIdx := (base + i).toUSize
        let d := (integer >>> (startActual + digitBits * i)) &&& mask
        mc0' := setU64Fast mc0' aIdx (g.powAt d)
        mState' := setU8Fast mState' aIdx 1
      let end1 := (base + ndigits).toUInt64
      let memUsed' := if end1 > memUsed then end1 else memUsed
      return ⟨mc0', mc1, mc2, mState', mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
              links, unconstrained, g, streams,
              memCap, memUsed', maxAccess, maxBcCount, pc, fpU, nextFree, cycles,
              nXor, nMul, nSet, nDeref, nJump, nKeccak⟩
    else
      let mut cur := vm
      for i in [:ndigits] do
        let d := (integer >>> (startActual + digitBits * i)) &&& mask
        let dVal : E := ⟨cur.g.powAt d, 0, 0⟩
        cur ← vmPut cur (base + i) dVal
      return cur
  | .windowsExp value dest offset start width count =>
    if start + width * count > 192 then throw .badProgram
    let base ← vmBitsBase vm dest
    let w := vmGetWord vm (fp + value)
    let maxWin := if width == 0 then 0 else (1 <<< width) - 1
    let vm := vmSetG vm maxWin
    let dstBase := base + offset
    if count == 0 then return vm
    let vm ← vmEnsureAddr vm (dstBase + count - 1)
    let mut allFresh := true
    for i in [:count] do
      if getU8Fast vm.mState (dstBase + i).toUSize != 0 then
        allFresh := false
        break
    if allFresh then
      let ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
           links, unconstrained, g, streams,
           memCap, memUsed, maxAccess, maxBcCount, pc, fpU, nextFree, cycles,
           nXor, nMul, nSet, nDeref, nJump, nKeccak⟩ := vm
      let mut mc0' := mc0
      let mut mState' := mState
      for i in [:count] do
        let aIdx := (dstBase + i).toUSize
        let win := extractWindow192 w (start + width * i) width
        mc0' := setU64Fast mc0' aIdx (g.powAt win)
        mState' := setU8Fast mState' aIdx 1
      let end1 := (dstBase + count).toUInt64
      let memUsed' := if end1 > memUsed then end1 else memUsed
      return ⟨mc0', mc1, mc2, mState', mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
              links, unconstrained, g, streams,
              memCap, memUsed', maxAccess, maxBcCount, pc, fpU, nextFree, cycles,
              nXor, nMul, nSet, nDeref, nJump, nKeccak⟩
    else
      let mut cur := vm
      for i in [:count] do
        let win := extractWindow192 w (start + width * i) width
        let wVal : E := ⟨cur.g.powAt win, 0, 0⟩
        cur ← vmPut cur (dstBase + i) wVal
      return cur
  | .fieldLimbs value base len =>
    if len < 1 || len > 3 then throw .badProgram
    let v := vmGetWord vm (fp + value)
    let dst := fp + base
    let mut cur ← vmPut vm dst ⟨v.c0, 0, 0⟩
    if len >= 2 then cur ← vmPut cur (dst + 1) ⟨v.c1, 0, 0⟩
    if len >= 3 then cur ← vmPut cur (dst + 2) ⟨v.c2, 0, 0⟩
    return cur
  | .inverse value dst =>
    let v := vmGetWord vm (fp + value)
    vmPut vm (fp + dst) (inverseFastE v)
  | .print _ _ =>
    return vm

@[inline] def state25FromCellsFast (inOdd : Bool)
    (w00 w01 w02 w03 w04 w05 w06 w07 w08 w09 w10 w11 w12 : E) : State25 :=
  if inOdd then
    ⟨w00.c1, w01.c0, w01.c1, w02.c0, w02.c1,
     w03.c0, w03.c1, w04.c0, w04.c1, w05.c0,
     w05.c1, w06.c0, w06.c1, w07.c0, w07.c1,
     w08.c0, w08.c1, w09.c0, w09.c1, w10.c0,
     w10.c1, w11.c0, w11.c1, w12.c0, w12.c1⟩
  else
    ⟨w00.c0, w00.c1, w01.c0, w01.c1, w02.c0,
     w02.c1, w03.c0, w03.c1, w04.c0, w04.c1,
     w05.c0, w05.c1, w06.c0, w06.c1, w07.c0,
     w07.c1, w08.c0, w09.c0, w09.c1, w10.c0,
     w10.c1, w11.c0, w11.c1, w12.c0, w12.c1⟩

def putCellsFromState25Fast (vm : FastVm) (outBase : Nat) (outOdd : Bool)
    (s : State25) : Except Fault FastVm := do
  let mut m ← vmEnsureAddr vm (outBase + 12)
  if outOdd then
    m ← vmPut m (outBase + 0) ⟨0, s.a00, 0⟩
    m ← vmPut m (outBase + 1) ⟨s.a01, s.a02, 0⟩
    m ← vmPut m (outBase + 2) ⟨s.a03, s.a04, 0⟩
    m ← vmPut m (outBase + 3) ⟨s.a05, s.a06, 0⟩
    m ← vmPut m (outBase + 4) ⟨s.a07, s.a08, 0⟩
    m ← vmPut m (outBase + 5) ⟨s.a09, s.a10, 0⟩
    m ← vmPut m (outBase + 6) ⟨s.a11, s.a12, 0⟩
    m ← vmPut m (outBase + 7) ⟨s.a13, s.a14, 0⟩
    m ← vmPut m (outBase + 8) ⟨s.a15, s.a16, 0⟩
    m ← vmPut m (outBase + 9) ⟨s.a17, s.a18, 0⟩
    m ← vmPut m (outBase + 10) ⟨s.a19, s.a20, 0⟩
    m ← vmPut m (outBase + 11) ⟨s.a21, s.a22, 0⟩
    m ← vmPut m (outBase + 12) ⟨s.a23, s.a24, 0⟩
  else
    m ← vmPut m (outBase + 0) ⟨s.a00, s.a01, 0⟩
    m ← vmPut m (outBase + 1) ⟨s.a02, s.a03, 0⟩
    m ← vmPut m (outBase + 2) ⟨s.a04, s.a05, 0⟩
    m ← vmPut m (outBase + 3) ⟨s.a06, s.a07, 0⟩
    m ← vmPut m (outBase + 4) ⟨s.a08, s.a09, 0⟩
    m ← vmPut m (outBase + 5) ⟨s.a10, s.a11, 0⟩
    m ← vmPut m (outBase + 6) ⟨s.a12, s.a13, 0⟩
    m ← vmPut m (outBase + 7) ⟨s.a14, s.a15, 0⟩
    m ← vmPut m (outBase + 8) ⟨s.a16, 0, 0⟩
    m ← vmPut m (outBase + 9) ⟨s.a17, s.a18, 0⟩
    m ← vmPut m (outBase + 10) ⟨s.a19, s.a20, 0⟩
    m ← vmPut m (outBase + 11) ⟨s.a21, s.a22, 0⟩
    m ← vmPut m (outBase + 12) ⟨s.a23, s.a24, 0⟩
  return m

@[noinline] def stepKeccakSlow (pc fp : Nat) (bcRead : UInt32)
    (i00 i01 i02 i03 i04 i05 i06 i07 i08 i09 i10 i11 i12 outBase : Nat)
    (inOdd outOdd : Bool) (vm : FastVm) : Except Fault FastVm := do
  let (w00, vm01) ← vmRead vm i00
  if w00.c2 != 0 then throw (.notCanonical w00)
  let (w01, vm02) ← vmRead vm01 i01
  if w01.c2 != 0 then throw (.notCanonical w01)
  let (w02, vm03) ← vmRead vm02 i02
  if w02.c2 != 0 then throw (.notCanonical w02)
  let (w03, vm04) ← vmRead vm03 i03
  if w03.c2 != 0 then throw (.notCanonical w03)
  let (w04, vm05) ← vmRead vm04 i04
  if w04.c2 != 0 then throw (.notCanonical w04)
  let (w05, vm06) ← vmRead vm05 i05
  if w05.c2 != 0 then throw (.notCanonical w05)
  let (w06, vm07) ← vmRead vm06 i06
  if w06.c2 != 0 then throw (.notCanonical w06)
  let (w07, vm08) ← vmRead vm07 i07
  if w07.c2 != 0 then throw (.notCanonical w07)
  let (w08, vm09) ← vmRead vm08 i08
  if w08.c2 != 0 then throw (.notCanonical w08)
  let (w09, vm10) ← vmRead vm09 i09
  if w09.c2 != 0 then throw (.notCanonical w09)
  let (w10, vm11) ← vmRead vm10 i10
  if w10.c2 != 0 then throw (.notCanonical w10)
  let (w11, vm12) ← vmRead vm11 i11
  if w11.c2 != 0 then throw (.notCanonical w11)
  let (w12, vm13) ← vmRead vm12 i12
  if w12.c2 != 0 then throw (.notCanonical w12)
  let inSt := state25FromCellsFast inOdd w00 w01 w02 w03 w04 w05 w06 w07 w08 w09 w10 w11 w12
  let outSt := keccakF1600Fast inSt
  let vmK ← putCellsFromState25Fast vm13 outBase outOdd outSt
  let (r00, vk00) ← vmBump vmK i00
  let (r01, vk01) ← vmBump vk00 i01
  let (r02, vk02) ← vmBump vk01 i02
  let (r03, vk03) ← vmBump vk02 i03
  let (r04, vk04) ← vmBump vk03 i04
  let (r05, vk05) ← vmBump vk04 i05
  let (r06, vk06) ← vmBump vk05 i06
  let (r07, vk07) ← vmBump vk06 i07
  let (r08, vk08) ← vmBump vk07 i08
  let (r09, vk09) ← vmBump vk08 i09
  let (r10, vk10) ← vmBump vk09 i10
  let (r11, vk11) ← vmBump vk10 i11
  let (r12, vk12) ← vmBump vk11 i12
  let (r13, vk13) ← vmBump vk12 (outBase + 0)
  let (r14, vk14) ← vmBump vk13 (outBase + 1)
  let (r15, vk15) ← vmBump vk14 (outBase + 2)
  let (r16, vk16) ← vmBump vk15 (outBase + 3)
  let (r17, vk17) ← vmBump vk16 (outBase + 4)
  let (r18, vk18) ← vmBump vk17 (outBase + 5)
  let (r19, vk19) ← vmBump vk18 (outBase + 6)
  let (r20, vk20) ← vmBump vk19 (outBase + 7)
  let (r21, vk21) ← vmBump vk20 (outBase + 8)
  let (r22, vk22) ← vmBump vk21 (outBase + 9)
  let (r23, vk23) ← vmBump vk22 (outBase + 10)
  let (r24, vk24) ← vmBump vk23 (outBase + 11)
  let (r25, vk25) ← vmBump vk24 (outBase + 12)
  let ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
       links, unconstrained, g, streams,
       memCap, memUsed, maxAccess, maxBcCount, _, fpU, nextFree, cycles,
       nXor, nMul, nSet, nDeref, nJump, nKeccak⟩ := vk25
  let nkNat := nKeccak.toNat
  let tKeccak := ensureBytesCap tKeccak (116 * (nkNat + 1))
  let kBase := (29 * nkNat).toUSize
  let mut tK := setU32Fast tKeccak kBase pc.toUInt32
  tK := setU32Fast tK (kBase + 1) fp.toUInt32
  tK := setU32Fast tK (kBase + 2) r00
  tK := setU32Fast tK (kBase + 3) r01
  tK := setU32Fast tK (kBase + 4) r02
  tK := setU32Fast tK (kBase + 5) r03
  tK := setU32Fast tK (kBase + 6) r04
  tK := setU32Fast tK (kBase + 7) r05
  tK := setU32Fast tK (kBase + 8) r06
  tK := setU32Fast tK (kBase + 9) r07
  tK := setU32Fast tK (kBase + 10) r08
  tK := setU32Fast tK (kBase + 11) r09
  tK := setU32Fast tK (kBase + 12) r10
  tK := setU32Fast tK (kBase + 13) r11
  tK := setU32Fast tK (kBase + 14) r12
  tK := setU32Fast tK (kBase + 15) r13
  tK := setU32Fast tK (kBase + 16) r14
  tK := setU32Fast tK (kBase + 17) r15
  tK := setU32Fast tK (kBase + 18) r16
  tK := setU32Fast tK (kBase + 19) r17
  tK := setU32Fast tK (kBase + 20) r18
  tK := setU32Fast tK (kBase + 21) r19
  tK := setU32Fast tK (kBase + 22) r20
  tK := setU32Fast tK (kBase + 23) r21
  tK := setU32Fast tK (kBase + 24) r22
  tK := setU32Fast tK (kBase + 25) r23
  tK := setU32Fast tK (kBase + 26) r24
  tK := setU32Fast tK (kBase + 27) r25
  tK := setU32Fast tK (kBase + 28) bcRead
  return ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tK,
          links, unconstrained, g, streams,
          memCap, memUsed, maxAccess, maxBcCount, (pc + 1).toUInt64, fpU, nextFree, cycles + 1,
          nXor, nMul, nSet, nDeref, nJump, nKeccak + 1⟩

@[inline] def bumpIdxFast (mAccess : ByteArray) (maxAcc : UInt64) (idx : USize) :
    UInt32 × ByteArray × UInt64 :=
  let cnt := getU32Fast mAccess idx
  let cnt1 := cnt + 1
  let cnt1U := cnt1.toUInt64
  let maxAcc' := if cnt1U > maxAcc then cnt1U else maxAcc
  (cnt, setU32Fast mAccess idx cnt1, maxAcc')

@[inline] def maxU64 (a b : UInt64) : UInt64 := if a >= b then a else b

set_option maxHeartbeats 1600000 in
@[noinline] def stepKeccakFast (opWords : @& ByteArray) (opBase : USize) (pcU fpU : UInt64)
    (bcRead : UInt32) (vm : FastVm) : Except Fault FastVm := do
  let m0 := getU64Fast opWords (opBase + 1)
  let m1 := getU64Fast opWords (opBase + 2)
  let m2 := getU64Fast opWords (opBase + 3)
  let m3 := getU64Fast opWords (opBase + 4)
  let tail := getU64Fast opWords (opBase + 5)
  let b8 := getU64Fast opWords (opBase + 6)
  let cap := getU64Fast opWords (opBase + 7)
  let out := getU64Fast opWords (opBase + 8)
  let inOdd := getU64Fast opWords (opBase + 9) != 0
  let outOdd := getU64Fast opWords (opBase + 10) != 0
  let i00 := fpU + m0
  let i01 := fpU + m1
  let i02 := fpU + m2
  let i03 := fpU + m3
  let i04 := fpU + tail
  let i05 := i04 + 1
  let i06 := i04 + 2
  let i07 := i04 + 3
  let i08 := fpU + b8
  let i09 := fpU + cap
  let i10 := i09 + 1
  let i11 := i09 + 2
  let i12 := i09 + 3
  let outBase := fpU + out
  let maxAddr :=
    maxU64 (outBase + 12)
      (maxU64 (maxU64 (maxU64 i00 i01) (maxU64 i02 i03))
              (maxU64 (maxU64 i07 i08) i12))
  if maxAddr + 1 > vm.memCap then
    return ← stepKeccakSlow pcU.toNat fpU.toNat bcRead
      i00.toNat i01.toNat i02.toNat i03.toNat i04.toNat i05.toNat i06.toNat i07.toNat
      i08.toNat i09.toNat i10.toNat i11.toNat i12.toNat outBase.toNat inOdd outOdd vm
  let u00 := i00.toUSize; let u01 := i01.toUSize; let u02 := i02.toUSize; let u03 := i03.toUSize
  let u04 := i04.toUSize; let u05 := i05.toUSize; let u06 := i06.toUSize; let u07 := i07.toUSize
  let u08 := i08.toUSize; let u09 := i09.toUSize; let u10 := i10.toUSize; let u11 := i11.toUSize
  let u12 := i12.toUSize
  let stInOk :=
    getU8Fast vm.mState u00 == 1 && getU8Fast vm.mState u01 == 1 &&
    getU8Fast vm.mState u02 == 1 && getU8Fast vm.mState u03 == 1 &&
    getU8Fast vm.mState u04 == 1 && getU8Fast vm.mState u05 == 1 &&
    getU8Fast vm.mState u06 == 1 && getU8Fast vm.mState u07 == 1 &&
    getU8Fast vm.mState u08 == 1 && getU8Fast vm.mState u09 == 1 &&
    getU8Fast vm.mState u10 == 1 && getU8Fast vm.mState u11 == 1 &&
    getU8Fast vm.mState u12 == 1
  let o00 := outBase.toUSize; let o01 := (outBase + 1).toUSize
  let o02 := (outBase + 2).toUSize; let o03 := (outBase + 3).toUSize
  let o04 := (outBase + 4).toUSize; let o05 := (outBase + 5).toUSize
  let o06 := (outBase + 6).toUSize; let o07 := (outBase + 7).toUSize
  let o08 := (outBase + 8).toUSize; let o09 := (outBase + 9).toUSize
  let o10 := (outBase + 10).toUSize; let o11 := (outBase + 11).toUSize
  let o12 := (outBase + 12).toUSize
  let stOutFresh :=
    getU8Fast vm.mState o00 == 0 && getU8Fast vm.mState o01 == 0 &&
    getU8Fast vm.mState o02 == 0 && getU8Fast vm.mState o03 == 0 &&
    getU8Fast vm.mState o04 == 0 && getU8Fast vm.mState o05 == 0 &&
    getU8Fast vm.mState o06 == 0 && getU8Fast vm.mState o07 == 0 &&
    getU8Fast vm.mState o08 == 0 && getU8Fast vm.mState o09 == 0 &&
    getU8Fast vm.mState o10 == 0 && getU8Fast vm.mState o11 == 0 &&
    getU8Fast vm.mState o12 == 0
  if !stInOk || !stOutFresh then
    return ← stepKeccakSlow pcU.toNat fpU.toNat bcRead
      i00.toNat i01.toNat i02.toNat i03.toNat i04.toNat i05.toNat i06.toNat i07.toNat
      i08.toNat i09.toNat i10.toNat i11.toNat i12.toNat outBase.toNat inOdd outOdd vm
  let c2Or :=
    getU64Fast vm.mc2 u00 ||| getU64Fast vm.mc2 u01 ||| getU64Fast vm.mc2 u02 |||
    getU64Fast vm.mc2 u03 ||| getU64Fast vm.mc2 u04 ||| getU64Fast vm.mc2 u05 |||
    getU64Fast vm.mc2 u06 ||| getU64Fast vm.mc2 u07 ||| getU64Fast vm.mc2 u08 |||
    getU64Fast vm.mc2 u09 ||| getU64Fast vm.mc2 u10 ||| getU64Fast vm.mc2 u11 |||
    getU64Fast vm.mc2 u12
  if c2Or != 0 then
    return ← stepKeccakSlow pcU.toNat fpU.toNat bcRead
      i00.toNat i01.toNat i02.toNat i03.toNat i04.toNat i05.toNat i06.toNat i07.toNat
      i08.toNat i09.toNat i10.toNat i11.toNat i12.toNat outBase.toNat inOdd outOdd vm
  let ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
       links, unconstrained, g, streams,
       memCap, memUsed, maxAccess, maxBcCount, _, fpCur, nextFree, cycles,
       nXor, nMul, nSet, nDeref, nJump, nKeccak⟩ := vm
  let inSt : State25 :=
    if inOdd then
      ⟨getU64Fast mc1 u00, getU64Fast mc0 u01, getU64Fast mc1 u01, getU64Fast mc0 u02, getU64Fast mc1 u02,
       getU64Fast mc0 u03, getU64Fast mc1 u03, getU64Fast mc0 u04, getU64Fast mc1 u04, getU64Fast mc0 u05,
       getU64Fast mc1 u05, getU64Fast mc0 u06, getU64Fast mc1 u06, getU64Fast mc0 u07, getU64Fast mc1 u07,
       getU64Fast mc0 u08, getU64Fast mc1 u08, getU64Fast mc0 u09, getU64Fast mc1 u09, getU64Fast mc0 u10,
       getU64Fast mc1 u10, getU64Fast mc0 u11, getU64Fast mc1 u11, getU64Fast mc0 u12, getU64Fast mc1 u12⟩
    else
      ⟨getU64Fast mc0 u00, getU64Fast mc1 u00, getU64Fast mc0 u01, getU64Fast mc1 u01, getU64Fast mc0 u02,
       getU64Fast mc1 u02, getU64Fast mc0 u03, getU64Fast mc1 u03, getU64Fast mc0 u04, getU64Fast mc1 u04,
       getU64Fast mc0 u05, getU64Fast mc1 u05, getU64Fast mc0 u06, getU64Fast mc1 u06, getU64Fast mc0 u07,
       getU64Fast mc1 u07, getU64Fast mc0 u08, getU64Fast mc0 u09, getU64Fast mc1 u09, getU64Fast mc0 u10,
       getU64Fast mc1 u10, getU64Fast mc0 u11, getU64Fast mc1 u11, getU64Fast mc0 u12, getU64Fast mc1 u12⟩
  let s := keccakF1600Fast inSt
  let mut mc0' := mc0
  let mut mc1' := mc1
  if outOdd then
    mc1' := setU64Fast mc1' o00 s.a00
    mc0' := setU64Fast mc0' o01 s.a01; mc1' := setU64Fast mc1' o01 s.a02
    mc0' := setU64Fast mc0' o02 s.a03; mc1' := setU64Fast mc1' o02 s.a04
    mc0' := setU64Fast mc0' o03 s.a05; mc1' := setU64Fast mc1' o03 s.a06
    mc0' := setU64Fast mc0' o04 s.a07; mc1' := setU64Fast mc1' o04 s.a08
    mc0' := setU64Fast mc0' o05 s.a09; mc1' := setU64Fast mc1' o05 s.a10
    mc0' := setU64Fast mc0' o06 s.a11; mc1' := setU64Fast mc1' o06 s.a12
    mc0' := setU64Fast mc0' o07 s.a13; mc1' := setU64Fast mc1' o07 s.a14
    mc0' := setU64Fast mc0' o08 s.a15; mc1' := setU64Fast mc1' o08 s.a16
    mc0' := setU64Fast mc0' o09 s.a17; mc1' := setU64Fast mc1' o09 s.a18
    mc0' := setU64Fast mc0' o10 s.a19; mc1' := setU64Fast mc1' o10 s.a20
    mc0' := setU64Fast mc0' o11 s.a21; mc1' := setU64Fast mc1' o11 s.a22
    mc0' := setU64Fast mc0' o12 s.a23; mc1' := setU64Fast mc1' o12 s.a24
  else
    mc0' := setU64Fast mc0' o00 s.a00; mc1' := setU64Fast mc1' o00 s.a01
    mc0' := setU64Fast mc0' o01 s.a02; mc1' := setU64Fast mc1' o01 s.a03
    mc0' := setU64Fast mc0' o02 s.a04; mc1' := setU64Fast mc1' o02 s.a05
    mc0' := setU64Fast mc0' o03 s.a06; mc1' := setU64Fast mc1' o03 s.a07
    mc0' := setU64Fast mc0' o04 s.a08; mc1' := setU64Fast mc1' o04 s.a09
    mc0' := setU64Fast mc0' o05 s.a10; mc1' := setU64Fast mc1' o05 s.a11
    mc0' := setU64Fast mc0' o06 s.a12; mc1' := setU64Fast mc1' o06 s.a13
    mc0' := setU64Fast mc0' o07 s.a14; mc1' := setU64Fast mc1' o07 s.a15
    mc0' := setU64Fast mc0' o08 s.a16
    mc0' := setU64Fast mc0' o09 s.a17; mc1' := setU64Fast mc1' o09 s.a18
    mc0' := setU64Fast mc0' o10 s.a19; mc1' := setU64Fast mc1' o10 s.a20
    mc0' := setU64Fast mc0' o11 s.a21; mc1' := setU64Fast mc1' o11 s.a22
    mc0' := setU64Fast mc0' o12 s.a23; mc1' := setU64Fast mc1' o12 s.a24
  let mut mState' := setU8Fast mState o00 1
  mState' := setU8Fast mState' o01 1; mState' := setU8Fast mState' o02 1
  mState' := setU8Fast mState' o03 1; mState' := setU8Fast mState' o04 1
  mState' := setU8Fast mState' o05 1; mState' := setU8Fast mState' o06 1
  mState' := setU8Fast mState' o07 1; mState' := setU8Fast mState' o08 1
  mState' := setU8Fast mState' o09 1; mState' := setU8Fast mState' o10 1
  mState' := setU8Fast mState' o11 1; mState' := setU8Fast mState' o12 1
  let (r00, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess u00
  let (r01, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess u01
  let (r02, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess u02
  let (r03, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess u03
  let (r04, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess u04
  let (r05, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess u05
  let (r06, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess u06
  let (r07, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess u07
  let (r08, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess u08
  let (r09, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess u09
  let (r10, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess u10
  let (r11, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess u11
  let (r12, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess u12
  let (r13, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess o00
  let (r14, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess o01
  let (r15, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess o02
  let (r16, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess o03
  let (r17, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess o04
  let (r18, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess o05
  let (r19, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess o06
  let (r20, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess o07
  let (r21, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess o08
  let (r22, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess o09
  let (r23, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess o10
  let (r24, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess o11
  let (r25, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess o12
  let end1 := maxAddr + 1
  let memUsed' := if end1 > memUsed then end1 else memUsed
  let nkU := nKeccak.toUSize
  let tKeccak :=
    if ((nKeccak + 1) * 116).toUSize <= tKeccak.size.toUSize then tKeccak
    else growBytesCap tKeccak ((nKeccak + 1).toNat * 116)
  let kBase := nkU * 29
  let mut tK := setU32Fast tKeccak kBase pcU.toUInt32
  tK := setU32Fast tK (kBase + 1) fpU.toUInt32
  tK := setU32Fast tK (kBase + 2) r00
  tK := setU32Fast tK (kBase + 3) r01
  tK := setU32Fast tK (kBase + 4) r02
  tK := setU32Fast tK (kBase + 5) r03
  tK := setU32Fast tK (kBase + 6) r04
  tK := setU32Fast tK (kBase + 7) r05
  tK := setU32Fast tK (kBase + 8) r06
  tK := setU32Fast tK (kBase + 9) r07
  tK := setU32Fast tK (kBase + 10) r08
  tK := setU32Fast tK (kBase + 11) r09
  tK := setU32Fast tK (kBase + 12) r10
  tK := setU32Fast tK (kBase + 13) r11
  tK := setU32Fast tK (kBase + 14) r12
  tK := setU32Fast tK (kBase + 15) r13
  tK := setU32Fast tK (kBase + 16) r14
  tK := setU32Fast tK (kBase + 17) r15
  tK := setU32Fast tK (kBase + 18) r16
  tK := setU32Fast tK (kBase + 19) r17
  tK := setU32Fast tK (kBase + 20) r18
  tK := setU32Fast tK (kBase + 21) r19
  tK := setU32Fast tK (kBase + 22) r20
  tK := setU32Fast tK (kBase + 23) r21
  tK := setU32Fast tK (kBase + 24) r22
  tK := setU32Fast tK (kBase + 25) r23
  tK := setU32Fast tK (kBase + 26) r24
  tK := setU32Fast tK (kBase + 27) r25
  tK := setU32Fast tK (kBase + 28) bcRead
  return ⟨mc0', mc1', mc2, mState', mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tK,
          links, unconstrained, g, streams,
          memCap, memUsed', maxAccess, maxBcCount, pcU + 1, fpCur, nextFree, cycles + 1,
          nXor, nMul, nSet, nDeref, nJump, nKeccak + 1⟩

/-! ## Per-Opcode Linear Step Helpers & Main Planar VM Execution Loop (`executeFastWith`) -/

def vmPrepStep (vm : FastVm) : UInt32 × FastVm :=
  let ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
       links, unconstrained, g, streams,
       memCap, memUsed, maxAccess, maxBcCount, pc, fp, nextFree, cycles,
       nXor, nMul, nSet, nDeref, nJump, nKeccak⟩ := vm
  let pcNat := pc.toNat
  let fpNat := fp.toNat
  let needG := max (pcNat + 2) fpNat
  let g := if needG >= g.len then g.grow needG else g
  let pcIdx := pcNat.toUSize
  let bcRead := getU32Fast bcCounts pcIdx
  let bcNext := bcRead + 1
  let bcNextU := bcNext.toUInt64
  let maxBcCount := if bcNextU > maxBcCount then bcNextU else maxBcCount
  let bcCounts := setU32Fast bcCounts pcIdx bcNext
  (bcRead, ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
            links, unconstrained, g, streams,
            memCap, memUsed, maxAccess, maxBcCount, pc, fp, nextFree, cycles,
            nXor, nMul, nSet, nDeref, nJump, nKeccak⟩)

@[noinline] def stepXorSlow (pc fp aa ab ac : Nat) (bcRead : UInt32)
    (vm : FastVm) : Except Fault FastVm := do
  let (va, vm1) ← vmRead vm aa
  let (vb, vm2) ← vmRead vm1 ab
  let vc : E := ⟨va.c0 ^^^ vb.c0, va.c1 ^^^ vb.c1, va.c2 ^^^ vb.c2⟩
  let vm3 ← vmPut vm2 ac vc
  let (ra, vm4) ← vmBump vm3 aa
  let (rb, vm5) ← vmBump vm4 ab
  let (rc, vm6) ← vmBump vm5 ac
  let ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
       links, unconstrained, g, streams,
       memCap, memUsed, maxAccess, maxBcCount, _, fpU, nextFree, cycles,
       nXor, nMul, nSet, nDeref, nJump, nKeccak⟩ := vm6
  let (tXor, nXor) := pushRow6 tXor nXor pc.toUInt32 fp.toUInt32 ra rb rc bcRead
  return ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
          links, unconstrained, g, streams,
          memCap, memUsed, maxAccess, maxBcCount, (pc + 1).toUInt64, fpU, nextFree, cycles + 1,
          nXor, nMul, nSet, nDeref, nJump, nKeccak⟩

@[inline] def stepXorFast (opWords : @& ByteArray) (opBase : USize) (pcU fpU : UInt64)
    (bcRead : UInt32) (vm : FastVm) : Except Fault FastVm := do
  let a := getU64Fast opWords (opBase + 1)
  let b := getU64Fast opWords (opBase + 2)
  let c := getU64Fast opWords (opBase + 3)
  let aa := fpU + a
  let ab := fpU + b
  let ac := fpU + c
  let maxAddr := maxU64 aa (maxU64 ab ac)
  let ua := aa.toUSize; let ub := ab.toUSize; let uc := ac.toUSize
  if maxAddr + 1 <= vm.memCap &&
      getU8Fast vm.mState ua == 1 && getU8Fast vm.mState ub == 1 && getU8Fast vm.mState uc == 0 then
    let ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
         links, unconstrained, g, streams,
         memCap, memUsed, maxAccess, maxBcCount, _, fpCur, nextFree, cycles,
         nXor, nMul, nSet, nDeref, nJump, nKeccak⟩ := vm
    let c0 := getU64Fast mc0 ua ^^^ getU64Fast mc0 ub
    let c1 := getU64Fast mc1 ua ^^^ getU64Fast mc1 ub
    let c2 := getU64Fast mc2 ua ^^^ getU64Fast mc2 ub
    let mc0 := if c0 != 0 then setU64Fast mc0 uc c0 else mc0
    let mc1 := if c1 != 0 then setU64Fast mc1 uc c1 else mc1
    let mc2 := if c2 != 0 then setU64Fast mc2 uc c2 else mc2
    let mState := setU8Fast mState uc 1
    let (ra, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess ua
    let (rb, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess ub
    let (rc, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess uc
    let end1 := maxAddr + 1
    let memUsed := if end1 > memUsed then end1 else memUsed
    let (tXor, nXor) := pushRow6 tXor nXor pcU.toUInt32 fpU.toUInt32 ra rb rc bcRead
    return ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
            links, unconstrained, g, streams,
            memCap, memUsed, maxAccess, maxBcCount, pcU + 1, fpCur, nextFree, cycles + 1,
            nXor, nMul, nSet, nDeref, nJump, nKeccak⟩
  else
    stepXorSlow pcU.toNat fpU.toNat aa.toNat ab.toNat ac.toNat bcRead vm

@[noinline] def stepMulSlow (pc fp aa ab ac : Nat) (bcRead : UInt32)
    (vm : FastVm) : Except Fault FastVm := do
  let mut vmWork := vm
  if vmIsWritten vmWork ac then
    let ha := vmIsWritten vmWork aa
    let hb := vmIsWritten vmWork ab
    if ha != hb then
      let known := vmGetWord vmWork (if ha then aa else ab)
      if known.c0 == 0 && known.c1 == 0 && known.c2 == 0 then
        throw .backSolveThroughZero
      let solved := Model.Field.nativeKaratsuba (vmGetWord vmWork ac) (inverseFastE known)
      vmWork ← vmPut vmWork (if ha then ab else aa) solved
  let (va, vm1) ← vmRead vmWork aa
  let (vb, vm2) ← vmRead vm1 ab
  let vc := Model.Field.nativeKaratsuba va vb
  let vm3 ← vmPut vm2 ac vc
  let (ra, vm4) ← vmBump vm3 aa
  let (rb, vm5) ← vmBump vm4 ab
  let (rc, vm6) ← vmBump vm5 ac
  let ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
       links, unconstrained, g, streams,
       memCap, memUsed, maxAccess, maxBcCount, _, fpU, nextFree, cycles,
       nXor, nMul, nSet, nDeref, nJump, nKeccak⟩ := vm6
  let (tMul, nMul) := pushRow6 tMul nMul pc.toUInt32 fp.toUInt32 ra rb rc bcRead
  return ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
          links, unconstrained, g, streams,
          memCap, memUsed, maxAccess, maxBcCount, (pc + 1).toUInt64, fpU, nextFree, cycles + 1,
          nXor, nMul, nSet, nDeref, nJump, nKeccak⟩

@[inline] def stepMulFast (opWords : @& ByteArray) (opBase : USize) (pcU fpU : UInt64)
    (bcRead : UInt32) (vm : FastVm) : Except Fault FastVm := do
  let a := getU64Fast opWords (opBase + 1)
  let b := getU64Fast opWords (opBase + 2)
  let c := getU64Fast opWords (opBase + 3)
  let aa := fpU + a
  let ab := fpU + b
  let ac := fpU + c
  let maxAddr := maxU64 aa (maxU64 ab ac)
  let ua := aa.toUSize; let ub := ab.toUSize; let uc := ac.toUSize
  if maxAddr + 1 <= vm.memCap &&
      getU8Fast vm.mState ua == 1 && getU8Fast vm.mState ub == 1 && getU8Fast vm.mState uc == 0 then
    let ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
         links, unconstrained, g, streams,
         memCap, memUsed, maxAccess, maxBcCount, _, fpCur, nextFree, cycles,
         nXor, nMul, nSet, nDeref, nJump, nKeccak⟩ := vm
    let a0 := getU64Fast mc0 ua; let a1 := getU64Fast mc1 ua; let a2 := getU64Fast mc2 ua
    let b0 := getU64Fast mc0 ub; let b1 := getU64Fast mc1 ub; let b2 := getU64Fast mc2 ub
    let vc : E :=
      if (a1 ||| a2 ||| b1 ||| b2) == 0 then
        ⟨Model.Field.nativeMul a0 b0, 0, 0⟩
      else
        Model.Field.nativeKaratsuba ⟨a0, a1, a2⟩ ⟨b0, b1, b2⟩
    let mc0 := if vc.c0 != 0 then setU64Fast mc0 uc vc.c0 else mc0
    let mc1 := if vc.c1 != 0 then setU64Fast mc1 uc vc.c1 else mc1
    let mc2 := if vc.c2 != 0 then setU64Fast mc2 uc vc.c2 else mc2
    let mState := setU8Fast mState uc 1
    let (ra, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess ua
    let (rb, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess ub
    let (rc, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess uc
    let end1 := maxAddr + 1
    let memUsed := if end1 > memUsed then end1 else memUsed
    let (tMul, nMul) := pushRow6 tMul nMul pcU.toUInt32 fpU.toUInt32 ra rb rc bcRead
    return ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
            links, unconstrained, g, streams,
            memCap, memUsed, maxAccess, maxBcCount, pcU + 1, fpCur, nextFree, cycles + 1,
            nXor, nMul, nSet, nDeref, nJump, nKeccak⟩
  else
    stepMulSlow pcU.toNat fpU.toNat aa.toNat ab.toNat ac.toNat bcRead vm

@[noinline] def stepSetSlow (pc fp addr : Nat) (val : E) (bcRead : UInt32)
    (vm : FastVm) : Except Fault FastVm := do
  let vm1 ← vmPut vm addr val
  let (r, vm2) ← vmBump vm1 addr
  let ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
       links, unconstrained, g, streams,
       memCap, memUsed, maxAccess, maxBcCount, _, fpU, nextFree, cycles,
       nXor, nMul, nSet, nDeref, nJump, nKeccak⟩ := vm2
  let (tSet, nSet) := pushRow4 tSet nSet pc.toUInt32 fp.toUInt32 r bcRead
  return ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
          links, unconstrained, g, streams,
          memCap, memUsed, maxAccess, maxBcCount, (pc + 1).toUInt64, fpU, nextFree, cycles + 1,
          nXor, nMul, nSet, nDeref, nJump, nKeccak⟩

@[inline] def stepSetFast (opWords : @& ByteArray) (opBase : USize) (pcU fpU : UInt64)
    (bcRead : UInt32) (vm : FastVm) : Except Fault FastVm := do
  let off := getU64Fast opWords (opBase + 1)
  let val : E := ⟨getU64Fast opWords (opBase + 2),
    getU64Fast opWords (opBase + 3), getU64Fast opWords (opBase + 4)⟩
  let addr := fpU + off
  let u := addr.toUSize
  if addr + 1 <= vm.memCap && getU8Fast vm.mState u == 0 then
    let ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
         links, unconstrained, g, streams,
         memCap, memUsed, maxAccess, maxBcCount, _, fpCur, nextFree, cycles,
         nXor, nMul, nSet, nDeref, nJump, nKeccak⟩ := vm
    let mc0 := if val.c0 != 0 then setU64Fast mc0 u val.c0 else mc0
    let mc1 := if val.c1 != 0 then setU64Fast mc1 u val.c1 else mc1
    let mc2 := if val.c2 != 0 then setU64Fast mc2 u val.c2 else mc2
    let mState := setU8Fast mState u 1
    let (r, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess u
    let end1 := addr + 1
    let memUsed := if end1 > memUsed then end1 else memUsed
    let (tSet, nSet) := pushRow4 tSet nSet pcU.toUInt32 fpU.toUInt32 r bcRead
    return ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
            links, unconstrained, g, streams,
            memCap, memUsed, maxAccess, maxBcCount, pcU + 1, fpCur, nextFree, cycles + 1,
            nXor, nMul, nSet, nDeref, nJump, nKeccak⟩
  else
    stepSetSlow pcU.toNat fpU.toNat addr.toNat val bcRead vm

@[noinline] def stepDerefSlow (pc fp o1 o2 o3 : Nat) (mTag : UInt64) (bcRead : UInt32)
    (vm : FastVm) : Except Fault FastVm := do
  let a1 := fp + o1
  let (p, vm1) ← vmRead vm a1
  let base ← vm1.g.logE p
  let a2 := base + o2
  let a3 := fp + o3
  let vm2 ←
    if mTag == 0 then
      if vmIsWritten vm1 a2 then
        let w2 := vmGetWord vm1 a2
        vmPut vm1 a3 w2
      else if vmIsWritten vm1 a3 then
        let w3 := vmGetWord vm1 a3
        vmPut vm1 a2 w3
      else
        vmLinkCold vm1 a2 a3
    else if mTag == 1 then
      let wPc : E := ⟨vm1.g.powAt (pc + 2), 0, 0⟩
      vmPut vm1 a2 wPc
    else
      let wFp : E := ⟨vm1.g.powAt fp, 0, 0⟩
      vmPut vm1 a2 wFp
  let (r1, vm3) ← vmBump vm2 a1
  let (r2, vm4) ← vmBump vm3 a2
  let (r3, vm5) ← vmBump vm4 a3
  let ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
       links, unconstrained, g, streams,
       memCap, memUsed, maxAccess, maxBcCount, _, fpU, nextFree, cycles,
       nXor, nMul, nSet, nDeref, nJump, nKeccak⟩ := vm5
  let (tDeref, nDeref) := pushRow6 tDeref nDeref pc.toUInt32 fp.toUInt32 r1 r2 r3 bcRead
  return ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
          links, unconstrained, g, streams,
          memCap, memUsed, maxAccess, maxBcCount, (pc + 1).toUInt64, fpU, nextFree, cycles + 1,
          nXor, nMul, nSet, nDeref, nJump, nKeccak⟩

@[inline] def stepDerefFast (opWords : @& ByteArray) (opBase : USize) (pcU fpU : UInt64)
    (bcRead : UInt32) (vm : FastVm) : Except Fault FastVm := do
  let o1 := getU64Fast opWords (opBase + 1)
  let o2 := getU64Fast opWords (opBase + 2)
  let o3 := getU64Fast opWords (opBase + 3)
  let mTag := getU64Fast opWords (opBase + 4)
  let a1 := fpU + o1
  let u1 := a1.toUSize
  if a1 + 1 <= vm.memCap && getU8Fast vm.mState u1 == 1 &&
      getU64Fast vm.mc1 u1 == 0 && getU64Fast vm.mc2 u1 == 0 then
    let rBase := vm.g.logU64Raw (getU64Fast vm.mc0 u1)
    if rBase == 0 then
      stepDerefSlow pcU.toNat fpU.toNat o1.toNat o2.toNat o3.toNat mTag bcRead vm
    else
      let base := rBase - 1
      let a2 := base + o2
      let a3 := fpU + o3
      let maxAddr := maxU64 a1 (maxU64 a2 a3)
      let u2 := a2.toUSize; let u3 := a3.toUSize
      if maxAddr + 1 <= vm.memCap then
        let s2 := getU8Fast vm.mState u2
        let s3 := getU8Fast vm.mState u3
        if mTag == 0 && ((s2 == 1 && s3 == 0) || (s2 == 0 && s3 == 1)) then
          let ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
               links, unconstrained, g, streams,
               memCap, memUsed, maxAccess, maxBcCount, _, fpCur, nextFree, cycles,
               nXor, nMul, nSet, nDeref, nJump, nKeccak⟩ := vm
          let (src, dst) := if s2 == 1 then (u2, u3) else (u3, u2)
          let w0 := getU64Fast mc0 src
          let w1 := getU64Fast mc1 src
          let w2 := getU64Fast mc2 src
          let mc0 := if w0 != 0 then setU64Fast mc0 dst w0 else mc0
          let mc1 := if w1 != 0 then setU64Fast mc1 dst w1 else mc1
          let mc2 := if w2 != 0 then setU64Fast mc2 dst w2 else mc2
          let mState := setU8Fast mState dst 1
          let (r1, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess u1
          let (r2, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess u2
          let (r3, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess u3
          let end1 := maxAddr + 1
          let memUsed := if end1 > memUsed then end1 else memUsed
          let (tDeref, nDeref) := pushRow6 tDeref nDeref pcU.toUInt32 fpU.toUInt32 r1 r2 r3 bcRead
          return ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
                  links, unconstrained, g, streams,
                  memCap, memUsed, maxAccess, maxBcCount, pcU + 1, fpCur, nextFree, cycles + 1,
                  nXor, nMul, nSet, nDeref, nJump, nKeccak⟩
        else if mTag != 0 && s2 == 0 then
          let ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
               links, unconstrained, g, streams,
               memCap, memUsed, maxAccess, maxBcCount, _, fpCur, nextFree, cycles,
               nXor, nMul, nSet, nDeref, nJump, nKeccak⟩ := vm
          let v0 :=
            if mTag == 1 then getU64Fast g.pows (pcU + 2).toUSize
            else getU64Fast g.pows fpU.toUSize
          let mc0 := setU64Fast mc0 u2 v0
          let mState := setU8Fast mState u2 1
          let (r1, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess u1
          let (r2, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess u2
          let (r3, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess u3
          let end1 := maxAddr + 1
          let memUsed := if end1 > memUsed then end1 else memUsed
          let (tDeref, nDeref) := pushRow6 tDeref nDeref pcU.toUInt32 fpU.toUInt32 r1 r2 r3 bcRead
          return ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
                  links, unconstrained, g, streams,
                  memCap, memUsed, maxAccess, maxBcCount, pcU + 1, fpCur, nextFree, cycles + 1,
                  nXor, nMul, nSet, nDeref, nJump, nKeccak⟩
        else
          stepDerefSlow pcU.toNat fpU.toNat o1.toNat o2.toNat o3.toNat mTag bcRead vm
      else
        stepDerefSlow pcU.toNat fpU.toNat o1.toNat o2.toNat o3.toNat mTag bcRead vm
  else
    stepDerefSlow pcU.toNat fpU.toNat o1.toNat o2.toNat o3.toNat mTag bcRead vm

@[noinline] def stepJumpSlow (pc fp ac ad af : Nat) (bcRead : UInt32)
    (vm : FastVm) : Except Fault FastVm := do
  let (vc, vm1) ← vmRead vm ac
  let (vd, vm2) ← vmRead vm1 ad
  let (vf, vm3) ← vmRead vm2 af
  if vc.c1 != 0 || vc.c2 != 0 then throw (.notInK vc)
  if vd.c1 != 0 || vd.c2 != 0 then throw (.notInK vd)
  if vf.c1 != 0 || vf.c2 != 0 then throw (.notInK vf)
  let mut nextPc := pc + 1
  let mut nextFp := fp
  if vc.c0 != 0 then
    nextPc ← vm3.g.logE vd
    nextFp ← vm3.g.logE vf
  let (rc, vm4) ← vmBump vm3 ac
  let (rd, vm5) ← vmBump vm4 ad
  let (rf, vm6) ← vmBump vm5 af
  let ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
       links, unconstrained, g, streams,
       memCap, memUsed, maxAccess, maxBcCount, _, _, nextFree, cycles,
       nXor, nMul, nSet, nDeref, nJump, nKeccak⟩ := vm6
  let (tJump, nJump) := pushRow6 tJump nJump pc.toUInt32 fp.toUInt32 rc rd rf bcRead
  return ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
          links, unconstrained, g, streams,
          memCap, memUsed, maxAccess, maxBcCount, nextPc.toUInt64, nextFp.toUInt64, nextFree, cycles + 1,
          nXor, nMul, nSet, nDeref, nJump, nKeccak⟩

@[inline] def stepJumpFast (opWords : @& ByteArray) (opBase : USize) (pcU fpU : UInt64)
    (bcRead : UInt32) (vm : FastVm) : Except Fault FastVm := do
  let oc := getU64Fast opWords (opBase + 1)
  let od := getU64Fast opWords (opBase + 2)
  let of_ := getU64Fast opWords (opBase + 3)
  let ac := fpU + oc
  let ad := fpU + od
  let af := fpU + of_
  let maxAddr := maxU64 ac (maxU64 ad af)
  let uc := ac.toUSize; let ud := ad.toUSize; let uf := af.toUSize
  if maxAddr + 1 <= vm.memCap &&
      getU8Fast vm.mState uc == 1 && getU8Fast vm.mState ud == 1 && getU8Fast vm.mState uf == 1 &&
      (getU64Fast vm.mc1 uc ||| getU64Fast vm.mc2 uc |||
       getU64Fast vm.mc1 ud ||| getU64Fast vm.mc2 ud |||
       getU64Fast vm.mc1 uf ||| getU64Fast vm.mc2 uf) == 0 then
    let c0 := getU64Fast vm.mc0 uc
    let d0 := getU64Fast vm.mc0 ud
    let f0 := getU64Fast vm.mc0 uf
    if c0 == 0 then
      let ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
           links, unconstrained, g, streams,
           memCap, memUsed, maxAccess, maxBcCount, _, _, nextFree, cycles,
           nXor, nMul, nSet, nDeref, nJump, nKeccak⟩ := vm
      let (rc, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess uc
      let (rd, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess ud
      let (rf, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess uf
      let end1 := maxAddr + 1
      let memUsed := if end1 > memUsed then end1 else memUsed
      let (tJump, nJump) := pushRow6 tJump nJump pcU.toUInt32 fpU.toUInt32 rc rd rf bcRead
      return ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
              links, unconstrained, g, streams,
              memCap, memUsed, maxAccess, maxBcCount, pcU + 1, fpU, nextFree, cycles + 1,
              nXor, nMul, nSet, nDeref, nJump, nKeccak⟩
    else
      let rd1 := vm.g.logU64Raw d0
      let rf1 := vm.g.logU64Raw f0
      if rd1 != 0 && rf1 != 0 then
        let ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
             links, unconstrained, g, streams,
             memCap, memUsed, maxAccess, maxBcCount, _, _, nextFree, cycles,
             nXor, nMul, nSet, nDeref, nJump, nKeccak⟩ := vm
        let (rc, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess uc
        let (rd, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess ud
        let (rf, mAccess, maxAccess) := bumpIdxFast mAccess maxAccess uf
        let end1 := maxAddr + 1
        let memUsed := if end1 > memUsed then end1 else memUsed
        let (tJump, nJump) := pushRow6 tJump nJump pcU.toUInt32 fpU.toUInt32 rc rd rf bcRead
        return ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
                links, unconstrained, g, streams,
                memCap, memUsed, maxAccess, maxBcCount, rd1 - 1, rf1 - 1, nextFree, cycles + 1,
                nXor, nMul, nSet, nDeref, nJump, nKeccak⟩
      else
        stepJumpSlow pcU.toNat fpU.toNat ac.toNat ad.toNat af.toNat bcRead vm
  else
    stepJumpSlow pcU.toNat fpU.toNat ac.toNat ad.toNat af.toNat bcRead vm

def estimateStreamWords (streams : @& FastStreams) : Nat := Id.run do
  let mut total := 0
  for es in streams.entries do
    for e in es do
      total := total + e.size
  return total

set_option maxHeartbeats 1600000 in
@[noinline] def applyHintsAtPc (streamNames : @& Array String)
    (hintLists : @& Array (Array FastRHint)) (hIdx : Nat) (vm : FastVm) :
    Except Fault FastVm := do
  let hs := hintLists[hIdx - 1]?.getD #[]
  let mut cur := vm
  for h in hs do
    cur ← applyFastHint streamNames h cur
  return cur

def executeFastLoop (nProgU : UInt64) (opWords : @& ByteArray) (hintAt : @& ByteArray)
    (hintLists : @& Array (Array FastRHint)) (streamNames : @& Array String) :
    Nat → FastVm → Except Fault FastVm
  | 0, vm =>
    if vm.pc + 1 == nProgU && vm.fp == 0 then .ok vm
    else .error .stepLimit
  | fuel + 1, vm =>
    let pc0 := vm.pc
    let fp0 := vm.fp
    if pc0 + 1 == nProgU && fp0 == 0 then
      .ok vm
    else if pc0 >= nProgU then
      .error .badProgram
    else
      let hIdx := getU32Fast hintAt pc0.toUSize
      let vmRes : Except Fault FastVm :=
        if hIdx == 0 then .ok vm
        else applyHintsAtPc streamNames hintLists hIdx.toNat vm
      match vmRes with
      | .error e => .error e
      | .ok vmReady =>
        let ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
             links, unconstrained, g, streamsCur,
             memCap, memUsed, maxAccess, maxBcCount, pcU, fpU, nextFree, cycles,
             nXor, nMul, nSet, nDeref, nJump, nKeccak⟩ := vmReady
        let needGU := maxU64 (pcU + 2) fpU
        let g := if needGU < g.len.toUInt64 then g else g.growCold needGU.toNat
        let pcIdx := pcU.toUSize
        let bcRead := getU32Fast bcCounts pcIdx
        let bcNext := bcRead + 1
        let bcNextU := bcNext.toUInt64
        let maxBcCount := if bcNextU > maxBcCount then bcNextU else maxBcCount
        let bcCounts := setU32Fast bcCounts pcIdx bcNext
        let vmStep : FastVm :=
          ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
           links, unconstrained, g, streamsCur,
           memCap, memUsed, maxAccess, maxBcCount, pcU, fpU, nextFree, cycles,
           nXor, nMul, nSet, nDeref, nJump, nKeccak⟩
        let opBase := (pcU <<< 4).toUSize
        let tag := getU64Fast opWords opBase
        let stepRes : Except Fault FastVm :=
          if tag == 0 then stepXorFast opWords opBase pcU fpU bcRead vmStep
          else if tag == 1 then stepMulFast opWords opBase pcU fpU bcRead vmStep
          else if tag == 2 then stepSetFast opWords opBase pcU fpU bcRead vmStep
          else if tag == 3 then stepDerefFast opWords opBase pcU fpU bcRead vmStep
          else if tag == 4 then stepJumpFast opWords opBase pcU fpU bcRead vmStep
          else stepKeccakFast opWords opBase pcU fpU bcRead vmStep
        match stepRes with
        | .error e => .error e
        | .ok vmNext =>
          executeFastLoop nProgU opWords hintAt hintLists streamNames fuel vmNext

def executeFastWith (fuel : Nat) (fprog : @& FastProg) (gInit : FastGPow)
    (frame : Nat) (publicInput : @& Array E) (streams : FastStreams) :
    Except Fault FastExec := do
  let nProg := fprog.size
  if nProg == 0 || (nProg &&& (nProg - 1)) != 0 then throw .badProgram
  if publicInput.size != 2 then throw .badProgram
  let n0 := max frame 2
  if n0 > maxCells then throw .outOfMemory
  let streamWords := estimateStreamWords streams
  let estMem := max n0 (max 131072 (nProg + frame + 5 * streamWords))
  let initMemCap := min maxCells estMem
  let seed := max (nProg + 2) (max initMemCap 262144)
  let g0 := gInit.grow seed
  let traceInitCap :=
    if streamWords >= 500000 then 300000
    else if nProg >= 65536 then 32768
    else 256
  let vm0 : FastVm := ⟨
    zeroBytesExact (8 * initMemCap),
    zeroBytesExact (8 * initMemCap),
    zeroBytesExact (8 * initMemCap),
    zeroBytesExact initMemCap,
    zeroBytesExact (4 * initMemCap),
    zeroBytesExact (4 * nProg),
    zeroBytesExact (24 * traceInitCap),
    zeroBytesExact (24 * traceInitCap),
    zeroBytesExact (16 * traceInitCap),
    zeroBytesExact (24 * traceInitCap),
    zeroBytesExact (24 * (traceInitCap / 4 + 16)),
    zeroBytesExact (116 * traceInitCap),
    #[],
    #[],
    g0,
    streams,
    initMemCap.toUInt64,
    n0.toUInt64,
    0,
    0,
    0,
    0,
    frame.toUInt64,
    0,
    0,
    0,
    0,
    0,
    0,
    0
  ⟩
  let vm1 ← vmPut vm0 0 (publicInput[0]?.getD Spec.Field.zero)
  let vm2 ← vmPut vm1 1 (publicInput[1]?.getD Spec.Field.zero)
  let vm ← executeFastLoop nProg.toUInt64 fprog.opWords fprog.hintAt fprog.hintLists fprog.streamNames fuel vm2
  let ⟨mc0, mc1, mc2, mState, mAccess, bcCounts, tXor, tMul, tSet, tDeref, tJump, tKeccak,
       _, unconstrained, g, _,
       memCap, memUsed, maxAccess, maxBcCount, _, _, _, cycles,
       nXor, nMul, nSet, nDeref, nJump, nKeccak⟩ := vm
  return {
    mc0 := mc0
    mc1 := mc1
    mc2 := mc2
    mState := mState
    mAccess := mAccess
    memCap := memCap.toNat
    memUsed := memUsed.toNat
    maxAccess := maxAccess.toNat
    maxBcCount := maxBcCount.toNat
    cycles := cycles.toNat
    unconstrained := unconstrained.size
    bcCounts := bcCounts
    tXor := tXor
    nXor := nXor.toNat
    tMul := tMul
    nMul := nMul.toNat
    tSet := tSet
    nSet := nSet.toNat
    tDeref := tDeref
    nDeref := nDeref.toNat
    tJump := tJump
    nJump := nJump.toNat
    tKeccak := tKeccak
    nKeccak := nKeccak.toNat
    g := g
  }

/-! ## Fast Streaming Memory Keccak256 (`hashUsedMemoryFast`) -/

def hashUsedMemoryFast (exec : @& FastExec) : ByteArray := Id.run do
  let used := exec.memUsed
  let mc0 := exec.mc0
  let mc1 := exec.mc1
  let mc2 := exec.mc2
  let nTasks := min 16 (max 1 ((used + 65535) / 65536))
  let tasks := (Array.range nTasks).map fun tid =>
    let lo := (tid * used) / nTasks
    let hi := ((tid + 1) * used) / nTasks
    Task.spawn fun _ => Id.run do
      let cnt := hi - lo
      let mut chunk := zeroBytesExact (24 * cnt)
      for step in [:cnt] do
        let addr := (lo + step).toUSize
        let wBase := (3 * step).toUSize
        chunk := setU64Fast chunk wBase (getU64Fast mc0 addr)
        chunk := setU64Fast chunk (wBase + 1) (getU64Fast mc1 addr)
        chunk := setU64Fast chunk (wBase + 2) (getU64Fast mc2 addr)
      return chunk
  let mut full := ByteArray.emptyWithCapacity (24 * used)
  for tk in tasks do
    full := full ++ tk.get
  return keccak256FastStream full

/-! ## 16-Task Parallel Witness Generation (`buildWitnessPar`) -/

structure FastWitness where
  logMem : Nat
  logBytecode : Nat
  cells : Nat
  rows : Array Nat
  layout : Model.Layout.PublicLayout
  lanesBytes : Array ByteArray

/-- Montgomery batch inversion over `GF(2^64)` for `JUMP` condition words:
1 `nativeInv` + `3 * nJump` `nativeMul`s. -/
def jumpInversesAndBits (nJump : Nat) (tJump opWords mc0 : @& ByteArray) :
    ByteArray × ByteArray := Id.run do
  if nJump == 0 then
    return (ByteArray.empty, ByteArray.empty)
  let mut prefs := zeroBytesExact (8 * nJump)
  let mut bits := zeroBytesExact (8 * nJump)
  let mut prod : UInt64 := 1
  for i in [:nJump] do
    let rBase := (6 * i).toUSize
    let pc := (getU32Fast tJump rBase).toNat
    let fp := (getU32Fast tJump (rBase + 1)).toNat
    let oc := (getU64Fast opWords (16 * pc + 1).toUSize).toNat
    let cond := getU64Fast mc0 (fp + oc).toUSize
    prefs := setU64Fast prefs i.toUSize prod
    if cond != 0 then
      prod := Model.Field.nativeMul prod cond
      bits := setU64Fast bits i.toUSize 1
  let mut invAcc : UInt64 := Model.Field.nativeInv prod
  let mut invs := zeroBytesExact (8 * nJump)
  for step in [:nJump] do
    let idx := nJump - 1 - step
    let rBase := (6 * idx).toUSize
    let pc := (getU32Fast tJump rBase).toNat
    let fp := (getU32Fast tJump (rBase + 1)).toNat
    let oc := (getU64Fast opWords (16 * pc + 1).toUSize).toNat
    let cond := getU64Fast mc0 (fp + oc).toUSize
    if cond != 0 then
      let witness := Model.Field.nativeMul invAcc (getU64Fast prefs idx.toUSize)
      invs := setU64Fast invs idx.toUSize witness
      invAcc := Model.Field.nativeMul invAcc cond
  return (invs, bits)

@[inline] def fillBinaryColsFast (nRows height : Nat) (tRows opWords mc0 mc1 mc2 : @& ByteArray)
    (g : @& FastGPow) : Array ByteArray := Id.run do
  let mut c00 := zeroBytesExact (8 * height)
  let mut c01 := zeroBytesExact (8 * height)
  let mut c02 := zeroBytesExact (8 * height)
  let mut c03 := zeroBytesExact (8 * height)
  let mut c04 := zeroBytesExact (8 * height)
  let mut c05 := zeroBytesExact (8 * height)
  let mut c06 := zeroBytesExact (8 * height)
  let mut c07 := zeroBytesExact (8 * height)
  let mut c08 := zeroBytesExact (8 * height)
  let mut c09 := zeroBytesExact (8 * height)
  let mut c10 := zeroBytesExact (8 * height)
  let mut c11 := zeroBytesExact (8 * height)
  let mut c12 := zeroBytesExact (8 * height)
  let mut c13 := zeroBytesExact (8 * height)
  let mut c14 := zeroBytesExact (8 * height)
  for r in [:nRows] do
    let rIdx := r.toUSize
    let rBase := (6 * r).toUSize
    let pc := (getU32Fast tRows rBase).toNat
    let fp := (getU32Fast tRows (rBase + 1)).toNat
    let ra := (getU32Fast tRows (rBase + 2)).toNat
    let rb := (getU32Fast tRows (rBase + 3)).toNat
    let rc := (getU32Fast tRows (rBase + 4)).toNat
    let bc := (getU32Fast tRows (rBase + 5)).toNat
    let opBase := (16 * pc).toUSize
    let a := (getU64Fast opWords (opBase + 1)).toNat
    let b := (getU64Fast opWords (opBase + 2)).toNat
    let c := (getU64Fast opWords (opBase + 3)).toNat
    let aa := (fp + a).toUSize
    let ab := (fp + b).toUSize
    c00 := setU64Fast c00 rIdx (g.powAt pc)
    c01 := setU64Fast c01 rIdx (g.powAt fp)
    c02 := setU64Fast c02 rIdx (g.powAt a)
    c03 := setU64Fast c03 rIdx (g.powAt b)
    c04 := setU64Fast c04 rIdx (g.powAt c)
    let va0 := getU64Fast mc0 aa; if va0 != 0 then c05 := setU64Fast c05 rIdx va0
    let va1 := getU64Fast mc1 aa; if va1 != 0 then c06 := setU64Fast c06 rIdx va1
    let va2 := getU64Fast mc2 aa; if va2 != 0 then c07 := setU64Fast c07 rIdx va2
    let vb0 := getU64Fast mc0 ab; if vb0 != 0 then c08 := setU64Fast c08 rIdx vb0
    let vb1 := getU64Fast mc1 ab; if vb1 != 0 then c09 := setU64Fast c09 rIdx vb1
    let vb2 := getU64Fast mc2 ab; if vb2 != 0 then c10 := setU64Fast c10 rIdx vb2
    c11 := setU64Fast c11 rIdx (g.powAt ra)
    c12 := setU64Fast c12 rIdx (g.powAt rb)
    c13 := setU64Fast c13 rIdx (g.powAt rc)
    c14 := setU64Fast c14 rIdx (g.powAt bc)
  return #[c00, c01, c02, c03, c04, c05, c06, c07, c08, c09, c10, c11, c12, c13, c14]

@[inline] def fillSetColsFast (nRows height : Nat) (tSet opWords : @& ByteArray)
    (g : @& FastGPow) : Array ByteArray := Id.run do
  let mut c00 := zeroBytesExact (8 * height)
  let mut c01 := zeroBytesExact (8 * height)
  let mut c02 := zeroBytesExact (8 * height)
  let mut c03 := zeroBytesExact (8 * height)
  let mut c04 := zeroBytesExact (8 * height)
  let mut c05 := zeroBytesExact (8 * height)
  let mut c06 := zeroBytesExact (8 * height)
  let mut c07 := zeroBytesExact (8 * height)
  for r in [:nRows] do
    let rIdx := r.toUSize
    let rBase := (4 * r).toUSize
    let pc := (getU32Fast tSet rBase).toNat
    let fp := (getU32Fast tSet (rBase + 1)).toNat
    let rv := (getU32Fast tSet (rBase + 2)).toNat
    let bc := (getU32Fast tSet (rBase + 3)).toNat
    let opBase := (16 * pc).toUSize
    let off := (getU64Fast opWords (opBase + 1)).toNat
    c00 := setU64Fast c00 rIdx (g.powAt pc)
    c01 := setU64Fast c01 rIdx (g.powAt fp)
    c02 := setU64Fast c02 rIdx (g.powAt off)
    let v0 := getU64Fast opWords (opBase + 2); if v0 != 0 then c03 := setU64Fast c03 rIdx v0
    let v1 := getU64Fast opWords (opBase + 3); if v1 != 0 then c04 := setU64Fast c04 rIdx v1
    let v2 := getU64Fast opWords (opBase + 4); if v2 != 0 then c05 := setU64Fast c05 rIdx v2
    c06 := setU64Fast c06 rIdx (g.powAt rv)
    c07 := setU64Fast c07 rIdx (g.powAt bc)
  return #[c00, c01, c02, c03, c04, c05, c06, c07]

@[inline] def fillDerefColsFast (nRows height : Nat) (tDeref opWords mc0 mc1 mc2 : @& ByteArray)
    (g : @& FastGPow) : Array ByteArray := Id.run do
  let mut c00 := zeroBytesExact (8 * height)
  let mut c01 := zeroBytesExact (8 * height)
  let mut c02 := zeroBytesExact (8 * height)
  let mut c03 := zeroBytesExact (8 * height)
  let mut c04 := zeroBytesExact (8 * height)
  let mut c05 := zeroBytesExact (8 * height)
  let mut c06 := zeroBytesExact (8 * height)
  let mut c07 := zeroBytesExact (8 * height)
  let mut c08 := zeroBytesExact (8 * height)
  let mut c09 := zeroBytesExact (8 * height)
  let mut c10 := zeroBytesExact (8 * height)
  let mut c11 := zeroBytesExact (8 * height)
  let mut c12 := zeroBytesExact (8 * height)
  let mut c13 := zeroBytesExact (8 * height)
  let mut c14 := zeroBytesExact (8 * height)
  for r in [:nRows] do
    let rIdx := r.toUSize
    let rBase := (6 * r).toUSize
    let pc := (getU32Fast tDeref rBase).toNat
    let fp := (getU32Fast tDeref (rBase + 1)).toNat
    let r1 := (getU32Fast tDeref (rBase + 2)).toNat
    let r2 := (getU32Fast tDeref (rBase + 3)).toNat
    let r3 := (getU32Fast tDeref (rBase + 4)).toNat
    let bc := (getU32Fast tDeref (rBase + 5)).toNat
    let opBase := (16 * pc).toUSize
    let o1 := (getU64Fast opWords (opBase + 1)).toNat
    let o2 := (getU64Fast opWords (opBase + 2)).toNat
    let o3 := (getU64Fast opWords (opBase + 3)).toNat
    let mTag := getU64Fast opWords (opBase + 4)
    let a1 := (fp + o1).toUSize
    let a3 := (fp + o3).toUSize
    c00 := setU64Fast c00 rIdx (g.powAt pc)
    c01 := setU64Fast c01 rIdx (g.powAt fp)
    c02 := setU64Fast c02 rIdx (g.powAt o1)
    c03 := setU64Fast c03 rIdx (g.powAt o2)
    c04 := setU64Fast c04 rIdx (g.powAt o3)
    if mTag == 1 then c05 := setU64Fast c05 rIdx 1
    if mTag == 2 then c06 := setU64Fast c06 rIdx 1
    c07 := setU64Fast c07 rIdx (getU64Fast mc0 a1)
    let w30 := getU64Fast mc0 a3; if w30 != 0 then c08 := setU64Fast c08 rIdx w30
    let w31 := getU64Fast mc1 a3; if w31 != 0 then c09 := setU64Fast c09 rIdx w31
    let w32 := getU64Fast mc2 a3; if w32 != 0 then c10 := setU64Fast c10 rIdx w32
    c11 := setU64Fast c11 rIdx (g.powAt r1)
    c12 := setU64Fast c12 rIdx (g.powAt r2)
    c13 := setU64Fast c13 rIdx (g.powAt r3)
    c14 := setU64Fast c14 rIdx (g.powAt bc)
  return #[c00, c01, c02, c03, c04, c05, c06, c07, c08, c09, c10, c11, c12, c13, c14]

@[inline] def fillJumpColsFast (nRows height : Nat) (tJump opWords mc0 : @& ByteArray)
    (g : @& FastGPow) : Array ByteArray := Id.run do
  let (invs, bits) := jumpInversesAndBits nRows tJump opWords mc0
  let mut c00 := zeroBytesExact (8 * height)
  let mut c01 := zeroBytesExact (8 * height)
  let mut c02 := zeroBytesExact (8 * height)
  let mut c03 := zeroBytesExact (8 * height)
  let mut c04 := zeroBytesExact (8 * height)
  let mut c05 := zeroBytesExact (8 * height)
  let mut c06 := zeroBytesExact (8 * height)
  let mut c07 := zeroBytesExact (8 * height)
  let mut c08 := zeroBytesExact (8 * height)
  let mut c09 := zeroBytesExact (8 * height)
  let mut c10 := zeroBytesExact (8 * height)
  let mut c11 := zeroBytesExact (8 * height)
  let mut c12 := zeroBytesExact (8 * height)
  let mut c13 := zeroBytesExact (8 * height)
  for r in [:nRows] do
    let rIdx := r.toUSize
    let rBase := (6 * r).toUSize
    let pc := (getU32Fast tJump rBase).toNat
    let fp := (getU32Fast tJump (rBase + 1)).toNat
    let rc := (getU32Fast tJump (rBase + 2)).toNat
    let rd := (getU32Fast tJump (rBase + 3)).toNat
    let rf := (getU32Fast tJump (rBase + 4)).toNat
    let bc := (getU32Fast tJump (rBase + 5)).toNat
    let opBase := (16 * pc).toUSize
    let oc := (getU64Fast opWords (opBase + 1)).toNat
    let od := (getU64Fast opWords (opBase + 2)).toNat
    let of_ := (getU64Fast opWords (opBase + 3)).toNat
    c00 := setU64Fast c00 rIdx (g.powAt pc)
    c01 := setU64Fast c01 rIdx (g.powAt fp)
    c02 := setU64Fast c02 rIdx (g.powAt oc)
    c03 := setU64Fast c03 rIdx (g.powAt od)
    c04 := setU64Fast c04 rIdx (g.powAt of_)
    c05 := setU64Fast c05 rIdx (getU64Fast mc0 (fp + oc).toUSize)
    c06 := setU64Fast c06 rIdx (getU64Fast mc0 (fp + od).toUSize)
    c07 := setU64Fast c07 rIdx (getU64Fast mc0 (fp + of_).toUSize)
    c08 := setU64Fast c08 rIdx (g.powAt rc)
    c09 := setU64Fast c09 rIdx (g.powAt rd)
    c10 := setU64Fast c10 rIdx (g.powAt rf)
    c11 := setU64Fast c11 rIdx (g.powAt bc)
    let iv := getU64Fast invs rIdx; if iv != 0 then c12 := setU64Fast c12 rIdx iv
    let bt := getU64Fast bits rIdx; if bt != 0 then c13 := setU64Fast c13 rIdx bt
  return #[c00, c01, c02, c03, c04, c05, c06, c07, c08, c09, c10, c11, c12, c13]

set_option maxHeartbeats 1600000 in
/-- Fill a range `[lo..hi)` of `KECCAK` witness columns (40 columns: `13` head + `26` counts + `1` bcCount,
ordered as `14` spares `0..13` followed by `26` standalone counts `14..39`) AND `50` `qKeccak` sub-columns
(`25` input state lanes + `25` 12-round mid state lanes). -/
def fillKeccakChunkFast (lo hi : Nat) (tKeccak opWords mc0 mc1 : @& ByteArray)
    (g : @& FastGPow) (zeroMidArr : @& Array UInt64) : Array ByteArray := Id.run do
  let cnt := hi - lo
  let mut sp00 := zeroBytesExact (8 * cnt)
  let mut sp01 := zeroBytesExact (8 * cnt)
  let mut sp02 := zeroBytesExact (8 * cnt)
  let mut sp03 := zeroBytesExact (8 * cnt)
  let mut sp04 := zeroBytesExact (8 * cnt)
  let mut sp05 := zeroBytesExact (8 * cnt)
  let mut sp06 := zeroBytesExact (8 * cnt)
  let mut sp07 := zeroBytesExact (8 * cnt)
  let mut sp08 := zeroBytesExact (8 * cnt)
  let mut sp09 := zeroBytesExact (8 * cnt)
  let mut sp10 := zeroBytesExact (8 * cnt)
  let mut sp11 := zeroBytesExact (8 * cnt)
  let mut sp12 := zeroBytesExact (8 * cnt)
  let mut sp13 := zeroBytesExact (8 * cnt)
  let mut kc01 := zeroBytesExact (8 * cnt)
  let mut kc02 := zeroBytesExact (8 * cnt)
  let mut kc03 := zeroBytesExact (8 * cnt)
  let mut kc04 := zeroBytesExact (8 * cnt)
  let mut kc05 := zeroBytesExact (8 * cnt)
  let mut kc06 := zeroBytesExact (8 * cnt)
  let mut kc07 := zeroBytesExact (8 * cnt)
  let mut kc08 := zeroBytesExact (8 * cnt)
  let mut kc09 := zeroBytesExact (8 * cnt)
  let mut kc10 := zeroBytesExact (8 * cnt)
  let mut kc11 := zeroBytesExact (8 * cnt)
  let mut kc12 := zeroBytesExact (8 * cnt)
  let mut kc13 := zeroBytesExact (8 * cnt)
  let mut kc14 := zeroBytesExact (8 * cnt)
  let mut kc15 := zeroBytesExact (8 * cnt)
  let mut kc16 := zeroBytesExact (8 * cnt)
  let mut kc17 := zeroBytesExact (8 * cnt)
  let mut kc18 := zeroBytesExact (8 * cnt)
  let mut kc19 := zeroBytesExact (8 * cnt)
  let mut kc20 := zeroBytesExact (8 * cnt)
  let mut kc21 := zeroBytesExact (8 * cnt)
  let mut kc22 := zeroBytesExact (8 * cnt)
  let mut kc23 := zeroBytesExact (8 * cnt)
  let mut kc24 := zeroBytesExact (8 * cnt)
  let mut kc25 := zeroBytesExact (8 * cnt)
  let mut kcBc := zeroBytesExact (8 * cnt)
  let mut q00 := zeroBytesExact (8 * cnt)
  let mut q01 := zeroBytesExact (8 * cnt)
  let mut q02 := zeroBytesExact (8 * cnt)
  let mut q03 := zeroBytesExact (8 * cnt)
  let mut q04 := zeroBytesExact (8 * cnt)
  let mut q05 := zeroBytesExact (8 * cnt)
  let mut q06 := zeroBytesExact (8 * cnt)
  let mut q07 := zeroBytesExact (8 * cnt)
  let mut q08 := zeroBytesExact (8 * cnt)
  let mut q09 := zeroBytesExact (8 * cnt)
  let mut q10 := zeroBytesExact (8 * cnt)
  let mut q11 := zeroBytesExact (8 * cnt)
  let mut q12 := zeroBytesExact (8 * cnt)
  let mut q13 := zeroBytesExact (8 * cnt)
  let mut q14 := zeroBytesExact (8 * cnt)
  let mut q15 := zeroBytesExact (8 * cnt)
  let mut q16 := zeroBytesExact (8 * cnt)
  let mut q17 := zeroBytesExact (8 * cnt)
  let mut q18 := zeroBytesExact (8 * cnt)
  let mut q19 := zeroBytesExact (8 * cnt)
  let mut q20 := zeroBytesExact (8 * cnt)
  let mut q21 := zeroBytesExact (8 * cnt)
  let mut q22 := zeroBytesExact (8 * cnt)
  let mut q23 := zeroBytesExact (8 * cnt)
  let mut q24 := zeroBytesExact (8 * cnt)
  let mut q25 := zeroBytesExact (8 * cnt)
  let mut q26 := zeroBytesExact (8 * cnt)
  let mut q27 := zeroBytesExact (8 * cnt)
  let mut q28 := zeroBytesExact (8 * cnt)
  let mut q29 := zeroBytesExact (8 * cnt)
  let mut q30 := zeroBytesExact (8 * cnt)
  let mut q31 := zeroBytesExact (8 * cnt)
  let mut q32 := zeroBytesExact (8 * cnt)
  let mut q33 := zeroBytesExact (8 * cnt)
  let mut q34 := zeroBytesExact (8 * cnt)
  let mut q35 := zeroBytesExact (8 * cnt)
  let mut q36 := zeroBytesExact (8 * cnt)
  let mut q37 := zeroBytesExact (8 * cnt)
  let mut q38 := zeroBytesExact (8 * cnt)
  let mut q39 := zeroBytesExact (8 * cnt)
  let mut q40 := zeroBytesExact (8 * cnt)
  let mut q41 := zeroBytesExact (8 * cnt)
  let mut q42 := zeroBytesExact (8 * cnt)
  let mut q43 := zeroBytesExact (8 * cnt)
  let mut q44 := zeroBytesExact (8 * cnt)
  let mut q45 := zeroBytesExact (8 * cnt)
  let mut q46 := zeroBytesExact (8 * cnt)
  let mut q47 := zeroBytesExact (8 * cnt)
  let mut q48 := zeroBytesExact (8 * cnt)
  let mut q49 := zeroBytesExact (8 * cnt)
  for s in [:cnt] do
    let row := lo + s
    let sIdx := s.toUSize
    let kBase := (29 * row).toUSize
    let pc := (getU32Fast tKeccak kBase).toNat
    let fp := (getU32Fast tKeccak (kBase + 1)).toNat
    let opBase := (16 * pc).toUSize
    let m0 := (getU64Fast opWords (opBase + 1)).toNat
    let m1 := (getU64Fast opWords (opBase + 2)).toNat
    let m2 := (getU64Fast opWords (opBase + 3)).toNat
    let m3 := (getU64Fast opWords (opBase + 4)).toNat
    let tail := (getU64Fast opWords (opBase + 5)).toNat
    let b8 := (getU64Fast opWords (opBase + 6)).toNat
    let cap := (getU64Fast opWords (opBase + 7)).toNat
    let out := (getU64Fast opWords (opBase + 8)).toNat
    let inOddU := getU64Fast opWords (opBase + 9)
    let outOddU := getU64Fast opWords (opBase + 10)
    let inOdd := inOddU != 0
    let missingLimb : UInt64 :=
      if inOdd then getU64Fast mc0 (fp + m0).toUSize
      else getU64Fast mc1 (fp + b8).toUSize
    sp00 := setU64Fast sp00 sIdx (g.powAt pc)
    sp01 := setU64Fast sp01 sIdx (g.powAt fp)
    sp02 := setU64Fast sp02 sIdx (g.powAt m0)
    sp03 := setU64Fast sp03 sIdx (g.powAt m1)
    sp04 := setU64Fast sp04 sIdx (g.powAt m2)
    sp05 := setU64Fast sp05 sIdx (g.powAt m3)
    sp06 := setU64Fast sp06 sIdx (g.powAt tail)
    sp07 := setU64Fast sp07 sIdx (g.powAt b8)
    sp08 := setU64Fast sp08 sIdx (g.powAt cap)
    sp09 := setU64Fast sp09 sIdx (g.powAt out)
    sp10 := setU64Fast sp10 sIdx inOddU
    sp11 := setU64Fast sp11 sIdx outOddU
    sp12 := setU64Fast sp12 sIdx missingLimb
    sp13 := setU64Fast sp13 sIdx (g.powAt (getU32Fast tKeccak (kBase + 2)).toNat)
    kc01 := setU64Fast kc01 sIdx (g.powAt (getU32Fast tKeccak (kBase + 3)).toNat)
    kc02 := setU64Fast kc02 sIdx (g.powAt (getU32Fast tKeccak (kBase + 4)).toNat)
    kc03 := setU64Fast kc03 sIdx (g.powAt (getU32Fast tKeccak (kBase + 5)).toNat)
    kc04 := setU64Fast kc04 sIdx (g.powAt (getU32Fast tKeccak (kBase + 6)).toNat)
    kc05 := setU64Fast kc05 sIdx (g.powAt (getU32Fast tKeccak (kBase + 7)).toNat)
    kc06 := setU64Fast kc06 sIdx (g.powAt (getU32Fast tKeccak (kBase + 8)).toNat)
    kc07 := setU64Fast kc07 sIdx (g.powAt (getU32Fast tKeccak (kBase + 9)).toNat)
    kc08 := setU64Fast kc08 sIdx (g.powAt (getU32Fast tKeccak (kBase + 10)).toNat)
    kc09 := setU64Fast kc09 sIdx (g.powAt (getU32Fast tKeccak (kBase + 11)).toNat)
    kc10 := setU64Fast kc10 sIdx (g.powAt (getU32Fast tKeccak (kBase + 12)).toNat)
    kc11 := setU64Fast kc11 sIdx (g.powAt (getU32Fast tKeccak (kBase + 13)).toNat)
    kc12 := setU64Fast kc12 sIdx (g.powAt (getU32Fast tKeccak (kBase + 14)).toNat)
    kc13 := setU64Fast kc13 sIdx (g.powAt (getU32Fast tKeccak (kBase + 15)).toNat)
    kc14 := setU64Fast kc14 sIdx (g.powAt (getU32Fast tKeccak (kBase + 16)).toNat)
    kc15 := setU64Fast kc15 sIdx (g.powAt (getU32Fast tKeccak (kBase + 17)).toNat)
    kc16 := setU64Fast kc16 sIdx (g.powAt (getU32Fast tKeccak (kBase + 18)).toNat)
    kc17 := setU64Fast kc17 sIdx (g.powAt (getU32Fast tKeccak (kBase + 19)).toNat)
    kc18 := setU64Fast kc18 sIdx (g.powAt (getU32Fast tKeccak (kBase + 20)).toNat)
    kc19 := setU64Fast kc19 sIdx (g.powAt (getU32Fast tKeccak (kBase + 21)).toNat)
    kc20 := setU64Fast kc20 sIdx (g.powAt (getU32Fast tKeccak (kBase + 22)).toNat)
    kc21 := setU64Fast kc21 sIdx (g.powAt (getU32Fast tKeccak (kBase + 23)).toNat)
    kc22 := setU64Fast kc22 sIdx (g.powAt (getU32Fast tKeccak (kBase + 24)).toNat)
    kc23 := setU64Fast kc23 sIdx (g.powAt (getU32Fast tKeccak (kBase + 25)).toNat)
    kc24 := setU64Fast kc24 sIdx (g.powAt (getU32Fast tKeccak (kBase + 26)).toNat)
    kc25 := setU64Fast kc25 sIdx (g.powAt (getU32Fast tKeccak (kBase + 27)).toNat)
    kcBc := setU64Fast kcBc sIdx (g.powAt (getU32Fast tKeccak (kBase + 28)).toNat)
    let a00 := (fp + m0).toUSize
    let a01 := (fp + m1).toUSize
    let a02 := (fp + m2).toUSize
    let a03 := (fp + m3).toUSize
    let a04 := (fp + tail).toUSize
    let a05 := (fp + tail + 1).toUSize
    let a06 := (fp + tail + 2).toUSize
    let a07 := (fp + tail + 3).toUSize
    let a08 := (fp + b8).toUSize
    let a09 := (fp + cap).toUSize
    let a10 := (fp + cap + 1).toUSize
    let a11 := (fp + cap + 2).toUSize
    let a12 := (fp + cap + 3).toUSize
    let inSt : State25 :=
      if inOdd then
        ⟨getU64Fast mc1 a00, getU64Fast mc0 a01, getU64Fast mc1 a01, getU64Fast mc0 a02, getU64Fast mc1 a02,
         getU64Fast mc0 a03, getU64Fast mc1 a03, getU64Fast mc0 a04, getU64Fast mc1 a04, getU64Fast mc0 a05,
         getU64Fast mc1 a05, getU64Fast mc0 a06, getU64Fast mc1 a06, getU64Fast mc0 a07, getU64Fast mc1 a07,
         getU64Fast mc0 a08, getU64Fast mc1 a08, getU64Fast mc0 a09, getU64Fast mc1 a09, getU64Fast mc0 a10,
         getU64Fast mc1 a10, getU64Fast mc0 a11, getU64Fast mc1 a11, getU64Fast mc0 a12, getU64Fast mc1 a12⟩
      else
        ⟨getU64Fast mc0 a00, getU64Fast mc1 a00, getU64Fast mc0 a01, getU64Fast mc1 a01, getU64Fast mc0 a02,
         getU64Fast mc1 a02, getU64Fast mc0 a03, getU64Fast mc1 a03, getU64Fast mc0 a04, getU64Fast mc1 a04,
         getU64Fast mc0 a05, getU64Fast mc1 a05, getU64Fast mc0 a06, getU64Fast mc1 a06, getU64Fast mc0 a07,
         getU64Fast mc1 a07, getU64Fast mc0 a08, getU64Fast mc0 a09, getU64Fast mc1 a09, getU64Fast mc0 a10,
         getU64Fast mc1 a10, getU64Fast mc0 a11, getU64Fast mc1 a11, getU64Fast mc0 a12, getU64Fast mc1 a12⟩
    let midSt := rounds12Fast inSt
    if inSt.a00 != 0 then q00 := setU64Fast q00 sIdx inSt.a00
    if inSt.a01 != 0 then q01 := setU64Fast q01 sIdx inSt.a01
    if inSt.a02 != 0 then q02 := setU64Fast q02 sIdx inSt.a02
    if inSt.a03 != 0 then q03 := setU64Fast q03 sIdx inSt.a03
    if inSt.a04 != 0 then q04 := setU64Fast q04 sIdx inSt.a04
    if inSt.a05 != 0 then q05 := setU64Fast q05 sIdx inSt.a05
    if inSt.a06 != 0 then q06 := setU64Fast q06 sIdx inSt.a06
    if inSt.a07 != 0 then q07 := setU64Fast q07 sIdx inSt.a07
    if inSt.a08 != 0 then q08 := setU64Fast q08 sIdx inSt.a08
    if inSt.a09 != 0 then q09 := setU64Fast q09 sIdx inSt.a09
    if inSt.a10 != 0 then q10 := setU64Fast q10 sIdx inSt.a10
    if inSt.a11 != 0 then q11 := setU64Fast q11 sIdx inSt.a11
    if inSt.a12 != 0 then q12 := setU64Fast q12 sIdx inSt.a12
    if inSt.a13 != 0 then q13 := setU64Fast q13 sIdx inSt.a13
    if inSt.a14 != 0 then q14 := setU64Fast q14 sIdx inSt.a14
    if inSt.a15 != 0 then q15 := setU64Fast q15 sIdx inSt.a15
    if inSt.a16 != 0 then q16 := setU64Fast q16 sIdx inSt.a16
    if inSt.a17 != 0 then q17 := setU64Fast q17 sIdx inSt.a17
    if inSt.a18 != 0 then q18 := setU64Fast q18 sIdx inSt.a18
    if inSt.a19 != 0 then q19 := setU64Fast q19 sIdx inSt.a19
    if inSt.a20 != 0 then q20 := setU64Fast q20 sIdx inSt.a20
    if inSt.a21 != 0 then q21 := setU64Fast q21 sIdx inSt.a21
    if inSt.a22 != 0 then q22 := setU64Fast q22 sIdx inSt.a22
    if inSt.a23 != 0 then q23 := setU64Fast q23 sIdx inSt.a23
    if inSt.a24 != 0 then q24 := setU64Fast q24 sIdx inSt.a24
    if midSt.a00 != 0 then q25 := setU64Fast q25 sIdx midSt.a00
    if midSt.a01 != 0 then q26 := setU64Fast q26 sIdx midSt.a01
    if midSt.a02 != 0 then q27 := setU64Fast q27 sIdx midSt.a02
    if midSt.a03 != 0 then q28 := setU64Fast q28 sIdx midSt.a03
    if midSt.a04 != 0 then q29 := setU64Fast q29 sIdx midSt.a04
    if midSt.a05 != 0 then q30 := setU64Fast q30 sIdx midSt.a05
    if midSt.a06 != 0 then q31 := setU64Fast q31 sIdx midSt.a06
    if midSt.a07 != 0 then q32 := setU64Fast q32 sIdx midSt.a07
    if midSt.a08 != 0 then q33 := setU64Fast q33 sIdx midSt.a08
    if midSt.a09 != 0 then q34 := setU64Fast q34 sIdx midSt.a09
    if midSt.a10 != 0 then q35 := setU64Fast q35 sIdx midSt.a10
    if midSt.a11 != 0 then q36 := setU64Fast q36 sIdx midSt.a11
    if midSt.a12 != 0 then q37 := setU64Fast q37 sIdx midSt.a12
    if midSt.a13 != 0 then q38 := setU64Fast q38 sIdx midSt.a13
    if midSt.a14 != 0 then q39 := setU64Fast q39 sIdx midSt.a14
    if midSt.a15 != 0 then q40 := setU64Fast q40 sIdx midSt.a15
    if midSt.a16 != 0 then q41 := setU64Fast q41 sIdx midSt.a16
    if midSt.a17 != 0 then q42 := setU64Fast q42 sIdx midSt.a17
    if midSt.a18 != 0 then q43 := setU64Fast q43 sIdx midSt.a18
    if midSt.a19 != 0 then q44 := setU64Fast q44 sIdx midSt.a19
    if midSt.a20 != 0 then q45 := setU64Fast q45 sIdx midSt.a20
    if midSt.a21 != 0 then q46 := setU64Fast q46 sIdx midSt.a21
    if midSt.a22 != 0 then q47 := setU64Fast q47 sIdx midSt.a22
    if midSt.a23 != 0 then q48 := setU64Fast q48 sIdx midSt.a23
    if midSt.a24 != 0 then q49 := setU64Fast q49 sIdx midSt.a24
  return #[q00, q01, q02, q03, q04, q05, q06, q07, q08, q09,
    q10, q11, q12, q13, q14, q15, q16, q17, q18, q19,
    q20, q21, q22, q23, q24, q25, q26, q27, q28, q29,
    q30, q31, q32, q33, q34, q35, q36, q37, q38, q39,
    q40, q41, q42, q43, q44, q45, q46, q47, q48, q49,
    sp00, sp01, sp02, sp03, sp04, sp05, sp06, sp07, sp08, sp09, sp10, sp11, sp12, sp13,
    kc01, kc02, kc03, kc04, kc05, kc06, kc07, kc08, kc09, kc10, kc11, kc12, kc13,
    kc14, kc15, kc16, kc17, kc18, kc19, kc20, kc21, kc22, kc23, kc24, kc25, kcBc]

@[inline] def fillMemColFast (colId cells used : Nat) (mc0 mc1 mc2 mAccess : @& ByteArray)
    (g : @& FastGPow) : ByteArray := Id.run do
  let copyUsed := min cells used
  if colId == 0 then
    if copyUsed == 0 then return zeroBytesExact (8 * cells)
    else return mc0.copySlice 0 (zeroBytesExact (8 * cells)) 0 (8 * copyUsed) true
  else if colId == 1 then
    if copyUsed == 0 then return zeroBytesExact (8 * cells)
    else return mc1.copySlice 0 (zeroBytesExact (8 * cells)) 0 (8 * copyUsed) true
  else if colId == 2 then
    if copyUsed == 0 then return zeroBytesExact (8 * cells)
    else return mc2.copySlice 0 (zeroBytesExact (8 * cells)) 0 (8 * copyUsed) true
  else
    let nTasks := min 16 (max 1 ((cells + 65535) / 65536))
    let tasks := (Array.range nTasks).map fun tid =>
      let lo := (tid * cells) / nTasks
      let hi := ((tid + 1) * cells) / nTasks
      Task.spawn fun _ => Id.run do
        let cnt := hi - lo
        let mut chunk := zeroBytesExact (8 * cnt)
        let gOne := g.powAt 0
        for step in [:cnt] do
          let addr := lo + step
          let v : UInt64 :=
            if addr < copyUsed then
              let acc := (getU32Fast mAccess addr.toUSize).toNat
              if acc == 0 then gOne else g.powAt acc
            else gOne
          chunk := setU64Fast chunk step.toUSize v
        return chunk
    let mut out := ByteArray.emptyWithCapacity (8 * cells)
    for tk in tasks do
      out := out ++ tk.get
    return out

@[inline] def fillBytecodeFinalFast (nProg : Nat) (bcCounts : @& ByteArray)
    (g : @& FastGPow) : ByteArray := Id.run do
  let mut out := zeroBytesExact (8 * nProg)
  let gOne := g.powAt 0
  for pc in [:nProg] do
    let cnt := (getU32Fast bcCounts pc.toUSize).toNat
    let v := if cnt == 0 then gOne else g.powAt cnt
    out := setU64Fast out pc.toUSize v
  return out

/-- Copy column `ByteArray` `colBuf` (`8 * len` bytes) into stacked lanes (`lanesBytes`),
where lane `k` stores words `[k * rows .. (k + 1) * rows)`. -/
def scatterPlacementToLanes (lanesBytes : Array ByteArray) (rows startWord lenWords : Nat)
    (colBuf : @& ByteArray) : Array ByteArray := Id.run do
  if lenWords == 0 then return lanesBytes
  let mut lanes := lanesBytes
  let mut rem := lenWords
  let mut srcWord := 0
  let mut curWord := startWord
  let maxIters := lanes.size + 2
  for _ in [:maxIters] do
    if rem == 0 then break
    let laneIdx := curWord / rows
    let laneOff := curWord % rows
    let take := min rem (rows - laneOff)
    if laneIdx < lanes.size then
      let dst := lanes[laneIdx]?.getD ByteArray.empty
      let dst' := colBuf.copySlice (8 * srcWord) dst (8 * laneOff) (8 * take) true
      lanes := lanes.setIfInBounds laneIdx dst'
    srcWord := srcWord + take
    curWord := curWord + take
    rem := rem - take
  return lanes

/-- Copy global witness words `[a, b)` of a column buffer whose column starts at
global word `colStart` into the lane buffer for lane starting at global word `laneStart`. -/
def copyColSliceIntoLane (lane : ByteArray) (laneStart a b colStart : Nat)
    (buf : @& ByteArray) : ByteArray :=
  let n := b - a
  if n == 0 then lane
  else buf.copySlice (8 * (a - colStart)) lane (8 * (a - laneStart)) (8 * n) true

/-- Copy the slice of a placed column overlapping `[laneStart, laneEnd)` into `lane`.
The column occupies global words `[place.index, place.index + span)`; only the first
`valid` words hold real data (`buf`), the rest stays zero. -/
def copyPlacedColIntoLane (lane : ByteArray) (laneStart laneEnd : Nat) (place : Placement)
    (buf : @& ByteArray) (span valid : Nat) : ByteArray :=
  let idx := place.index
  let a := max idx laneStart
  let b := min (idx + min span valid) laneEnd
  copyColSliceIntoLane lane laneStart a b idx buf

/-- Fill global witness words `[a, b)` of the `memFinal` column (base global word `colStart`)
directly with `g.powAt access` values computed from `mAccess`. -/
def fillMemFinalLane (lane : ByteArray) (laneStart a b colStart memUsed : Nat)
    (mAccess : @& ByteArray) (g : @& FastGPow) : ByteArray := Id.run do
  let mut l := lane
  let gOne := g.powAt 0
  for w in [a:b] do
    let colW := w - colStart
    let v : UInt64 :=
      if colW < memUsed then
        let acc := (getU32Fast mAccess colW.toUSize).toNat
        if acc == 0 then gOne else g.powAt acc
      else gOne
    l := setU64Fast l (w - laneStart).toUSize v
  return l

set_option maxHeartbeats 1600000 in
/-- Build the full stacked witness as `lanes` contiguous `ByteArray`s (`8 * rows` bytes/lane)
in parallel across 16 tasks. -/
def buildWitnessPar (fprog : @& FastProg) (exec : @& FastExec) : FastWitness := Id.run do
  let nProg := fprog.size
  let rowsArr := #[exec.nXor, exec.nMul, exec.nSet, exec.nDeref, exec.nJump, exec.nKeccak]
  let logBytecode := log2FloorPow2 nProg
  let cells := memoryCells exec.memUsed
  let logMem := log2FloorPow2 cells
  let layout := Model.Layout.buildPublicLayout logMem logBytecode rowsArr
  let maxCount := max exec.maxBcCount exec.maxAccess
  let g := exec.g.grow (max exec.memUsed (max nProg maxCount))
  let hXor := 1 <<< (layout.taus[0]?.getD 0)
  let hMul := 1 <<< (layout.taus[1]?.getD 0)
  let hSet := 1 <<< (layout.taus[2]?.getD 0)
  let hDeref := 1 <<< (layout.taus[3]?.getD 0)
  let hJump := 1 <<< (layout.taus[4]?.getD 0)
  let hKeccak := 1 <<< (layout.taus[5]?.getD 0)
  let opWords := fprog.opWords
  let mc0 := exec.mc0
  let mc1 := exec.mc1
  let mc2 := exec.mc2
  let mAccess := exec.mAccess
  let bcCounts := exec.bcCounts
  let tXor := exec.tXor
  let tMul := exec.tMul
  let tSet := exec.tSet
  let tDeref := exec.tDeref
  let tJump := exec.tJump
  let tKeccak := exec.tKeccak
  let nXor := exec.nXor
  let nMul := exec.nMul
  let nSet := exec.nSet
  let nDeref := exec.nDeref
  let nJump := exec.nJump
  let nKeccak := exec.nKeccak
  let memUsed := exec.memUsed

  let tkBc := Task.spawn fun _ => fillBytecodeFinalFast nProg bcCounts g
  let tkXor := Task.spawn fun _ => fillBinaryColsFast nXor hXor tXor opWords mc0 mc1 mc2 g
  let tkMul := Task.spawn fun _ => fillBinaryColsFast nMul hMul tMul opWords mc0 mc1 mc2 g
  let tkSet := Task.spawn fun _ => fillSetColsFast nSet hSet tSet opWords g
  let tkDeref := Task.spawn fun _ => fillDerefColsFast nDeref hDeref tDeref opWords mc0 mc1 mc2 g
  let tkJump := Task.spawn fun _ => fillJumpColsFast nJump hJump tJump opWords mc0 g

  let zeroMid := rounds12Fast zeroState25Fast
  let zeroMidArr : Array UInt64 :=
    #[zeroMid.a00, zeroMid.a01, zeroMid.a02, zeroMid.a03, zeroMid.a04,
      zeroMid.a05, zeroMid.a06, zeroMid.a07, zeroMid.a08, zeroMid.a09,
      zeroMid.a10, zeroMid.a11, zeroMid.a12, zeroMid.a13, zeroMid.a14,
      zeroMid.a15, zeroMid.a16, zeroMid.a17, zeroMid.a18, zeroMid.a19,
      zeroMid.a20, zeroMid.a21, zeroMid.a22, zeroMid.a23, zeroMid.a24]
  let nKTasks := min 16 (max 1 ((nKeccak + 2047) / 2048))
  let kTasks := (Array.range nKTasks).map fun tid =>
    let lo := (tid * nKeccak) / nKTasks
    let hi := ((tid + 1) * nKeccak) / nKTasks
    Task.spawn fun _ => fillKeccakChunkFast lo hi tKeccak opWords mc0 mc1 g zeroMidArr
  let kChunks := kTasks.map Task.get
  let kLos := (Array.range nKTasks).map fun tid => (tid * nKeccak) / nKTasks
  let kHis := (Array.range nKTasks).map fun tid => ((tid + 1) * nKeccak) / nKTasks

  let tailRows := hKeccak - nKeccak
  let midPads : Array ByteArray := (Array.range 25).map fun i =>
    if tailRows == 0 then ByteArray.empty
    else repeatU64BytesExact tailRows (zeroMidArr[i]?.getD 0)

  let shape := layout.shape
  let rowsPerLane := 1 <<< (shape.mu - logBatch)
  let nLanes := shape.nLanes
  let xorCols := tkXor.get
  let mulCols := tkMul.get
  let setCols := tkSet.get
  let derefCols := tkDeref.get
  let jumpCols := tkJump.get
  let bcBuf := tkBc.get
  let qBase := (layout.placements[qKeccak]?.join).map Placement.index |>.getD 0
  let bXor := tableBase ⟨0, by decide⟩
  let bMul := tableBase ⟨1, by decide⟩
  let bSet := tableBase ⟨2, by decide⟩
  let bDeref := tableBase ⟨3, by decide⟩
  let bJump := tableBase ⟨4, by decide⟩
  let bKeccak := tableBase ⟨5, by decide⟩

  let nLTasks := min 16 (max 1 nLanes)
  let laneTasks := (Array.range nLTasks).map fun tid =>
    let laneLo := (tid * nLanes) / nLTasks
    let laneHi := ((tid + 1) * nLanes) / nLTasks
    Task.spawn fun _ => Id.run do
      let placeAt := fun (c : Nat) => layout.placements[c]?.join
      let mut lanes : Array ByteArray :=
        (Array.range (laneHi - laneLo)).map fun _ => zeroBytesExact (8 * rowsPerLane)
      for j in [laneLo:laneHi] do
        let laneStart := j * rowsPerLane
        let laneEnd := laneStart + rowsPerLane
        let mut lane := lanes[j - laneLo]?.getD ByteArray.empty
        if let some p := placeAt memLo then
          lane := copyPlacedColIntoLane lane laneStart laneEnd p mc0 cells memUsed
        if let some p := placeAt memHi then
          lane := copyPlacedColIntoLane lane laneStart laneEnd p mc1 cells memUsed
        if let some p := placeAt memTop then
          lane := copyPlacedColIntoLane lane laneStart laneEnd p mc2 cells memUsed
        if let some p := placeAt memFinal then
          let aF := max p.index laneStart
          let bF := min (p.index + cells) laneEnd
          lane := fillMemFinalLane lane laneStart aF bF p.index memUsed mAccess g
        if let some p := placeAt bytecodeFinal then
          lane := copyPlacedColIntoLane lane laneStart laneEnd p bcBuf nProg nProg
        for i in [:arithWidth] do
          if let some p := placeAt (bXor + i) then
            lane := copyPlacedColIntoLane lane laneStart laneEnd p
              (xorCols[i]?.getD ByteArray.empty) hXor hXor
        for i in [:arithWidth] do
          if let some p := placeAt (bMul + i) then
            lane := copyPlacedColIntoLane lane laneStart laneEnd p
              (mulCols[i]?.getD ByteArray.empty) hMul hMul
        for i in [:setWidth] do
          if let some p := placeAt (bSet + i) then
            lane := copyPlacedColIntoLane lane laneStart laneEnd p
              (setCols[i]?.getD ByteArray.empty) hSet hSet
        for i in [:derefWidth] do
          if let some p := placeAt (bDeref + i) then
            lane := copyPlacedColIntoLane lane laneStart laneEnd p
              (derefCols[i]?.getD ByteArray.empty) hDeref hDeref
        for i in [:jumpWidth] do
          if let some p := placeAt (bJump + i) then
            lane := copyPlacedColIntoLane lane laneStart laneEnd p
              (jumpCols[i]?.getD ByteArray.empty) hJump hJump
        for slot in [:64] do
          let colStart := qBase + slot * hKeccak
          let a := max colStart laneStart
          let b := min (colStart + hKeccak) laneEnd
          if b > a then
            let dataEnd := min b (colStart + nKeccak)
            if dataEnd > a then
              for t in [:nKTasks] do
                let klo := kLos[t]?.getD 0
                let khi := kHis[t]?.getD 0
                let ca := max a (colStart + klo)
                let cb := min dataEnd (colStart + khi)
                if cb > ca then
                  let ch := kChunks[t]?.getD #[]
                  lane := copyColSliceIntoLane lane laneStart ca cb (colStart + klo)
                    (ch[slot]?.getD ByteArray.empty)
            let padA := max a (colStart + nKeccak)
            if padA < b && slot >= 25 && slot < 50 then
              lane := copyColSliceIntoLane lane laneStart padA b (colStart + nKeccak)
                (midPads[slot - 25]?.getD ByteArray.empty)
        for i in [:26] do
          let col := if i < 25 then bKeccak + keccakCnt + 1 + i else bKeccak + keccakCntBc
          if let some p := placeAt col then
            let idx := p.index
            let span := 1 <<< p.variables
            let a := max idx laneStart
            let b := min (idx + span) laneEnd
            if b > a then
              let dataEnd := min b (idx + nKeccak)
              if dataEnd > a then
                for t in [:nKTasks] do
                  let klo := kLos[t]?.getD 0
                  let khi := kHis[t]?.getD 0
                  let ca := max a (idx + klo)
                  let cb := min dataEnd (idx + khi)
                  if cb > ca then
                    let ch := kChunks[t]?.getD #[]
                    lane := copyColSliceIntoLane lane laneStart ca cb (idx + klo)
                      (ch[64 + i]?.getD ByteArray.empty)
        lanes := lanes.setIfInBounds (j - laneLo) lane
      return lanes

  let mut lanesBytes : Array ByteArray := Array.emptyWithCapacity nLanes
  for tk in laneTasks do
    lanesBytes := lanesBytes ++ tk.get

  return {
    logMem := logMem
    logBytecode := logBytecode
    cells := cells
    rows := rowsArr
    layout := layout
    lanesBytes := lanesBytes
  }

/-! ## 16-Task Parallel L0 PCS Commitment (`l0RootFromLanesPar`) -/

/-- Precompute all `(1 <<< logRows) - 1` additive NTT twiddles for a coset into a flat `ByteArray`. -/
def precomputeCosetTwiddles (table : @& Array K) (logRows logInvRate coset : Nat) : ByteArray := Id.run do
  let rows := 1 <<< logRows
  let mut tw := zeroBytesExact (8 * rows)
  let logD := logRows + logInvRate
  for step in [:logRows] do
    let layer := logInvRate + step
    let localBlocks := 1 <<< step
    let values := Model.Pcs.Ntt.rowFromEvals table logD (logD - layer - 1)
    let baseT := Model.Pcs.Ntt.twiddleFromRow values (coset <<< step)
    let stepBase := localBlocks - 1
    tw := setU64Fast tw stepBase.toUSize baseT
    for bit in [:step] do
      let bLen := 1 <<< bit
      let delta := values.getD (bit + 1) 0
      for k in [:bLen] do
        let prev := getU64Fast tw (stepBase + k).toUSize
        tw := setU64Fast tw (stepBase + bLen + k).toUSize (prev ^^^ delta)
  return tw

def nttButterflyZeroLoop (topIdx botIdx : USize) : Nat → ByteArray → ByteArray
  | 0, data => data
  | rem + 1, data =>
    let topV := getU64Fast data topIdx
    let botV := getU64Fast data botIdx
    let data' := setU64Fast data botIdx (botV ^^^ topV)
    nttButterflyZeroLoop (topIdx + 1) (botIdx + 1) rem data'

def nttButterflyMulLoop (t : UInt64) (topIdx botIdx : USize) : Nat → ByteArray → ByteArray
  | 0, data => data
  | rem + 1, data =>
    let topV := getU64Fast data topIdx
    let botV := getU64Fast data botIdx
    let uV := topV ^^^ Model.Field.nativeMul botV t
    let vV := botV ^^^ uV
    let data1 := setU64Fast data topIdx uV
    let data2 := setU64Fast data botIdx vV
    nttButterflyMulLoop t (topIdx + 1) (botIdx + 1) rem data2

def nttBlocksLoop (tw : @& ByteArray) (half : Nat) (halfU strideU twIdx blockRowBase : USize) :
    Nat → ByteArray → ByteArray
  | 0, data => data
  | rem + 1, data =>
    let t := getU64Fast tw twIdx
    let data' :=
      if t == 0 then
        nttButterflyZeroLoop blockRowBase (blockRowBase + halfU) half data
      else
        nttButterflyMulLoop t blockRowBase (blockRowBase + halfU) half data
    nttBlocksLoop tw half halfU strideU (twIdx + 1) (blockRowBase + strideU) rem data'

/-- In-place 1D coset additive NTT on a single `8 * (1 <<< logRows)`-byte lane buffer
using precomputed flat coset twiddles `tw`. -/
def encodeCosetLaneWithTwiddles (tw : @& ByteArray) (laneOrig : @& ByteArray)
    (logRows : Nat) : ByteArray := Id.run do
  let rows := 1 <<< logRows
  if rows == 0 then return laneOrig
  let mut data := ByteArray.emptyWithCapacity (8 * rows)
  data := laneOrig.copySlice 0 data 0 (8 * rows) false
  for step in [:logRows] do
    let localBlocks := 1 <<< step
    let half := 1 <<< (logRows - step - 1)
    let halfU := half.toUSize
    let strideU := (2 * half).toUSize
    let twBase := (localBlocks - 1).toUSize
    data := nttBlocksLoop tw half halfU strideU twBase 0 localBlocks data
  return data

/-- In-place 1D coset additive NTT on a single `8 * (1 <<< logRows)`-byte lane buffer. -/
def encodeCosetLaneBytes (table : @& Array K) (laneOrig : @& ByteArray)
    (logRows logInvRate coset : Nat) : ByteArray :=
  let tw := precomputeCosetTwiddles table logRows logInvRate coset
  encodeCosetLaneWithTwiddles tw laneOrig logRows

@[inline] def absorbWords17Fast (s : State25)
    (w00 w01 w02 w03 w04 w05 w06 w07 w08 w09 w10 w11 w12 w13 w14 w15 w16 : UInt64) : State25 :=
  keccakF1600Fast
    { s with
      a00 := s.a00 ^^^ w00, a01 := s.a01 ^^^ w01, a02 := s.a02 ^^^ w02, a03 := s.a03 ^^^ w03,
      a04 := s.a04 ^^^ w04, a05 := s.a05 ^^^ w05, a06 := s.a06 ^^^ w06, a07 := s.a07 ^^^ w07,
      a08 := s.a08 ^^^ w08, a09 := s.a09 ^^^ w09, a10 := s.a10 ^^^ w10, a11 := s.a11 ^^^ w11,
      a12 := s.a12 ^^^ w12, a13 := s.a13 ^^^ w13, a14 := s.a14 ^^^ w14, a15 := s.a15 ^^^ w15,
      a16 := s.a16 ^^^ w16 }

@[inline] def absorbFinal13Fast (s : State25)
    (w00 w01 w02 w03 w04 w05 w06 w07 w08 w09 w10 w11 w12 : UInt64) : Model.Merkle.Digest32 :=
  let st := keccakF1600Fast
    { s with
      a00 := s.a00 ^^^ w00, a01 := s.a01 ^^^ w01, a02 := s.a02 ^^^ w02, a03 := s.a03 ^^^ w03,
      a04 := s.a04 ^^^ w04, a05 := s.a05 ^^^ w05, a06 := s.a06 ^^^ w06, a07 := s.a07 ^^^ w07,
      a08 := s.a08 ^^^ w08, a09 := s.a09 ^^^ w09, a10 := s.a10 ^^^ w10, a11 := s.a11 ^^^ w11,
      a12 := s.a12 ^^^ w12, a13 := s.a13 ^^^ 1, a16 := s.a16 ^^^ 0x8000000000000000 }
  ⟨st.a00, st.a01, st.a02, st.a03⟩

@[inline] def hashPair25Fast (left right : Model.Merkle.Digest32) : Model.Merkle.Digest32 :=
  let st := keccakF1600Fast
    { zeroState25Fast with
      a00 := left.lo0, a01 := left.lo1, a02 := left.hi0, a03 := left.hi1,
      a04 := right.lo0, a05 := right.lo1, a06 := right.hi0, a07 := right.hi1,
      a08 := 1, a16 := 0x8000000000000000 }
  ⟨st.a00, st.a01, st.a02, st.a03⟩

@[inline] def laneWordAt (encodedLanes : @& Array ByteArray) (lanes : Nat) (rIdx : USize)
    (leafWordPos : Nat) : UInt64 :=
  if leafWordPos + lanes >= 64 then
    let laneIdx := 63 - leafWordPos
    getU64Fast (encodedLanes[laneIdx]?.getD ByteArray.empty) rIdx
  else 0

def hashLeafFromEncodedLanes (st1 st2 st3 : State25)
    (encodedLanes : @& Array ByteArray) (lanes nVecs row : Nat) : Model.Merkle.Digest32 :=
  let rIdx := row.toUSize
  let s1 :=
    if nVecs <= 5 then st1
    else
      absorbWords17Fast zeroState25Fast
        (laneWordAt encodedLanes lanes rIdx 0)  (laneWordAt encodedLanes lanes rIdx 1)
        (laneWordAt encodedLanes lanes rIdx 2)  (laneWordAt encodedLanes lanes rIdx 3)
        (laneWordAt encodedLanes lanes rIdx 4)  (laneWordAt encodedLanes lanes rIdx 5)
        (laneWordAt encodedLanes lanes rIdx 6)  (laneWordAt encodedLanes lanes rIdx 7)
        (laneWordAt encodedLanes lanes rIdx 8)  (laneWordAt encodedLanes lanes rIdx 9)
        (laneWordAt encodedLanes lanes rIdx 10) (laneWordAt encodedLanes lanes rIdx 11)
        (laneWordAt encodedLanes lanes rIdx 12) (laneWordAt encodedLanes lanes rIdx 13)
        (laneWordAt encodedLanes lanes rIdx 14) (laneWordAt encodedLanes lanes rIdx 15)
        (laneWordAt encodedLanes lanes rIdx 16)
  let s2 :=
    if nVecs <= 3 then st2
    else
      absorbWords17Fast s1
        (laneWordAt encodedLanes lanes rIdx 17) (laneWordAt encodedLanes lanes rIdx 18)
        (laneWordAt encodedLanes lanes rIdx 19) (laneWordAt encodedLanes lanes rIdx 20)
        (laneWordAt encodedLanes lanes rIdx 21) (laneWordAt encodedLanes lanes rIdx 22)
        (laneWordAt encodedLanes lanes rIdx 23) (laneWordAt encodedLanes lanes rIdx 24)
        (laneWordAt encodedLanes lanes rIdx 25) (laneWordAt encodedLanes lanes rIdx 26)
        (laneWordAt encodedLanes lanes rIdx 27) (laneWordAt encodedLanes lanes rIdx 28)
        (laneWordAt encodedLanes lanes rIdx 29) (laneWordAt encodedLanes lanes rIdx 30)
        (laneWordAt encodedLanes lanes rIdx 31) (laneWordAt encodedLanes lanes rIdx 32)
        (laneWordAt encodedLanes lanes rIdx 33)
  let s3 :=
    if nVecs <= 1 then st3
    else
      absorbWords17Fast s2
        (laneWordAt encodedLanes lanes rIdx 34) (laneWordAt encodedLanes lanes rIdx 35)
        (laneWordAt encodedLanes lanes rIdx 36) (laneWordAt encodedLanes lanes rIdx 37)
        (laneWordAt encodedLanes lanes rIdx 38) (laneWordAt encodedLanes lanes rIdx 39)
        (laneWordAt encodedLanes lanes rIdx 40) (laneWordAt encodedLanes lanes rIdx 41)
        (laneWordAt encodedLanes lanes rIdx 42) (laneWordAt encodedLanes lanes rIdx 43)
        (laneWordAt encodedLanes lanes rIdx 44) (laneWordAt encodedLanes lanes rIdx 45)
        (laneWordAt encodedLanes lanes rIdx 46) (laneWordAt encodedLanes lanes rIdx 47)
        (laneWordAt encodedLanes lanes rIdx 48) (laneWordAt encodedLanes lanes rIdx 49)
        (laneWordAt encodedLanes lanes rIdx 50)
  absorbFinal13Fast s3
    (laneWordAt encodedLanes lanes rIdx 51) (laneWordAt encodedLanes lanes rIdx 52)
    (laneWordAt encodedLanes lanes rIdx 53) (laneWordAt encodedLanes lanes rIdx 54)
    (laneWordAt encodedLanes lanes rIdx 55) (laneWordAt encodedLanes lanes rIdx 56)
    (laneWordAt encodedLanes lanes rIdx 57) (laneWordAt encodedLanes lanes rIdx 58)
    (laneWordAt encodedLanes lanes rIdx 59) (laneWordAt encodedLanes lanes rIdx 60)
    (laneWordAt encodedLanes lanes rIdx 61) (laneWordAt encodedLanes lanes rIdx 62)
    (laneWordAt encodedLanes lanes rIdx 63)

def reduceDigestsPow2 (digests : Array Model.Merkle.Digest32) (levels : Nat) :
    Model.Merkle.Digest32 := Id.run do
  let mut cur := digests
  for lv in [:levels] do
    let half := 1 <<< (levels - 1 - lv)
    let mut next := Array.emptyWithCapacity half
    for i in [:half] do
      let l := cur[2 * i]?.getD default
      let r := cur[2 * i + 1]?.getD default
      next := next.push (hashPair25Fast l r)
    cur := next
  return cur[0]?.getD default

def hashLeaf64Full (encodedLanes : @& Array ByteArray) (rIdx : USize) : Model.Merkle.Digest32 :=
  let s1 :=
    absorbWords17Fast zeroState25Fast
      (getU64Fast (encodedLanes[63]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[62]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[61]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[60]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[59]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[58]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[57]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[56]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[55]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[54]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[53]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[52]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[51]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[50]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[49]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[48]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[47]?.getD ByteArray.empty) rIdx)
  let s2 :=
    absorbWords17Fast s1
      (getU64Fast (encodedLanes[46]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[45]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[44]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[43]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[42]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[41]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[40]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[39]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[38]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[37]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[36]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[35]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[34]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[33]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[32]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[31]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[30]?.getD ByteArray.empty) rIdx)
  let s3 :=
    absorbWords17Fast s2
      (getU64Fast (encodedLanes[29]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[28]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[27]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[26]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[25]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[24]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[23]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[22]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[21]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[20]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[19]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[18]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[17]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[16]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[15]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[14]?.getD ByteArray.empty) rIdx)
      (getU64Fast (encodedLanes[13]?.getD ByteArray.empty) rIdx)
  absorbFinal13Fast s3
    (getU64Fast (encodedLanes[12]?.getD ByteArray.empty) rIdx)
    (getU64Fast (encodedLanes[11]?.getD ByteArray.empty) rIdx)
    (getU64Fast (encodedLanes[10]?.getD ByteArray.empty) rIdx)
    (getU64Fast (encodedLanes[9]?.getD ByteArray.empty) rIdx)
    (getU64Fast (encodedLanes[8]?.getD ByteArray.empty) rIdx)
    (getU64Fast (encodedLanes[7]?.getD ByteArray.empty) rIdx)
    (getU64Fast (encodedLanes[6]?.getD ByteArray.empty) rIdx)
    (getU64Fast (encodedLanes[5]?.getD ByteArray.empty) rIdx)
    (getU64Fast (encodedLanes[4]?.getD ByteArray.empty) rIdx)
    (getU64Fast (encodedLanes[3]?.getD ByteArray.empty) rIdx)
    (getU64Fast (encodedLanes[2]?.getD ByteArray.empty) rIdx)
    (getU64Fast (encodedLanes[1]?.getD ByteArray.empty) rIdx)
    (getU64Fast (encodedLanes[0]?.getD ByteArray.empty) rIdx)

def subtreeRootRec (st1 st2 st3 : State25) (encodedLanes : @& Array ByteArray)
    (lanes nVecs baseRow : Nat) : Nat → Model.Merkle.Digest32
  | 0 =>
    if lanes == 64 then hashLeaf64Full encodedLanes baseRow.toUSize
    else hashLeafFromEncodedLanes st1 st2 st3 encodedLanes lanes nVecs baseRow
  | lv + 1 =>
    let half := 1 <<< lv
    let l := subtreeRootRec st1 st2 st3 encodedLanes lanes nVecs baseRow lv
    let r := subtreeRootRec st1 st2 st3 encodedLanes lanes nVecs (baseRow + half) lv
    hashPair25Fast l r

def subtreeRootFromLanesChunk (st1 st2 st3 : State25)
    (encodedLanes : @& Array ByteArray) (lanes nVecs baseRow subLog : Nat) :
    Model.Merkle.Digest32 :=
  subtreeRootRec st1 st2 st3 encodedLanes lanes nVecs baseRow subLog

/-- 16-task parallel L0 PCS commitment directly from `lanesBytes` (`1 <= lanes <= 64`). -/
def l0RootFromLanesPar (lanesBytes : @& Array ByteArray) (shape : Shape)
    (logInvRate : Nat := logInvRateDefault) : ByteArray := Id.run do
  let lanes := shape.nLanes
  let logRows := shape.mu - logBatch
  if !(1 <= lanes && lanes <= 64) then
    let rows := 1 <<< logRows
    let mut msg := Array.emptyWithCapacity (lanes * rows)
    for l in [:lanes] do
      let lb := lanesBytes[l]?.getD ByteArray.empty
      for r in [:rows] do
        msg := msg.push (getU64Fast lb r.toUSize)
    return Spec.Pcs.Commit.root msg lanes logRows logInvRate
  let nVecs := (lanes + 7) / 8
  let logD := logRows + logInvRate
  let table := Model.Pcs.Ntt.evals logD
  let st1 := keccakF1600Fast zeroState25Fast
  let st2 := keccakF1600Fast st1
  let st3 := keccakF1600Fast st2
  let rate := 1 <<< logInvRate
  let mut cosetRoots : Array Model.Merkle.Digest32 := Array.emptyWithCapacity rate
  for coset in [:rate] do
    let tw := precomputeCosetTwiddles table logRows logInvRate coset
    let nLaneTasks := min 16 lanes
    let laneGroupTasks := (Array.range nLaneTasks).map fun tid =>
      let lo := (tid * lanes) / nLaneTasks
      let hi := ((tid + 1) * lanes) / nLaneTasks
      Task.spawn fun _ => Id.run do
        let mut group := Array.emptyWithCapacity (hi - lo)
        for l in [lo:hi] do
          let lb := lanesBytes[l]?.getD ByteArray.empty
          group := group.push (encodeCosetLaneWithTwiddles tw lb logRows)
        return group
    let mut encodedLanes := Array.emptyWithCapacity lanes
    for tk in laneGroupTasks do
      encodedLanes := encodedLanes ++ tk.get
    let cosetRoot :=
      if logRows >= 4 then
        let subLog := logRows - 4
        let subRows := 1 <<< subLog
        let treeTasks := (Array.range 16).map fun tid =>
          Task.spawn fun _ =>
            subtreeRootFromLanesChunk st1 st2 st3 encodedLanes lanes nVecs (tid * subRows) subLog
        let top16 := treeTasks.map Task.get
        reduceDigestsPow2 top16 4
      else
        subtreeRootFromLanesChunk st1 st2 st3 encodedLanes lanes nVecs 0 logRows
    cosetRoots := cosetRoots.push cosetRoot
  return (reduceDigestsPow2 cosetRoots logInvRate).toBytes

/-! ## Announce Digest, Transcript Challenges, and E2E Bridge Helpers -/

def announceWordsFast (logMem : Nat) (rows : @& Array Nat) : Array E :=
  #[Spec.Field.embed (UInt64.ofNat logMem)] ++
    rows.map (fun cnt => Spec.Field.embed (UInt64.ofNat cnt)) ++
    #[Spec.Field.embed (UInt64.ofNat logInvRateDefault)]

def announceDigestFast (logMem : Nat) (rows : @& Array Nat) : ByteArray := Id.run do
  let words := announceWordsFast logMem rows
  let mut buf := zeroBytesExact (24 * words.size)
  for i in [:words.size] do
    let w := words[i]?.getD Spec.Field.zero
    let base := (3 * i).toUSize
    buf := setU64Fast buf base w.c0
    buf := setU64Fast buf (base + 1) w.c1
    buf := setU64Fast buf (base + 2) w.c2
  return keccak256FastStream buf

def challengePairFast (iv : ByteArray) (publicInput : @& Array E)
    (logMem : Nat) (rows : @& Array Nat) (root : ByteArray) : E × E :=
  let first := Spec.Witness.sampleAfter
    (Model.Transcript.Registers.init iv (Spec.Witness.publicBytes publicInput))
    (announceWordsFast logMem rows)
  let roots := Spec.Merkle.hashToScalars root
  (first.1, (Spec.Witness.sampleAfter first.2 #[roots.1, roots.2]).1)

/-- Convert `lanesBytes` into a contiguous `Array K` stacked message (`committedLen shape` words),
parallelized per lane across 16 tasks for downstream Bus / GKR / WHIR stages. -/
def messageArrayOfLanesPar (lanesBytes : @& Array ByteArray) (shape : Shape) : Array K := Id.run do
  let lanes := shape.nLanes
  let rows := 1 <<< (shape.mu - logBatch)
  let nTasks := min 16 (max 1 lanes)
  let tasks := (Array.range nTasks).map fun tid =>
    let lo := (tid * lanes) / nTasks
    let hi := ((tid + 1) * lanes) / nTasks
    Task.spawn fun _ => Id.run do
      let mut chunk := Array.emptyWithCapacity ((hi - lo) * rows)
      for l in [lo:hi] do
        let lb := lanesBytes[l]?.getD ByteArray.empty
        for r in [:rows] do
          chunk := chunk.push (getU64Fast lb r.toUSize)
      return chunk
  let mut out := Array.emptyWithCapacity (lanes * rows)
  for tk in tasks do
    out := out ++ tk.get
  return out

set_option maxHeartbeats 1600000 in
/-- Compute the 25 `keccakOut` columns (`steps = 1 <<< tau_keccak` words each) in parallel across 16 tasks
directly from `FastExec.tKeccak`, avoiding boxed `Memory` / `StepTrace` reconstruction! -/
def buildKeccakOutColsPar (fprog : @& FastProg) (exec : @& FastExec) (steps : Nat) :
    Array (Array K) := Id.run do
  let nKeccak := exec.nKeccak
  let tKeccak := exec.tKeccak
  let opWords := fprog.opWords
  let mc0 := exec.mc0
  let mc1 := exec.mc1
  let zeroPerm := keccakF1600Fast zeroState25Fast
  let zeroPermArr : Array UInt64 :=
    #[zeroPerm.a00, zeroPerm.a01, zeroPerm.a02, zeroPerm.a03, zeroPerm.a04,
      zeroPerm.a05, zeroPerm.a06, zeroPerm.a07, zeroPerm.a08, zeroPerm.a09,
      zeroPerm.a10, zeroPerm.a11, zeroPerm.a12, zeroPerm.a13, zeroPerm.a14,
      zeroPerm.a15, zeroPerm.a16, zeroPerm.a17, zeroPerm.a18, zeroPerm.a19,
      zeroPerm.a20, zeroPerm.a21, zeroPerm.a22, zeroPerm.a23, zeroPerm.a24]
  let nTasks := min 16 (max 1 ((nKeccak + 2047) / 2048))
  let tasks := (Array.range nTasks).map fun tid =>
    let lo := (tid * nKeccak) / nTasks
    let hi := ((tid + 1) * nKeccak) / nTasks
    Task.spawn fun _ => Id.run do
      let cnt := hi - lo
      let mut cols : Array (Array K) := (Array.range 25).map fun _ => Array.emptyWithCapacity cnt
      for s in [:cnt] do
        let row := lo + s
        let kBase := (29 * row).toUSize
        let pc := (getU32Fast tKeccak kBase).toNat
        let fp := (getU32Fast tKeccak (kBase + 1)).toNat
        let opBase := (16 * pc).toUSize
        let m0 := (getU64Fast opWords (opBase + 1)).toNat
        let m1 := (getU64Fast opWords (opBase + 2)).toNat
        let m2 := (getU64Fast opWords (opBase + 3)).toNat
        let m3 := (getU64Fast opWords (opBase + 4)).toNat
        let tail := (getU64Fast opWords (opBase + 5)).toNat
        let b8 := (getU64Fast opWords (opBase + 6)).toNat
        let cap := (getU64Fast opWords (opBase + 7)).toNat
        let inOdd := getU64Fast opWords (opBase + 9) != 0
        let a00 := (fp + m0).toUSize
        let a01 := (fp + m1).toUSize
        let a02 := (fp + m2).toUSize
        let a03 := (fp + m3).toUSize
        let a04 := (fp + tail).toUSize
        let a05 := (fp + tail + 1).toUSize
        let a06 := (fp + tail + 2).toUSize
        let a07 := (fp + tail + 3).toUSize
        let a08 := (fp + b8).toUSize
        let a09 := (fp + cap).toUSize
        let a10 := (fp + cap + 1).toUSize
        let a11 := (fp + cap + 2).toUSize
        let a12 := (fp + cap + 3).toUSize
        let inSt : State25 :=
          if inOdd then
            ⟨getU64Fast mc1 a00, getU64Fast mc0 a01, getU64Fast mc1 a01, getU64Fast mc0 a02, getU64Fast mc1 a02,
             getU64Fast mc0 a03, getU64Fast mc1 a03, getU64Fast mc0 a04, getU64Fast mc1 a04, getU64Fast mc0 a05,
             getU64Fast mc1 a05, getU64Fast mc0 a06, getU64Fast mc1 a06, getU64Fast mc0 a07, getU64Fast mc1 a07,
             getU64Fast mc0 a08, getU64Fast mc1 a08, getU64Fast mc0 a09, getU64Fast mc1 a09, getU64Fast mc0 a10,
             getU64Fast mc1 a10, getU64Fast mc0 a11, getU64Fast mc1 a11, getU64Fast mc0 a12, getU64Fast mc1 a12⟩
          else
            ⟨getU64Fast mc0 a00, getU64Fast mc1 a00, getU64Fast mc0 a01, getU64Fast mc1 a01, getU64Fast mc0 a02,
             getU64Fast mc1 a02, getU64Fast mc0 a03, getU64Fast mc1 a03, getU64Fast mc0 a04, getU64Fast mc1 a04,
             getU64Fast mc0 a05, getU64Fast mc1 a05, getU64Fast mc0 a06, getU64Fast mc1 a06, getU64Fast mc0 a07,
             getU64Fast mc1 a07, getU64Fast mc0 a08, getU64Fast mc0 a09, getU64Fast mc1 a09, getU64Fast mc0 a10,
             getU64Fast mc1 a10, getU64Fast mc0 a11, getU64Fast mc1 a11, getU64Fast mc0 a12, getU64Fast mc1 a12⟩
        let outSt := keccakF1600Fast inSt
        let pushL := fun (arr : Array (Array K)) (l : Nat) (v : UInt64) =>
          arr.modify l (fun c => c.push v)
        cols := pushL cols 0 outSt.a00; cols := pushL cols 1 outSt.a01
        cols := pushL cols 2 outSt.a02; cols := pushL cols 3 outSt.a03
        cols := pushL cols 4 outSt.a04; cols := pushL cols 5 outSt.a05
        cols := pushL cols 6 outSt.a06; cols := pushL cols 7 outSt.a07
        cols := pushL cols 8 outSt.a08; cols := pushL cols 9 outSt.a09
        cols := pushL cols 10 outSt.a10; cols := pushL cols 11 outSt.a11
        cols := pushL cols 12 outSt.a12; cols := pushL cols 13 outSt.a13
        cols := pushL cols 14 outSt.a14; cols := pushL cols 15 outSt.a15
        cols := pushL cols 16 outSt.a16; cols := pushL cols 17 outSt.a17
        cols := pushL cols 18 outSt.a18; cols := pushL cols 19 outSt.a19
        cols := pushL cols 20 outSt.a20; cols := pushL cols 21 outSt.a21
        cols := pushL cols 22 outSt.a22; cols := pushL cols 23 outSt.a23
        cols := pushL cols 24 outSt.a24
      return cols
  let chunks := tasks.map Task.get
  let tailRows := steps - nKeccak
  return (Array.range 25).map fun lane => Id.run do
    let pad := zeroPermArr[lane]?.getD 0
    let mut out := Array.emptyWithCapacity steps
    for ch in chunks do
      out := out ++ (ch[lane]?.getD #[])
    if tailRows > 0 then
      out := out ++ Array.replicate tailRows pad
    return out

/-- Lightweight `SizedRun` shell (no boxed `Memory` / `StepTrace` arrays needed when `keccakOutCols`
are supplied directly!). -/
def shellSizedRun (exec : @& FastExec) (fw : @& FastWitness) : SizedRun :=
  let emptyTrace : ExecutionTrace := {
    tables := Array.replicate nTables #[]
    bytecodeCount := #[]
    cycles := exec.cycles
    memUsed := exec.memUsed
    unconstrained := exec.unconstrained
    memory := {}
    g := {}
  }
  { trace := emptyTrace
    logMem := fw.logMem
    logBytecode := fw.logBytecode
    cells := fw.cells
    rows := fw.rows
    layout := fw.layout }

end LeanVmXmss.Model.Witness









