import Model.Bus.Native
import Model.Witness.Flat

namespace LeanVmXmss.Model.Bus

open Spec.Field (K E zero one)
open Model.Field
open Model.Pcs.Ntt (foldRange foldRangeLoop)

structure PlanarE where
  c0 : ByteArray
  c1 : ByteArray
  c2 : ByteArray
  deriving Inhabited

structure PlanarK where
  words : ByteArray
  deriving Inhabited

def planarEEmpty (n : Nat) : PlanarE :=
  ⟨ByteArray.emptyWithCapacity (8 * n), ByteArray.emptyWithCapacity (8 * n),
   ByteArray.emptyWithCapacity (8 * n)⟩

def planarEPush (p : PlanarE) (x : E) : PlanarE :=
  ⟨Model.Witness.pushU64LE p.c0 x.c0,
   Model.Witness.pushU64LE p.c1 x.c1,
   Model.Witness.pushU64LE p.c2 x.c2⟩

def planarEGet (p : PlanarE) (i : Nat) : E :=
  ⟨Model.Witness.readU64LE p.c0 i,
   Model.Witness.readU64LE p.c1 i,
   Model.Witness.readU64LE p.c2 i⟩

def decodePlanarE (p : PlanarE) : Array E :=
  let n := p.c0.size / 8
  foldRange n (fun acc i => acc.push (planarEGet p i)) (Array.emptyWithCapacity n)

def encodePlanarE (xs : Array E) : PlanarE :=
  foldRange xs.size (fun acc i => planarEPush acc (xs[i]?.getD zero)) (planarEEmpty xs.size)

theorem usize_offset_lt {b : ByteArray} {base : USize} {k : Nat}
    (h1 : base ≤ base + 7) (h2 : base + 7 < b.usize) (hk : k ≤ 7) :
    (base + USize.ofNat k).toNat < b.size := by
  have hlt1 : base.toNat ≤ (base + 7).toNat := USize.le_iff_toNat_le.mp h1
  have hlt2 : (base + 7).toNat < b.usize.toNat := USize.lt_iff_toNat_lt.mp h2
  have husz : b.usize.toNat ≤ b.size := by
    rw [ByteArray.usize, USize.toNat_ofNat']
    exact Nat.mod_le _ _
  have _hbase_lt : base.toNat < USize.size := USize.toNat_lt_size base
  have _h32 : 8 ≤ 2 ^ System.Platform.numBits := by
    rcases System.Platform.numBits_eq with h | h
    · simp [h]
    · simp [h]
  have hsize_eq : USize.size = 2 ^ System.Platform.numBits := rfl
  have h7 : (7 : USize).toNat = 7 := by
    change (USize.ofNat 7).toNat = 7
    rw [USize.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  have hk_val : (USize.ofNat k).toNat = k := by
    rw [USize.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  have hmod : (base + 7).toNat = (base.toNat + 7) % USize.size := by
    rw [USize.toNat_add, h7, hsize_eq]
  have hno_wrap : base.toNat + 7 < USize.size := by
    by_cases hlt : base.toNat + 7 < USize.size
    · exact hlt
    · have hsub : (base + 7).toNat = base.toNat + 7 - USize.size := by
        rw [hmod, Nat.mod_eq_sub_mod (by omega)]
        exact Nat.mod_eq_of_lt (by omega)
      omega
  have _h7_eq : (base + 7).toNat = base.toNat + 7 := by
    rw [hmod]
    exact Nat.mod_eq_of_lt hno_wrap
  rw [USize.toNat_add, hk_val, Nat.mod_eq_of_lt (by omega)]
  omega

@[inline] def readU64Fast (b : @& ByteArray) (idx : USize) : UInt64 :=
  let base := idx <<< 3
  let top := base + 7
  if h1 : base ≤ top then
    if h2 : top < b.usize then
      let b0 := (b.uget base (by simpa using usize_offset_lt (k := 0) h1 h2 (by omega))).toUInt64
      let b1 := (b.uget (base + 1) (usize_offset_lt (k := 1) h1 h2 (by omega))).toUInt64
      let b2 := (b.uget (base + 2) (usize_offset_lt (k := 2) h1 h2 (by omega))).toUInt64
      let b3 := (b.uget (base + 3) (usize_offset_lt (k := 3) h1 h2 (by omega))).toUInt64
      let b4 := (b.uget (base + 4) (usize_offset_lt (k := 4) h1 h2 (by omega))).toUInt64
      let b5 := (b.uget (base + 5) (usize_offset_lt (k := 5) h1 h2 (by omega))).toUInt64
      let b6 := (b.uget (base + 6) (usize_offset_lt (k := 6) h1 h2 (by omega))).toUInt64
      let b7 := (b.uget (base + 7) (usize_offset_lt (k := 7) h1 h2 (by omega))).toUInt64
      b0 + (b1 <<< 8) + (b2 <<< 16) + (b3 <<< 24) +
      (b4 <<< 32) + (b5 <<< 40) + (b6 <<< 48) + (b7 <<< 56)
    else 0
  else 0

theorem usize_lt_size {b : ByteArray} {i : USize} (h : i < b.usize) : i.toNat < b.size := by
  have hlt : i.toNat < b.usize.toNat := USize.lt_iff_toNat_lt.mp h
  have husz : b.usize.toNat ≤ b.size := by
    rw [ByteArray.usize, USize.toNat_ofNat']
    exact Nat.mod_le _ _
  omega

@[inline] def setByteFast (b : ByteArray) (i : USize) (v : UInt8) : ByteArray :=
  if h : i < b.usize then b.uset i v (usize_lt_size h) else b

@[inline] def writeU64Fast (b : ByteArray) (idx : USize) (w : UInt64) : ByteArray :=
  let base := idx <<< 3
  let b := setByteFast b base w.toUInt8
  let b := setByteFast b (base + 1) (w >>> 8).toUInt8
  let b := setByteFast b (base + 2) (w >>> 16).toUInt8
  let b := setByteFast b (base + 3) (w >>> 24).toUInt8
  let b := setByteFast b (base + 4) (w >>> 32).toUInt8
  let b := setByteFast b (base + 5) (w >>> 40).toUInt8
  let b := setByteFast b (base + 6) (w >>> 48).toUInt8
  setByteFast b (base + 7) (w >>> 56).toUInt8

@[inline] def writeEFast (p : PlanarE) (i : USize) (e : E) : PlanarE :=
  let ⟨c0, c1, c2⟩ := p
  ⟨writeU64Fast c0 i e.c0, writeU64Fast c1 i e.c1, writeU64Fast c2 i e.c2⟩

@[inline] def pushU64Fast (b : ByteArray) (w : UInt64) : ByteArray :=
  b.push w.toUInt8
   |>.push (w >>> 8).toUInt8
   |>.push (w >>> 16).toUInt8
   |>.push (w >>> 24).toUInt8
   |>.push (w >>> 32).toUInt8
   |>.push (w >>> 40).toUInt8
   |>.push (w >>> 48).toUInt8
   |>.push (w >>> 56).toUInt8

@[inline] def planarEPushFast (p : PlanarE) (x : E) : PlanarE :=
  let ⟨c0, c1, c2⟩ := p
  ⟨pushU64Fast c0 x.c0, pushU64Fast c1 x.c1, pushU64Fast c2 x.c2⟩

@[inline] def planarEAppend (a b : PlanarE) : PlanarE :=
  let ⟨a0, a1, a2⟩ := a
  let ⟨b0, b1, b2⟩ := b
  ⟨a0 ++ b0, a1 ++ b1, a2 ++ b2⟩

@[inline] def planarESize (p : @& PlanarE) : Nat := p.c0.size / 8

@[inline] def readEFast (p : @& PlanarE) (i : USize) : E :=
  ⟨readU64Fast p.c0 i, readU64Fast p.c1 i, readU64Fast p.c2 i⟩

@[inline] def readEDefault (p : @& PlanarE) (n : Nat) (i : Nat) (defVal : E) : E :=
  if i < n then readEFast p (USize.ofNat i) else defVal

def encodePlanarEFast (xs : @& Array E) : PlanarE :=
  foldRange xs.size (fun acc i => planarEPushFast acc (xs[i]?.getD zero)) (planarEEmpty xs.size)

def decodePlanarEFast (p : @& PlanarE) : Array E :=
  let n := planarESize p
  foldRange n (fun acc i => acc.push (readEFast p (USize.ofNat i))) (Array.emptyWithCapacity n)

def parTreeReduce {α : Type} (depth minChunk base len : Nat) (leaf : Nat → Nat → α)
    (combine : α → α → α) : α :=
  Nat.rec (motive := fun _ => Nat → Nat → α)
    (fun b l => leaf b l)
    (fun _ recFn b l =>
      if l < minChunk then
        leaf b l
      else
        let half := l / 2
        let rightTask := Task.spawn (fun _ => recFn (b + half) (l - half))
        let leftVal := recFn b half
        combine leftVal rightTask.get)
    depth base len

@[inline] def parReduce16 {α : Type} (minChunk len : Nat) (leaf : Nat → Nat → α)
    (combine : α → α → α) : α :=
  parTreeReduce 4 minChunk 0 len leaf combine

def encodePlanarKChunk (col : @& Array K) (base len : Nat) : ByteArray :=
  foldRangeLoop
    (fun acc i => pushU64Fast acc (col[i]?.getD 0))
    len base (ByteArray.emptyWithCapacity (8 * len))

def encodePlanarK (col : @& Array K) : PlanarK :=
  ⟨parReduce16 2048 col.size (encodePlanarKChunk col) ByteArray.append⟩

def encodeColumnsRange (cols : @& Array (Array K)) (base len : Nat) : Array PlanarK :=
  foldRangeLoop
    (fun acc i => acc.push (encodePlanarK (cols[i]?.getD #[])))
    len base (Array.emptyWithCapacity len)

def encodeColumns (cols : @& Array (Array K)) : Array PlanarK :=
  parReduce16 4 cols.size (encodeColumnsRange cols) Array.append

@[inline] def readKDefault (pk : @& PlanarK) (i : Nat) : K :=
  if i < pk.words.size / 8 then readU64Fast pk.words (USize.ofNat i) else 0

@[inline] def getColK (pcols : @& Array PlanarK) (colIdx rowIdx : Nat) : K :=
  match pcols[colIdx]? with
  | some pk => readKDefault pk rowIdx
  | none => 0

def batchInv (xs : Array E) : Array E :=
  let n := xs.size
  let pref := foldRange n
    (fun acc i =>
      let prev := acc.back?.getD one
      acc.push (planarEmul prev (xs[i]?.getD one)))
    #[]
  let total := pref.back?.getD one
  let invTotal := nativeEinv total
  let out := foldRange n
    (fun (st : E × Array E) k =>
      let i := n - 1 - k
      let xi := xs[i]?.getD one
      let pre := if i = 0 then one else pref[i - 1]?.getD one
      let yi := planarEmul st.1 pre
      (planarEmul st.1 xi, st.2.setIfInBounds i yi))
    (invTotal, Array.replicate n zero)
  out.2

end LeanVmXmss.Model.Bus
