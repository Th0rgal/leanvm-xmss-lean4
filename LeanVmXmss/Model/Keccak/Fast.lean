import Model.Keccak.Registers

namespace LeanVmXmss.Model.Keccak

@[inline] def rotlConst (a : UInt64) (s r : UInt64) : UInt64 :=
  (a <<< s) ||| (a >>> r)

@[inline] def round25Fast (s : State25) (rc : UInt64) : State25 :=
  let c0 := s.a00 ^^^ s.a05 ^^^ s.a10 ^^^ s.a15 ^^^ s.a20
  let c1 := s.a01 ^^^ s.a06 ^^^ s.a11 ^^^ s.a16 ^^^ s.a21
  let c2 := s.a02 ^^^ s.a07 ^^^ s.a12 ^^^ s.a17 ^^^ s.a22
  let c3 := s.a03 ^^^ s.a08 ^^^ s.a13 ^^^ s.a18 ^^^ s.a23
  let c4 := s.a04 ^^^ s.a09 ^^^ s.a14 ^^^ s.a19 ^^^ s.a24
  let d0 := c4 ^^^ rotlConst c1 1 63
  let d1 := c0 ^^^ rotlConst c2 1 63
  let d2 := c1 ^^^ rotlConst c3 1 63
  let d3 := c2 ^^^ rotlConst c4 1 63
  let d4 := c3 ^^^ rotlConst c0 1 63
  let b00 := s.a00 ^^^ d0
  let b10 := rotlConst (s.a01 ^^^ d1) 1 63
  let b20 := rotlConst (s.a02 ^^^ d2) 62 2
  let b05 := rotlConst (s.a03 ^^^ d3) 28 36
  let b15 := rotlConst (s.a04 ^^^ d4) 27 37
  let b16 := rotlConst (s.a05 ^^^ d0) 36 28
  let b01 := rotlConst (s.a06 ^^^ d1) 44 20
  let b11 := rotlConst (s.a07 ^^^ d2) 6 58
  let b21 := rotlConst (s.a08 ^^^ d3) 55 9
  let b06 := rotlConst (s.a09 ^^^ d4) 20 44
  let b07 := rotlConst (s.a10 ^^^ d0) 3 61
  let b17 := rotlConst (s.a11 ^^^ d1) 10 54
  let b02 := rotlConst (s.a12 ^^^ d2) 43 21
  let b12 := rotlConst (s.a13 ^^^ d3) 25 39
  let b22 := rotlConst (s.a14 ^^^ d4) 39 25
  let b23 := rotlConst (s.a15 ^^^ d0) 41 23
  let b08 := rotlConst (s.a16 ^^^ d1) 45 19
  let b18 := rotlConst (s.a17 ^^^ d2) 15 49
  let b03 := rotlConst (s.a18 ^^^ d3) 21 43
  let b13 := rotlConst (s.a19 ^^^ d4) 8 56
  let b14 := rotlConst (s.a20 ^^^ d0) 18 46
  let b24 := rotlConst (s.a21 ^^^ d1) 2 62
  let b09 := rotlConst (s.a22 ^^^ d2) 61 3
  let b19 := rotlConst (s.a23 ^^^ d3) 56 8
  let b04 := rotlConst (s.a24 ^^^ d4) 14 50
  ⟨(b00 ^^^ ((~~~b01) &&& b02)) ^^^ rc,
    b01 ^^^ ((~~~b02) &&& b03),
    b02 ^^^ ((~~~b03) &&& b04),
    b03 ^^^ ((~~~b04) &&& b00),
    b04 ^^^ ((~~~b00) &&& b01),
    b05 ^^^ ((~~~b06) &&& b07),
    b06 ^^^ ((~~~b07) &&& b08),
    b07 ^^^ ((~~~b08) &&& b09),
    b08 ^^^ ((~~~b09) &&& b05),
    b09 ^^^ ((~~~b05) &&& b06),
    b10 ^^^ ((~~~b11) &&& b12),
    b11 ^^^ ((~~~b12) &&& b13),
    b12 ^^^ ((~~~b13) &&& b14),
    b13 ^^^ ((~~~b14) &&& b10),
    b14 ^^^ ((~~~b10) &&& b11),
    b15 ^^^ ((~~~b16) &&& b17),
    b16 ^^^ ((~~~b17) &&& b18),
    b17 ^^^ ((~~~b18) &&& b19),
    b18 ^^^ ((~~~b19) &&& b15),
    b19 ^^^ ((~~~b15) &&& b16),
    b20 ^^^ ((~~~b21) &&& b22),
    b21 ^^^ ((~~~b22) &&& b23),
    b22 ^^^ ((~~~b23) &&& b24),
    b23 ^^^ ((~~~b24) &&& b20),
    b24 ^^^ ((~~~b20) &&& b21)⟩

@[noinline] def rounds6Lo0Fast (s : State25) : State25 :=
  let s := round25Fast s 0x0000000000000001
  let s := round25Fast s 0x0000000000008082
  let s := round25Fast s 0x800000000000808a
  let s := round25Fast s 0x8000000080008000
  let s := round25Fast s 0x000000000000808b
  round25Fast s 0x0000000080000001

@[noinline] def rounds6Lo1Fast (s : State25) : State25 :=
  let s := round25Fast s 0x8000000080008081
  let s := round25Fast s 0x8000000000008009
  let s := round25Fast s 0x000000000000008a
  let s := round25Fast s 0x0000000000000088
  let s := round25Fast s 0x0000000080008009
  round25Fast s 0x000000008000000a

@[noinline] def rounds6Hi0Fast (s : State25) : State25 :=
  let s := round25Fast s 0x000000008000808b
  let s := round25Fast s 0x800000000000008b
  let s := round25Fast s 0x8000000000008089
  let s := round25Fast s 0x8000000000008003
  let s := round25Fast s 0x8000000000008002
  round25Fast s 0x8000000000000080

@[noinline] def rounds6Hi1Fast (s : State25) : State25 :=
  let s := round25Fast s 0x000000000000800a
  let s := round25Fast s 0x800000008000000a
  let s := round25Fast s 0x8000000080008081
  let s := round25Fast s 0x8000000000008080
  let s := round25Fast s 0x0000000080000001
  round25Fast s 0x8000000080008008

@[inline] def rounds12Fast (s : State25) : State25 :=
  rounds6Lo1Fast (rounds6Lo0Fast s)

@[inline] def rounds12HiFast (s : State25) : State25 :=
  rounds6Hi1Fast (rounds6Hi0Fast s)

@[inline] def keccakF1600Fast (s : State25) : State25 :=
  rounds6Hi1Fast (rounds6Hi0Fast (rounds6Lo1Fast (rounds6Lo0Fast s)))

def zeroState25Fast : State25 :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

private theorem usizeLtSizeFast {idx : USize} {n : Nat} (h : idx < n.toUSize) :
    idx.toNat < n := by
  rw [USize.lt_iff_toNat_lt] at h
  exact Nat.lt_of_lt_of_le h (Nat.mod_le n USize.size)

private theorem usizeAddLtSizeFast {base : USize} {n : Nat} (k : Nat) (hk : k ≤ 7)
    (h0 : base ≤ base + 7) (h7 : base + 7 < n.toUSize) :
    (base + USize.ofNat k).toNat < n := by
  have h7nat : (7 : USize).toNat = 7 := by
    change (USize.ofNat 7).toNat = 7
    rw [USize.toNat_ofNat']
    rcases System.Platform.numBits_eq with h32 | h64
    · simp [h32]
    · simp [h64]
  have hknat : (USize.ofNat k).toNat = k := by
    rw [USize.toNat_ofNat']
    rcases System.Platform.numBits_eq with h32 | h64
    · simp [h32]; omega
    · simp [h64]; omega
  have hle : base.toNat ≤ (base + 7).toNat := USize.le_iff_toNat_le.mp h0
  have hlt : base.toNat < USize.size := base.toNat_lt_size
  have hsz : USize.size = 2 ^ System.Platform.numBits := rfl
  have h7sz : 7 < USize.size := by
    rw [hsz]
    rcases System.Platform.numBits_eq with h32 | h64
    · simp [h32]
    · simp [h64]
  have hadd7 : (base + 7).toNat = (base.toNat + 7) % USize.size := by
    rw [USize.toNat_add, h7nat]
  have hno : base.toNat + 7 < USize.size := by
    cases Nat.lt_or_ge (base.toNat + 7) USize.size with
    | inl h => exact h
    | inr hge =>
      have hmod : (base.toNat + 7) % USize.size = base.toNat + 7 - USize.size := by
        rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
      omega
  have hb7 : (base + 7).toNat = base.toNat + 7 := by
    rw [hadd7, Nat.mod_eq_of_lt hno]
  have hbk : (base + USize.ofNat k).toNat = base.toNat + k := by
    rw [USize.toNat_add, hknat, Nat.mod_eq_of_lt (by omega)]
  have h7s : (base + 7).toNat < n := usizeLtSizeFast h7
  omega

@[inline] def readU64USizeLE (b : @& ByteArray) (base : USize) : UInt64 :=
  if h7 : base + 7 < b.usize then
    if h0 : base ≤ base + 7 then
      let b0 := b.uget (base + 0) (usizeAddLtSizeFast 0 (by decide) h0 h7)
      let b1 := b.uget (base + 1) (usizeAddLtSizeFast 1 (by decide) h0 h7)
      let b2 := b.uget (base + 2) (usizeAddLtSizeFast 2 (by decide) h0 h7)
      let b3 := b.uget (base + 3) (usizeAddLtSizeFast 3 (by decide) h0 h7)
      let b4 := b.uget (base + 4) (usizeAddLtSizeFast 4 (by decide) h0 h7)
      let b5 := b.uget (base + 5) (usizeAddLtSizeFast 5 (by decide) h0 h7)
      let b6 := b.uget (base + 6) (usizeAddLtSizeFast 6 (by decide) h0 h7)
      let b7 := b.uget (base + 7) (usizeLtSizeFast h7)
      b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) ||| (b3.toUInt64 <<< 24) |||
        (b4.toUInt64 <<< 32) ||| (b5.toUInt64 <<< 40) ||| (b6.toUInt64 <<< 48) ||| (b7.toUInt64 <<< 56)
    else 0
  else 0

@[inline] def readU64BytesLE (b : @& ByteArray) (offset : Nat) : UInt64 :=
  if offset + 7 < b.size then
    readU64USizeLE b offset.toUSize
  else
    (b[offset]?.getD 0).toUInt64 |||
      ((b[offset + 1]?.getD 0).toUInt64 <<< 8) |||
      ((b[offset + 2]?.getD 0).toUInt64 <<< 16) |||
      ((b[offset + 3]?.getD 0).toUInt64 <<< 24) |||
      ((b[offset + 4]?.getD 0).toUInt64 <<< 32) |||
      ((b[offset + 5]?.getD 0).toUInt64 <<< 40) |||
      ((b[offset + 6]?.getD 0).toUInt64 <<< 48) |||
      ((b[offset + 7]?.getD 0).toUInt64 <<< 56)

@[inline] def pushU64BytesLE (bytes : ByteArray) (w : UInt64) : ByteArray :=
  bytes.push w.toUInt8
    |>.push (w >>> 8).toUInt8
    |>.push (w >>> 16).toUInt8
    |>.push (w >>> 24).toUInt8
    |>.push (w >>> 32).toUInt8
    |>.push (w >>> 40).toUInt8
    |>.push (w >>> 48).toUInt8
    |>.push (w >>> 56).toUInt8

@[inline] def absorb25Fast (s : State25) (b : @& ByteArray) (base : Nat) : State25 :=
  if base + 135 < b.size then
    let u := base.toUSize
    keccakF1600Fast
      { s with
        a00 := s.a00 ^^^ readU64USizeLE b u
        a01 := s.a01 ^^^ readU64USizeLE b (u + 8)
        a02 := s.a02 ^^^ readU64USizeLE b (u + 16)
        a03 := s.a03 ^^^ readU64USizeLE b (u + 24)
        a04 := s.a04 ^^^ readU64USizeLE b (u + 32)
        a05 := s.a05 ^^^ readU64USizeLE b (u + 40)
        a06 := s.a06 ^^^ readU64USizeLE b (u + 48)
        a07 := s.a07 ^^^ readU64USizeLE b (u + 56)
        a08 := s.a08 ^^^ readU64USizeLE b (u + 64)
        a09 := s.a09 ^^^ readU64USizeLE b (u + 72)
        a10 := s.a10 ^^^ readU64USizeLE b (u + 80)
        a11 := s.a11 ^^^ readU64USizeLE b (u + 88)
        a12 := s.a12 ^^^ readU64USizeLE b (u + 96)
        a13 := s.a13 ^^^ readU64USizeLE b (u + 104)
        a14 := s.a14 ^^^ readU64USizeLE b (u + 112)
        a15 := s.a15 ^^^ readU64USizeLE b (u + 120)
        a16 := s.a16 ^^^ readU64USizeLE b (u + 128) }
  else
    keccakF1600Fast
      { s with
        a00 := s.a00 ^^^ readU64BytesLE b base
        a01 := s.a01 ^^^ readU64BytesLE b (base + 8)
        a02 := s.a02 ^^^ readU64BytesLE b (base + 16)
        a03 := s.a03 ^^^ readU64BytesLE b (base + 24)
        a04 := s.a04 ^^^ readU64BytesLE b (base + 32)
        a05 := s.a05 ^^^ readU64BytesLE b (base + 40)
        a06 := s.a06 ^^^ readU64BytesLE b (base + 48)
        a07 := s.a07 ^^^ readU64BytesLE b (base + 56)
        a08 := s.a08 ^^^ readU64BytesLE b (base + 64)
        a09 := s.a09 ^^^ readU64BytesLE b (base + 72)
        a10 := s.a10 ^^^ readU64BytesLE b (base + 80)
        a11 := s.a11 ^^^ readU64BytesLE b (base + 88)
        a12 := s.a12 ^^^ readU64BytesLE b (base + 96)
        a13 := s.a13 ^^^ readU64BytesLE b (base + 104)
        a14 := s.a14 ^^^ readU64BytesLE b (base + 112)
        a15 := s.a15 ^^^ readU64BytesLE b (base + 120)
        a16 := s.a16 ^^^ readU64BytesLE b (base + 128) }

def keccak256FastStream (b : @& ByteArray) : ByteArray := Id.run do
  let nFull := b.size / 136
  let mut st := zeroState25Fast
  for i in [:nFull] do
    st := absorb25Fast st b (136 * i)
  let tail := b.extract (136 * nFull) b.size
  let blk := Spec.Keccak.finalBlock tail 1
  let stFinal := absorb25Fast st blk 0
  let out := ByteArray.emptyWithCapacity 32
  let out := pushU64BytesLE out stFinal.a00
  let out := pushU64BytesLE out stFinal.a01
  let out := pushU64BytesLE out stFinal.a02
  return pushU64BytesLE out stFinal.a03

end LeanVmXmss.Model.Keccak
