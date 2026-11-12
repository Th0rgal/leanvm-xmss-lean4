import Spec.Keccak.Basic

namespace LeanVmXmss.Model.Keccak

structure State25 where
  a00 : UInt64
  a01 : UInt64
  a02 : UInt64
  a03 : UInt64
  a04 : UInt64
  a05 : UInt64
  a06 : UInt64
  a07 : UInt64
  a08 : UInt64
  a09 : UInt64
  a10 : UInt64
  a11 : UInt64
  a12 : UInt64
  a13 : UInt64
  a14 : UInt64
  a15 : UInt64
  a16 : UInt64
  a17 : UInt64
  a18 : UInt64
  a19 : UInt64
  a20 : UInt64
  a21 : UInt64
  a22 : UInt64
  a23 : UInt64
  a24 : UInt64
  deriving Repr, DecidableEq

instance : BEq State25 where
  beq a b := a.a00.toNat == b.a00.toNat && a.a01.toNat == b.a01.toNat &&
    a.a02.toNat == b.a02.toNat && a.a03.toNat == b.a03.toNat && a.a04.toNat == b.a04.toNat &&
    a.a05.toNat == b.a05.toNat && a.a06.toNat == b.a06.toNat && a.a07.toNat == b.a07.toNat &&
    a.a08.toNat == b.a08.toNat && a.a09.toNat == b.a09.toNat && a.a10.toNat == b.a10.toNat &&
    a.a11.toNat == b.a11.toNat && a.a12.toNat == b.a12.toNat && a.a13.toNat == b.a13.toNat &&
    a.a14.toNat == b.a14.toNat && a.a15.toNat == b.a15.toNat && a.a16.toNat == b.a16.toNat &&
    a.a17.toNat == b.a17.toNat && a.a18.toNat == b.a18.toNat && a.a19.toNat == b.a19.toNat &&
    a.a20.toNat == b.a20.toNat && a.a21.toNat == b.a21.toNat && a.a22.toNat == b.a22.toNat &&
    a.a23.toNat == b.a23.toNat && a.a24.toNat == b.a24.toNat

def State25.toSpec (s : State25) : Spec.Keccak.State :=
  #[s.a00, s.a01, s.a02, s.a03, s.a04,
    s.a05, s.a06, s.a07, s.a08, s.a09,
    s.a10, s.a11, s.a12, s.a13, s.a14,
    s.a15, s.a16, s.a17, s.a18, s.a19,
    s.a20, s.a21, s.a22, s.a23, s.a24]

def State25.fromSpec (s : Spec.Keccak.State) : State25 :=
  ⟨s[0]!, s[1]!, s[2]!, s[3]!, s[4]!,
    s[5]!, s[6]!, s[7]!, s[8]!, s[9]!,
    s[10]!, s[11]!, s[12]!, s[13]!, s[14]!,
    s[15]!, s[16]!, s[17]!, s[18]!, s[19]!,
    s[20]!, s[21]!, s[22]!, s[23]!, s[24]!⟩

def round25 (s : State25) (rc : UInt64) : State25 :=
  let c0 := s.a00 ^^^ s.a05 ^^^ s.a10 ^^^ s.a15 ^^^ s.a20
  let c1 := s.a01 ^^^ s.a06 ^^^ s.a11 ^^^ s.a16 ^^^ s.a21
  let c2 := s.a02 ^^^ s.a07 ^^^ s.a12 ^^^ s.a17 ^^^ s.a22
  let c3 := s.a03 ^^^ s.a08 ^^^ s.a13 ^^^ s.a18 ^^^ s.a23
  let c4 := s.a04 ^^^ s.a09 ^^^ s.a14 ^^^ s.a19 ^^^ s.a24
  let b00 := Spec.Keccak.rotl (s.a00 ^^^ c4 ^^^ Spec.Keccak.rotl c1 1) 0
  let b10 := Spec.Keccak.rotl (s.a01 ^^^ c0 ^^^ Spec.Keccak.rotl c2 1) 1
  let b20 := Spec.Keccak.rotl (s.a02 ^^^ c1 ^^^ Spec.Keccak.rotl c3 1) 62
  let b05 := Spec.Keccak.rotl (s.a03 ^^^ c2 ^^^ Spec.Keccak.rotl c4 1) 28
  let b15 := Spec.Keccak.rotl (s.a04 ^^^ c3 ^^^ Spec.Keccak.rotl c0 1) 27
  let b16 := Spec.Keccak.rotl (s.a05 ^^^ c4 ^^^ Spec.Keccak.rotl c1 1) 36
  let b01 := Spec.Keccak.rotl (s.a06 ^^^ c0 ^^^ Spec.Keccak.rotl c2 1) 44
  let b11 := Spec.Keccak.rotl (s.a07 ^^^ c1 ^^^ Spec.Keccak.rotl c3 1) 6
  let b21 := Spec.Keccak.rotl (s.a08 ^^^ c2 ^^^ Spec.Keccak.rotl c4 1) 55
  let b06 := Spec.Keccak.rotl (s.a09 ^^^ c3 ^^^ Spec.Keccak.rotl c0 1) 20
  let b07 := Spec.Keccak.rotl (s.a10 ^^^ c4 ^^^ Spec.Keccak.rotl c1 1) 3
  let b17 := Spec.Keccak.rotl (s.a11 ^^^ c0 ^^^ Spec.Keccak.rotl c2 1) 10
  let b02 := Spec.Keccak.rotl (s.a12 ^^^ c1 ^^^ Spec.Keccak.rotl c3 1) 43
  let b12 := Spec.Keccak.rotl (s.a13 ^^^ c2 ^^^ Spec.Keccak.rotl c4 1) 25
  let b22 := Spec.Keccak.rotl (s.a14 ^^^ c3 ^^^ Spec.Keccak.rotl c0 1) 39
  let b23 := Spec.Keccak.rotl (s.a15 ^^^ c4 ^^^ Spec.Keccak.rotl c1 1) 41
  let b08 := Spec.Keccak.rotl (s.a16 ^^^ c0 ^^^ Spec.Keccak.rotl c2 1) 45
  let b18 := Spec.Keccak.rotl (s.a17 ^^^ c1 ^^^ Spec.Keccak.rotl c3 1) 15
  let b03 := Spec.Keccak.rotl (s.a18 ^^^ c2 ^^^ Spec.Keccak.rotl c4 1) 21
  let b13 := Spec.Keccak.rotl (s.a19 ^^^ c3 ^^^ Spec.Keccak.rotl c0 1) 8
  let b14 := Spec.Keccak.rotl (s.a20 ^^^ c4 ^^^ Spec.Keccak.rotl c1 1) 18
  let b24 := Spec.Keccak.rotl (s.a21 ^^^ c0 ^^^ Spec.Keccak.rotl c2 1) 2
  let b09 := Spec.Keccak.rotl (s.a22 ^^^ c1 ^^^ Spec.Keccak.rotl c3 1) 61
  let b19 := Spec.Keccak.rotl (s.a23 ^^^ c2 ^^^ Spec.Keccak.rotl c4 1) 56
  let b04 := Spec.Keccak.rotl (s.a24 ^^^ c3 ^^^ Spec.Keccak.rotl c0 1) 14
  ⟨(b00 ^^^ ((~~~b01) &&& b02)) ^^^ rc,
    (b01 ^^^ ((~~~b02) &&& b03)),
    (b02 ^^^ ((~~~b03) &&& b04)),
    (b03 ^^^ ((~~~b04) &&& b00)),
    (b04 ^^^ ((~~~b00) &&& b01)),
    (b05 ^^^ ((~~~b06) &&& b07)),
    (b06 ^^^ ((~~~b07) &&& b08)),
    (b07 ^^^ ((~~~b08) &&& b09)),
    (b08 ^^^ ((~~~b09) &&& b05)),
    (b09 ^^^ ((~~~b05) &&& b06)),
    (b10 ^^^ ((~~~b11) &&& b12)),
    (b11 ^^^ ((~~~b12) &&& b13)),
    (b12 ^^^ ((~~~b13) &&& b14)),
    (b13 ^^^ ((~~~b14) &&& b10)),
    (b14 ^^^ ((~~~b10) &&& b11)),
    (b15 ^^^ ((~~~b16) &&& b17)),
    (b16 ^^^ ((~~~b17) &&& b18)),
    (b17 ^^^ ((~~~b18) &&& b19)),
    (b18 ^^^ ((~~~b19) &&& b15)),
    (b19 ^^^ ((~~~b15) &&& b16)),
    (b20 ^^^ ((~~~b21) &&& b22)),
    (b21 ^^^ ((~~~b22) &&& b23)),
    (b22 ^^^ ((~~~b23) &&& b24)),
    (b23 ^^^ ((~~~b24) &&& b20)),
    (b24 ^^^ ((~~~b20) &&& b21))⟩

@[export shard_b_keccak_lane_00]
def lane00 (a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 rc : UInt64) : UInt64 :=
  let c0 := a00 ^^^ a05 ^^^ a10 ^^^ a15 ^^^ a20
  let c1 := a01 ^^^ a06 ^^^ a11 ^^^ a16 ^^^ a21
  let c2 := a02 ^^^ a07 ^^^ a12 ^^^ a17 ^^^ a22
  let c3 := a03 ^^^ a08 ^^^ a13 ^^^ a18 ^^^ a23
  let c4 := a04 ^^^ a09 ^^^ a14 ^^^ a19 ^^^ a24
  let b00 := (a00 ^^^ c4 ^^^ ((c1 <<< 1) ||| (c1 >>> 63)))
  let b01 := (((a06 ^^^ c0 ^^^ ((c2 <<< 1) ||| (c2 >>> 63))) <<< 44) ||| ((a06 ^^^ c0 ^^^ ((c2 <<< 1) ||| (c2 >>> 63))) >>> 20))
  let b02 := (((a12 ^^^ c1 ^^^ ((c3 <<< 1) ||| (c3 >>> 63))) <<< 43) ||| ((a12 ^^^ c1 ^^^ ((c3 <<< 1) ||| (c3 >>> 63))) >>> 21))
  (b00 ^^^ ((~~~b01) &&& b02)) ^^^ rc

@[export shard_b_keccak_lane_01]
def lane01 (a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 _rc : UInt64) : UInt64 :=
  let c0 := a00 ^^^ a05 ^^^ a10 ^^^ a15 ^^^ a20
  let c1 := a01 ^^^ a06 ^^^ a11 ^^^ a16 ^^^ a21
  let c2 := a02 ^^^ a07 ^^^ a12 ^^^ a17 ^^^ a22
  let c3 := a03 ^^^ a08 ^^^ a13 ^^^ a18 ^^^ a23
  let c4 := a04 ^^^ a09 ^^^ a14 ^^^ a19 ^^^ a24
  let b01 := (((a06 ^^^ c0 ^^^ ((c2 <<< 1) ||| (c2 >>> 63))) <<< 44) ||| ((a06 ^^^ c0 ^^^ ((c2 <<< 1) ||| (c2 >>> 63))) >>> 20))
  let b02 := (((a12 ^^^ c1 ^^^ ((c3 <<< 1) ||| (c3 >>> 63))) <<< 43) ||| ((a12 ^^^ c1 ^^^ ((c3 <<< 1) ||| (c3 >>> 63))) >>> 21))
  let b03 := (((a18 ^^^ c2 ^^^ ((c4 <<< 1) ||| (c4 >>> 63))) <<< 21) ||| ((a18 ^^^ c2 ^^^ ((c4 <<< 1) ||| (c4 >>> 63))) >>> 43))
  (b01 ^^^ ((~~~b02) &&& b03))

@[export shard_b_keccak_lane_02]
def lane02 (a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 _rc : UInt64) : UInt64 :=
  let c0 := a00 ^^^ a05 ^^^ a10 ^^^ a15 ^^^ a20
  let c1 := a01 ^^^ a06 ^^^ a11 ^^^ a16 ^^^ a21
  let c2 := a02 ^^^ a07 ^^^ a12 ^^^ a17 ^^^ a22
  let c3 := a03 ^^^ a08 ^^^ a13 ^^^ a18 ^^^ a23
  let c4 := a04 ^^^ a09 ^^^ a14 ^^^ a19 ^^^ a24
  let b02 := (((a12 ^^^ c1 ^^^ ((c3 <<< 1) ||| (c3 >>> 63))) <<< 43) ||| ((a12 ^^^ c1 ^^^ ((c3 <<< 1) ||| (c3 >>> 63))) >>> 21))
  let b03 := (((a18 ^^^ c2 ^^^ ((c4 <<< 1) ||| (c4 >>> 63))) <<< 21) ||| ((a18 ^^^ c2 ^^^ ((c4 <<< 1) ||| (c4 >>> 63))) >>> 43))
  let b04 := (((a24 ^^^ c3 ^^^ ((c0 <<< 1) ||| (c0 >>> 63))) <<< 14) ||| ((a24 ^^^ c3 ^^^ ((c0 <<< 1) ||| (c0 >>> 63))) >>> 50))
  (b02 ^^^ ((~~~b03) &&& b04))

@[export shard_b_keccak_lane_03]
def lane03 (a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 _rc : UInt64) : UInt64 :=
  let c0 := a00 ^^^ a05 ^^^ a10 ^^^ a15 ^^^ a20
  let c1 := a01 ^^^ a06 ^^^ a11 ^^^ a16 ^^^ a21
  let c2 := a02 ^^^ a07 ^^^ a12 ^^^ a17 ^^^ a22
  let c3 := a03 ^^^ a08 ^^^ a13 ^^^ a18 ^^^ a23
  let c4 := a04 ^^^ a09 ^^^ a14 ^^^ a19 ^^^ a24
  let b00 := (a00 ^^^ c4 ^^^ ((c1 <<< 1) ||| (c1 >>> 63)))
  let b03 := (((a18 ^^^ c2 ^^^ ((c4 <<< 1) ||| (c4 >>> 63))) <<< 21) ||| ((a18 ^^^ c2 ^^^ ((c4 <<< 1) ||| (c4 >>> 63))) >>> 43))
  let b04 := (((a24 ^^^ c3 ^^^ ((c0 <<< 1) ||| (c0 >>> 63))) <<< 14) ||| ((a24 ^^^ c3 ^^^ ((c0 <<< 1) ||| (c0 >>> 63))) >>> 50))
  (b03 ^^^ ((~~~b04) &&& b00))

@[export shard_b_keccak_lane_04]
def lane04 (a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 _rc : UInt64) : UInt64 :=
  let c0 := a00 ^^^ a05 ^^^ a10 ^^^ a15 ^^^ a20
  let c1 := a01 ^^^ a06 ^^^ a11 ^^^ a16 ^^^ a21
  let c2 := a02 ^^^ a07 ^^^ a12 ^^^ a17 ^^^ a22
  let c3 := a03 ^^^ a08 ^^^ a13 ^^^ a18 ^^^ a23
  let c4 := a04 ^^^ a09 ^^^ a14 ^^^ a19 ^^^ a24
  let b00 := (a00 ^^^ c4 ^^^ ((c1 <<< 1) ||| (c1 >>> 63)))
  let b01 := (((a06 ^^^ c0 ^^^ ((c2 <<< 1) ||| (c2 >>> 63))) <<< 44) ||| ((a06 ^^^ c0 ^^^ ((c2 <<< 1) ||| (c2 >>> 63))) >>> 20))
  let b04 := (((a24 ^^^ c3 ^^^ ((c0 <<< 1) ||| (c0 >>> 63))) <<< 14) ||| ((a24 ^^^ c3 ^^^ ((c0 <<< 1) ||| (c0 >>> 63))) >>> 50))
  (b04 ^^^ ((~~~b00) &&& b01))

@[export shard_b_keccak_lane_05]
def lane05 (a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 _rc : UInt64) : UInt64 :=
  let c0 := a00 ^^^ a05 ^^^ a10 ^^^ a15 ^^^ a20
  let c1 := a01 ^^^ a06 ^^^ a11 ^^^ a16 ^^^ a21
  let c2 := a02 ^^^ a07 ^^^ a12 ^^^ a17 ^^^ a22
  let c3 := a03 ^^^ a08 ^^^ a13 ^^^ a18 ^^^ a23
  let c4 := a04 ^^^ a09 ^^^ a14 ^^^ a19 ^^^ a24
  let b05 := (((a03 ^^^ c2 ^^^ ((c4 <<< 1) ||| (c4 >>> 63))) <<< 28) ||| ((a03 ^^^ c2 ^^^ ((c4 <<< 1) ||| (c4 >>> 63))) >>> 36))
  let b06 := (((a09 ^^^ c3 ^^^ ((c0 <<< 1) ||| (c0 >>> 63))) <<< 20) ||| ((a09 ^^^ c3 ^^^ ((c0 <<< 1) ||| (c0 >>> 63))) >>> 44))
  let b07 := (((a10 ^^^ c4 ^^^ ((c1 <<< 1) ||| (c1 >>> 63))) <<< 3) ||| ((a10 ^^^ c4 ^^^ ((c1 <<< 1) ||| (c1 >>> 63))) >>> 61))
  (b05 ^^^ ((~~~b06) &&& b07))

@[export shard_b_keccak_lane_06]
def lane06 (a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 _rc : UInt64) : UInt64 :=
  let c0 := a00 ^^^ a05 ^^^ a10 ^^^ a15 ^^^ a20
  let c1 := a01 ^^^ a06 ^^^ a11 ^^^ a16 ^^^ a21
  let c2 := a02 ^^^ a07 ^^^ a12 ^^^ a17 ^^^ a22
  let c3 := a03 ^^^ a08 ^^^ a13 ^^^ a18 ^^^ a23
  let c4 := a04 ^^^ a09 ^^^ a14 ^^^ a19 ^^^ a24
  let b06 := (((a09 ^^^ c3 ^^^ ((c0 <<< 1) ||| (c0 >>> 63))) <<< 20) ||| ((a09 ^^^ c3 ^^^ ((c0 <<< 1) ||| (c0 >>> 63))) >>> 44))
  let b07 := (((a10 ^^^ c4 ^^^ ((c1 <<< 1) ||| (c1 >>> 63))) <<< 3) ||| ((a10 ^^^ c4 ^^^ ((c1 <<< 1) ||| (c1 >>> 63))) >>> 61))
  let b08 := (((a16 ^^^ c0 ^^^ ((c2 <<< 1) ||| (c2 >>> 63))) <<< 45) ||| ((a16 ^^^ c0 ^^^ ((c2 <<< 1) ||| (c2 >>> 63))) >>> 19))
  (b06 ^^^ ((~~~b07) &&& b08))

@[export shard_b_keccak_lane_07]
def lane07 (a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 _rc : UInt64) : UInt64 :=
  let c0 := a00 ^^^ a05 ^^^ a10 ^^^ a15 ^^^ a20
  let c1 := a01 ^^^ a06 ^^^ a11 ^^^ a16 ^^^ a21
  let c2 := a02 ^^^ a07 ^^^ a12 ^^^ a17 ^^^ a22
  let c3 := a03 ^^^ a08 ^^^ a13 ^^^ a18 ^^^ a23
  let c4 := a04 ^^^ a09 ^^^ a14 ^^^ a19 ^^^ a24
  let b07 := (((a10 ^^^ c4 ^^^ ((c1 <<< 1) ||| (c1 >>> 63))) <<< 3) ||| ((a10 ^^^ c4 ^^^ ((c1 <<< 1) ||| (c1 >>> 63))) >>> 61))
  let b08 := (((a16 ^^^ c0 ^^^ ((c2 <<< 1) ||| (c2 >>> 63))) <<< 45) ||| ((a16 ^^^ c0 ^^^ ((c2 <<< 1) ||| (c2 >>> 63))) >>> 19))
  let b09 := (((a22 ^^^ c1 ^^^ ((c3 <<< 1) ||| (c3 >>> 63))) <<< 61) ||| ((a22 ^^^ c1 ^^^ ((c3 <<< 1) ||| (c3 >>> 63))) >>> 3))
  (b07 ^^^ ((~~~b08) &&& b09))

@[export shard_b_keccak_lane_08]
def lane08 (a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 _rc : UInt64) : UInt64 :=
  let c0 := a00 ^^^ a05 ^^^ a10 ^^^ a15 ^^^ a20
  let c1 := a01 ^^^ a06 ^^^ a11 ^^^ a16 ^^^ a21
  let c2 := a02 ^^^ a07 ^^^ a12 ^^^ a17 ^^^ a22
  let c3 := a03 ^^^ a08 ^^^ a13 ^^^ a18 ^^^ a23
  let c4 := a04 ^^^ a09 ^^^ a14 ^^^ a19 ^^^ a24
  let b05 := (((a03 ^^^ c2 ^^^ ((c4 <<< 1) ||| (c4 >>> 63))) <<< 28) ||| ((a03 ^^^ c2 ^^^ ((c4 <<< 1) ||| (c4 >>> 63))) >>> 36))
  let b08 := (((a16 ^^^ c0 ^^^ ((c2 <<< 1) ||| (c2 >>> 63))) <<< 45) ||| ((a16 ^^^ c0 ^^^ ((c2 <<< 1) ||| (c2 >>> 63))) >>> 19))
  let b09 := (((a22 ^^^ c1 ^^^ ((c3 <<< 1) ||| (c3 >>> 63))) <<< 61) ||| ((a22 ^^^ c1 ^^^ ((c3 <<< 1) ||| (c3 >>> 63))) >>> 3))
  (b08 ^^^ ((~~~b09) &&& b05))

@[export shard_b_keccak_lane_09]
def lane09 (a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 _rc : UInt64) : UInt64 :=
  let c0 := a00 ^^^ a05 ^^^ a10 ^^^ a15 ^^^ a20
  let c1 := a01 ^^^ a06 ^^^ a11 ^^^ a16 ^^^ a21
  let c2 := a02 ^^^ a07 ^^^ a12 ^^^ a17 ^^^ a22
  let c3 := a03 ^^^ a08 ^^^ a13 ^^^ a18 ^^^ a23
  let c4 := a04 ^^^ a09 ^^^ a14 ^^^ a19 ^^^ a24
  let b05 := (((a03 ^^^ c2 ^^^ ((c4 <<< 1) ||| (c4 >>> 63))) <<< 28) ||| ((a03 ^^^ c2 ^^^ ((c4 <<< 1) ||| (c4 >>> 63))) >>> 36))
  let b06 := (((a09 ^^^ c3 ^^^ ((c0 <<< 1) ||| (c0 >>> 63))) <<< 20) ||| ((a09 ^^^ c3 ^^^ ((c0 <<< 1) ||| (c0 >>> 63))) >>> 44))
  let b09 := (((a22 ^^^ c1 ^^^ ((c3 <<< 1) ||| (c3 >>> 63))) <<< 61) ||| ((a22 ^^^ c1 ^^^ ((c3 <<< 1) ||| (c3 >>> 63))) >>> 3))
  (b09 ^^^ ((~~~b05) &&& b06))

@[export shard_b_keccak_lane_10]
def lane10 (a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 _rc : UInt64) : UInt64 :=
  let c0 := a00 ^^^ a05 ^^^ a10 ^^^ a15 ^^^ a20
  let c1 := a01 ^^^ a06 ^^^ a11 ^^^ a16 ^^^ a21
  let c2 := a02 ^^^ a07 ^^^ a12 ^^^ a17 ^^^ a22
  let c3 := a03 ^^^ a08 ^^^ a13 ^^^ a18 ^^^ a23
  let c4 := a04 ^^^ a09 ^^^ a14 ^^^ a19 ^^^ a24
  let b10 := (((a01 ^^^ c0 ^^^ ((c2 <<< 1) ||| (c2 >>> 63))) <<< 1) ||| ((a01 ^^^ c0 ^^^ ((c2 <<< 1) ||| (c2 >>> 63))) >>> 63))
  let b11 := (((a07 ^^^ c1 ^^^ ((c3 <<< 1) ||| (c3 >>> 63))) <<< 6) ||| ((a07 ^^^ c1 ^^^ ((c3 <<< 1) ||| (c3 >>> 63))) >>> 58))
  let b12 := (((a13 ^^^ c2 ^^^ ((c4 <<< 1) ||| (c4 >>> 63))) <<< 25) ||| ((a13 ^^^ c2 ^^^ ((c4 <<< 1) ||| (c4 >>> 63))) >>> 39))
  (b10 ^^^ ((~~~b11) &&& b12))

@[export shard_b_keccak_lane_11]
def lane11 (a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 _rc : UInt64) : UInt64 :=
  let c0 := a00 ^^^ a05 ^^^ a10 ^^^ a15 ^^^ a20
  let c1 := a01 ^^^ a06 ^^^ a11 ^^^ a16 ^^^ a21
  let c2 := a02 ^^^ a07 ^^^ a12 ^^^ a17 ^^^ a22
  let c3 := a03 ^^^ a08 ^^^ a13 ^^^ a18 ^^^ a23
  let c4 := a04 ^^^ a09 ^^^ a14 ^^^ a19 ^^^ a24
  let b11 := (((a07 ^^^ c1 ^^^ ((c3 <<< 1) ||| (c3 >>> 63))) <<< 6) ||| ((a07 ^^^ c1 ^^^ ((c3 <<< 1) ||| (c3 >>> 63))) >>> 58))
  let b12 := (((a13 ^^^ c2 ^^^ ((c4 <<< 1) ||| (c4 >>> 63))) <<< 25) ||| ((a13 ^^^ c2 ^^^ ((c4 <<< 1) ||| (c4 >>> 63))) >>> 39))
  let b13 := (((a19 ^^^ c3 ^^^ ((c0 <<< 1) ||| (c0 >>> 63))) <<< 8) ||| ((a19 ^^^ c3 ^^^ ((c0 <<< 1) ||| (c0 >>> 63))) >>> 56))
  (b11 ^^^ ((~~~b12) &&& b13))

@[export shard_b_keccak_lane_12]
def lane12 (a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 _rc : UInt64) : UInt64 :=
  let c0 := a00 ^^^ a05 ^^^ a10 ^^^ a15 ^^^ a20
  let c1 := a01 ^^^ a06 ^^^ a11 ^^^ a16 ^^^ a21
  let c2 := a02 ^^^ a07 ^^^ a12 ^^^ a17 ^^^ a22
  let c3 := a03 ^^^ a08 ^^^ a13 ^^^ a18 ^^^ a23
  let c4 := a04 ^^^ a09 ^^^ a14 ^^^ a19 ^^^ a24
  let b12 := (((a13 ^^^ c2 ^^^ ((c4 <<< 1) ||| (c4 >>> 63))) <<< 25) ||| ((a13 ^^^ c2 ^^^ ((c4 <<< 1) ||| (c4 >>> 63))) >>> 39))
  let b13 := (((a19 ^^^ c3 ^^^ ((c0 <<< 1) ||| (c0 >>> 63))) <<< 8) ||| ((a19 ^^^ c3 ^^^ ((c0 <<< 1) ||| (c0 >>> 63))) >>> 56))
  let b14 := (((a20 ^^^ c4 ^^^ ((c1 <<< 1) ||| (c1 >>> 63))) <<< 18) ||| ((a20 ^^^ c4 ^^^ ((c1 <<< 1) ||| (c1 >>> 63))) >>> 46))
  (b12 ^^^ ((~~~b13) &&& b14))

@[export shard_b_keccak_lane_13]
def lane13 (a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 _rc : UInt64) : UInt64 :=
  let c0 := a00 ^^^ a05 ^^^ a10 ^^^ a15 ^^^ a20
  let c1 := a01 ^^^ a06 ^^^ a11 ^^^ a16 ^^^ a21
  let c2 := a02 ^^^ a07 ^^^ a12 ^^^ a17 ^^^ a22
  let c3 := a03 ^^^ a08 ^^^ a13 ^^^ a18 ^^^ a23
  let c4 := a04 ^^^ a09 ^^^ a14 ^^^ a19 ^^^ a24
  let b10 := (((a01 ^^^ c0 ^^^ ((c2 <<< 1) ||| (c2 >>> 63))) <<< 1) ||| ((a01 ^^^ c0 ^^^ ((c2 <<< 1) ||| (c2 >>> 63))) >>> 63))
  let b13 := (((a19 ^^^ c3 ^^^ ((c0 <<< 1) ||| (c0 >>> 63))) <<< 8) ||| ((a19 ^^^ c3 ^^^ ((c0 <<< 1) ||| (c0 >>> 63))) >>> 56))
  let b14 := (((a20 ^^^ c4 ^^^ ((c1 <<< 1) ||| (c1 >>> 63))) <<< 18) ||| ((a20 ^^^ c4 ^^^ ((c1 <<< 1) ||| (c1 >>> 63))) >>> 46))
  (b13 ^^^ ((~~~b14) &&& b10))

@[export shard_b_keccak_lane_14]
def lane14 (a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 _rc : UInt64) : UInt64 :=
  let c0 := a00 ^^^ a05 ^^^ a10 ^^^ a15 ^^^ a20
  let c1 := a01 ^^^ a06 ^^^ a11 ^^^ a16 ^^^ a21
  let c2 := a02 ^^^ a07 ^^^ a12 ^^^ a17 ^^^ a22
  let c3 := a03 ^^^ a08 ^^^ a13 ^^^ a18 ^^^ a23
  let c4 := a04 ^^^ a09 ^^^ a14 ^^^ a19 ^^^ a24
  let b10 := (((a01 ^^^ c0 ^^^ ((c2 <<< 1) ||| (c2 >>> 63))) <<< 1) ||| ((a01 ^^^ c0 ^^^ ((c2 <<< 1) ||| (c2 >>> 63))) >>> 63))
  let b11 := (((a07 ^^^ c1 ^^^ ((c3 <<< 1) ||| (c3 >>> 63))) <<< 6) ||| ((a07 ^^^ c1 ^^^ ((c3 <<< 1) ||| (c3 >>> 63))) >>> 58))
  let b14 := (((a20 ^^^ c4 ^^^ ((c1 <<< 1) ||| (c1 >>> 63))) <<< 18) ||| ((a20 ^^^ c4 ^^^ ((c1 <<< 1) ||| (c1 >>> 63))) >>> 46))
  (b14 ^^^ ((~~~b10) &&& b11))

@[export shard_b_keccak_lane_15]
def lane15 (a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 _rc : UInt64) : UInt64 :=
  let c0 := a00 ^^^ a05 ^^^ a10 ^^^ a15 ^^^ a20
  let c1 := a01 ^^^ a06 ^^^ a11 ^^^ a16 ^^^ a21
  let c2 := a02 ^^^ a07 ^^^ a12 ^^^ a17 ^^^ a22
  let c3 := a03 ^^^ a08 ^^^ a13 ^^^ a18 ^^^ a23
  let c4 := a04 ^^^ a09 ^^^ a14 ^^^ a19 ^^^ a24
  let b15 := (((a04 ^^^ c3 ^^^ ((c0 <<< 1) ||| (c0 >>> 63))) <<< 27) ||| ((a04 ^^^ c3 ^^^ ((c0 <<< 1) ||| (c0 >>> 63))) >>> 37))
  let b16 := (((a05 ^^^ c4 ^^^ ((c1 <<< 1) ||| (c1 >>> 63))) <<< 36) ||| ((a05 ^^^ c4 ^^^ ((c1 <<< 1) ||| (c1 >>> 63))) >>> 28))
  let b17 := (((a11 ^^^ c0 ^^^ ((c2 <<< 1) ||| (c2 >>> 63))) <<< 10) ||| ((a11 ^^^ c0 ^^^ ((c2 <<< 1) ||| (c2 >>> 63))) >>> 54))
  (b15 ^^^ ((~~~b16) &&& b17))

@[export shard_b_keccak_lane_16]
def lane16 (a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 _rc : UInt64) : UInt64 :=
  let c0 := a00 ^^^ a05 ^^^ a10 ^^^ a15 ^^^ a20
  let c1 := a01 ^^^ a06 ^^^ a11 ^^^ a16 ^^^ a21
  let c2 := a02 ^^^ a07 ^^^ a12 ^^^ a17 ^^^ a22
  let c3 := a03 ^^^ a08 ^^^ a13 ^^^ a18 ^^^ a23
  let c4 := a04 ^^^ a09 ^^^ a14 ^^^ a19 ^^^ a24
  let b16 := (((a05 ^^^ c4 ^^^ ((c1 <<< 1) ||| (c1 >>> 63))) <<< 36) ||| ((a05 ^^^ c4 ^^^ ((c1 <<< 1) ||| (c1 >>> 63))) >>> 28))
  let b17 := (((a11 ^^^ c0 ^^^ ((c2 <<< 1) ||| (c2 >>> 63))) <<< 10) ||| ((a11 ^^^ c0 ^^^ ((c2 <<< 1) ||| (c2 >>> 63))) >>> 54))
  let b18 := (((a17 ^^^ c1 ^^^ ((c3 <<< 1) ||| (c3 >>> 63))) <<< 15) ||| ((a17 ^^^ c1 ^^^ ((c3 <<< 1) ||| (c3 >>> 63))) >>> 49))
  (b16 ^^^ ((~~~b17) &&& b18))

@[export shard_b_keccak_lane_17]
def lane17 (a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 _rc : UInt64) : UInt64 :=
  let c0 := a00 ^^^ a05 ^^^ a10 ^^^ a15 ^^^ a20
  let c1 := a01 ^^^ a06 ^^^ a11 ^^^ a16 ^^^ a21
  let c2 := a02 ^^^ a07 ^^^ a12 ^^^ a17 ^^^ a22
  let c3 := a03 ^^^ a08 ^^^ a13 ^^^ a18 ^^^ a23
  let c4 := a04 ^^^ a09 ^^^ a14 ^^^ a19 ^^^ a24
  let b17 := (((a11 ^^^ c0 ^^^ ((c2 <<< 1) ||| (c2 >>> 63))) <<< 10) ||| ((a11 ^^^ c0 ^^^ ((c2 <<< 1) ||| (c2 >>> 63))) >>> 54))
  let b18 := (((a17 ^^^ c1 ^^^ ((c3 <<< 1) ||| (c3 >>> 63))) <<< 15) ||| ((a17 ^^^ c1 ^^^ ((c3 <<< 1) ||| (c3 >>> 63))) >>> 49))
  let b19 := (((a23 ^^^ c2 ^^^ ((c4 <<< 1) ||| (c4 >>> 63))) <<< 56) ||| ((a23 ^^^ c2 ^^^ ((c4 <<< 1) ||| (c4 >>> 63))) >>> 8))
  (b17 ^^^ ((~~~b18) &&& b19))

@[export shard_b_keccak_lane_18]
def lane18 (a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 _rc : UInt64) : UInt64 :=
  let c0 := a00 ^^^ a05 ^^^ a10 ^^^ a15 ^^^ a20
  let c1 := a01 ^^^ a06 ^^^ a11 ^^^ a16 ^^^ a21
  let c2 := a02 ^^^ a07 ^^^ a12 ^^^ a17 ^^^ a22
  let c3 := a03 ^^^ a08 ^^^ a13 ^^^ a18 ^^^ a23
  let c4 := a04 ^^^ a09 ^^^ a14 ^^^ a19 ^^^ a24
  let b15 := (((a04 ^^^ c3 ^^^ ((c0 <<< 1) ||| (c0 >>> 63))) <<< 27) ||| ((a04 ^^^ c3 ^^^ ((c0 <<< 1) ||| (c0 >>> 63))) >>> 37))
  let b18 := (((a17 ^^^ c1 ^^^ ((c3 <<< 1) ||| (c3 >>> 63))) <<< 15) ||| ((a17 ^^^ c1 ^^^ ((c3 <<< 1) ||| (c3 >>> 63))) >>> 49))
  let b19 := (((a23 ^^^ c2 ^^^ ((c4 <<< 1) ||| (c4 >>> 63))) <<< 56) ||| ((a23 ^^^ c2 ^^^ ((c4 <<< 1) ||| (c4 >>> 63))) >>> 8))
  (b18 ^^^ ((~~~b19) &&& b15))

@[export shard_b_keccak_lane_19]
def lane19 (a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 _rc : UInt64) : UInt64 :=
  let c0 := a00 ^^^ a05 ^^^ a10 ^^^ a15 ^^^ a20
  let c1 := a01 ^^^ a06 ^^^ a11 ^^^ a16 ^^^ a21
  let c2 := a02 ^^^ a07 ^^^ a12 ^^^ a17 ^^^ a22
  let c3 := a03 ^^^ a08 ^^^ a13 ^^^ a18 ^^^ a23
  let c4 := a04 ^^^ a09 ^^^ a14 ^^^ a19 ^^^ a24
  let b15 := (((a04 ^^^ c3 ^^^ ((c0 <<< 1) ||| (c0 >>> 63))) <<< 27) ||| ((a04 ^^^ c3 ^^^ ((c0 <<< 1) ||| (c0 >>> 63))) >>> 37))
  let b16 := (((a05 ^^^ c4 ^^^ ((c1 <<< 1) ||| (c1 >>> 63))) <<< 36) ||| ((a05 ^^^ c4 ^^^ ((c1 <<< 1) ||| (c1 >>> 63))) >>> 28))
  let b19 := (((a23 ^^^ c2 ^^^ ((c4 <<< 1) ||| (c4 >>> 63))) <<< 56) ||| ((a23 ^^^ c2 ^^^ ((c4 <<< 1) ||| (c4 >>> 63))) >>> 8))
  (b19 ^^^ ((~~~b15) &&& b16))

@[export shard_b_keccak_lane_20]
def lane20 (a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 _rc : UInt64) : UInt64 :=
  let c0 := a00 ^^^ a05 ^^^ a10 ^^^ a15 ^^^ a20
  let c1 := a01 ^^^ a06 ^^^ a11 ^^^ a16 ^^^ a21
  let c2 := a02 ^^^ a07 ^^^ a12 ^^^ a17 ^^^ a22
  let c3 := a03 ^^^ a08 ^^^ a13 ^^^ a18 ^^^ a23
  let c4 := a04 ^^^ a09 ^^^ a14 ^^^ a19 ^^^ a24
  let b20 := (((a02 ^^^ c1 ^^^ ((c3 <<< 1) ||| (c3 >>> 63))) <<< 62) ||| ((a02 ^^^ c1 ^^^ ((c3 <<< 1) ||| (c3 >>> 63))) >>> 2))
  let b21 := (((a08 ^^^ c2 ^^^ ((c4 <<< 1) ||| (c4 >>> 63))) <<< 55) ||| ((a08 ^^^ c2 ^^^ ((c4 <<< 1) ||| (c4 >>> 63))) >>> 9))
  let b22 := (((a14 ^^^ c3 ^^^ ((c0 <<< 1) ||| (c0 >>> 63))) <<< 39) ||| ((a14 ^^^ c3 ^^^ ((c0 <<< 1) ||| (c0 >>> 63))) >>> 25))
  (b20 ^^^ ((~~~b21) &&& b22))

@[export shard_b_keccak_lane_21]
def lane21 (a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 _rc : UInt64) : UInt64 :=
  let c0 := a00 ^^^ a05 ^^^ a10 ^^^ a15 ^^^ a20
  let c1 := a01 ^^^ a06 ^^^ a11 ^^^ a16 ^^^ a21
  let c2 := a02 ^^^ a07 ^^^ a12 ^^^ a17 ^^^ a22
  let c3 := a03 ^^^ a08 ^^^ a13 ^^^ a18 ^^^ a23
  let c4 := a04 ^^^ a09 ^^^ a14 ^^^ a19 ^^^ a24
  let b21 := (((a08 ^^^ c2 ^^^ ((c4 <<< 1) ||| (c4 >>> 63))) <<< 55) ||| ((a08 ^^^ c2 ^^^ ((c4 <<< 1) ||| (c4 >>> 63))) >>> 9))
  let b22 := (((a14 ^^^ c3 ^^^ ((c0 <<< 1) ||| (c0 >>> 63))) <<< 39) ||| ((a14 ^^^ c3 ^^^ ((c0 <<< 1) ||| (c0 >>> 63))) >>> 25))
  let b23 := (((a15 ^^^ c4 ^^^ ((c1 <<< 1) ||| (c1 >>> 63))) <<< 41) ||| ((a15 ^^^ c4 ^^^ ((c1 <<< 1) ||| (c1 >>> 63))) >>> 23))
  (b21 ^^^ ((~~~b22) &&& b23))

@[export shard_b_keccak_lane_22]
def lane22 (a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 _rc : UInt64) : UInt64 :=
  let c0 := a00 ^^^ a05 ^^^ a10 ^^^ a15 ^^^ a20
  let c1 := a01 ^^^ a06 ^^^ a11 ^^^ a16 ^^^ a21
  let c2 := a02 ^^^ a07 ^^^ a12 ^^^ a17 ^^^ a22
  let c3 := a03 ^^^ a08 ^^^ a13 ^^^ a18 ^^^ a23
  let c4 := a04 ^^^ a09 ^^^ a14 ^^^ a19 ^^^ a24
  let b22 := (((a14 ^^^ c3 ^^^ ((c0 <<< 1) ||| (c0 >>> 63))) <<< 39) ||| ((a14 ^^^ c3 ^^^ ((c0 <<< 1) ||| (c0 >>> 63))) >>> 25))
  let b23 := (((a15 ^^^ c4 ^^^ ((c1 <<< 1) ||| (c1 >>> 63))) <<< 41) ||| ((a15 ^^^ c4 ^^^ ((c1 <<< 1) ||| (c1 >>> 63))) >>> 23))
  let b24 := (((a21 ^^^ c0 ^^^ ((c2 <<< 1) ||| (c2 >>> 63))) <<< 2) ||| ((a21 ^^^ c0 ^^^ ((c2 <<< 1) ||| (c2 >>> 63))) >>> 62))
  (b22 ^^^ ((~~~b23) &&& b24))

@[export shard_b_keccak_lane_23]
def lane23 (a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 _rc : UInt64) : UInt64 :=
  let c0 := a00 ^^^ a05 ^^^ a10 ^^^ a15 ^^^ a20
  let c1 := a01 ^^^ a06 ^^^ a11 ^^^ a16 ^^^ a21
  let c2 := a02 ^^^ a07 ^^^ a12 ^^^ a17 ^^^ a22
  let c3 := a03 ^^^ a08 ^^^ a13 ^^^ a18 ^^^ a23
  let c4 := a04 ^^^ a09 ^^^ a14 ^^^ a19 ^^^ a24
  let b20 := (((a02 ^^^ c1 ^^^ ((c3 <<< 1) ||| (c3 >>> 63))) <<< 62) ||| ((a02 ^^^ c1 ^^^ ((c3 <<< 1) ||| (c3 >>> 63))) >>> 2))
  let b23 := (((a15 ^^^ c4 ^^^ ((c1 <<< 1) ||| (c1 >>> 63))) <<< 41) ||| ((a15 ^^^ c4 ^^^ ((c1 <<< 1) ||| (c1 >>> 63))) >>> 23))
  let b24 := (((a21 ^^^ c0 ^^^ ((c2 <<< 1) ||| (c2 >>> 63))) <<< 2) ||| ((a21 ^^^ c0 ^^^ ((c2 <<< 1) ||| (c2 >>> 63))) >>> 62))
  (b23 ^^^ ((~~~b24) &&& b20))

@[export shard_b_keccak_lane_24]
def lane24 (a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 _rc : UInt64) : UInt64 :=
  let c0 := a00 ^^^ a05 ^^^ a10 ^^^ a15 ^^^ a20
  let c1 := a01 ^^^ a06 ^^^ a11 ^^^ a16 ^^^ a21
  let c2 := a02 ^^^ a07 ^^^ a12 ^^^ a17 ^^^ a22
  let c3 := a03 ^^^ a08 ^^^ a13 ^^^ a18 ^^^ a23
  let c4 := a04 ^^^ a09 ^^^ a14 ^^^ a19 ^^^ a24
  let b20 := (((a02 ^^^ c1 ^^^ ((c3 <<< 1) ||| (c3 >>> 63))) <<< 62) ||| ((a02 ^^^ c1 ^^^ ((c3 <<< 1) ||| (c3 >>> 63))) >>> 2))
  let b21 := (((a08 ^^^ c2 ^^^ ((c4 <<< 1) ||| (c4 >>> 63))) <<< 55) ||| ((a08 ^^^ c2 ^^^ ((c4 <<< 1) ||| (c4 >>> 63))) >>> 9))
  let b24 := (((a21 ^^^ c0 ^^^ ((c2 <<< 1) ||| (c2 >>> 63))) <<< 2) ||| ((a21 ^^^ c0 ^^^ ((c2 <<< 1) ||| (c2 >>> 63))) >>> 62))
  (b24 ^^^ ((~~~b20) &&& b21))

def roundConstant : Nat → UInt64
  | 0 => 0x1
  | 1 => 0x8082
  | 2 => 0x800000000000808a
  | 3 => 0x8000000080008000
  | 4 => 0x808b
  | 5 => 0x80000001
  | 6 => 0x8000000080008081
  | 7 => 0x8000000000008009
  | 8 => 0x8a
  | 9 => 0x88
  | 10 => 0x80008009
  | 11 => 0x8000000a
  | 12 => 0x8000808b
  | 13 => 0x800000000000008b
  | 14 => 0x8000000000008089
  | 15 => 0x8000000000008003
  | 16 => 0x8000000000008002
  | 17 => 0x8000000000000080
  | 18 => 0x800a
  | 19 => 0x800000008000000a
  | 20 => 0x8000000080008081
  | 21 => 0x8000000000008080
  | 22 => 0x80000001
  | 23 => 0x8000000080008008
  | _ => 0

def rounds25 (count : Nat) : Nat → State25 → State25 :=
  Nat.rec (fun _ s => s) (fun _ previous i s => previous (i + 1) (round25 s (roundConstant i))) count

def keccakF1600 (s : State25) : State25 := rounds25 24 0 s

structure Pair64 where
  lo : UInt64
  hi : UInt64
  deriving Repr, DecidableEq, Inhabited

@[inline] def rotl64Fast (x : UInt64) (k : UInt64) : UInt64 :=
  (x <<< k) ||| (x >>> (64 - k))

@[inline] def round25CPS {α : Type}
    (a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 rc : UInt64)
    (k : UInt64 → UInt64 → UInt64 → UInt64 → UInt64 →
         UInt64 → UInt64 → UInt64 → UInt64 → UInt64 →
         UInt64 → UInt64 → UInt64 → UInt64 → UInt64 →
         UInt64 → UInt64 → UInt64 → UInt64 → UInt64 →
         UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → α) : α :=
  let c0 := a00 ^^^ a05 ^^^ a10 ^^^ a15 ^^^ a20
  let c1 := a01 ^^^ a06 ^^^ a11 ^^^ a16 ^^^ a21
  let c2 := a02 ^^^ a07 ^^^ a12 ^^^ a17 ^^^ a22
  let c3 := a03 ^^^ a08 ^^^ a13 ^^^ a18 ^^^ a23
  let c4 := a04 ^^^ a09 ^^^ a14 ^^^ a19 ^^^ a24
  let d0 := c4 ^^^ rotl64Fast c1 1
  let d1 := c0 ^^^ rotl64Fast c2 1
  let d2 := c1 ^^^ rotl64Fast c3 1
  let d3 := c2 ^^^ rotl64Fast c4 1
  let d4 := c3 ^^^ rotl64Fast c0 1
  let b00 := a00 ^^^ d0
  let b10 := rotl64Fast (a01 ^^^ d1) 1
  let b20 := rotl64Fast (a02 ^^^ d2) 62
  let b05 := rotl64Fast (a03 ^^^ d3) 28
  let b15 := rotl64Fast (a04 ^^^ d4) 27
  let b16 := rotl64Fast (a05 ^^^ d0) 36
  let b01 := rotl64Fast (a06 ^^^ d1) 44
  let b11 := rotl64Fast (a07 ^^^ d2) 6
  let b21 := rotl64Fast (a08 ^^^ d3) 55
  let b06 := rotl64Fast (a09 ^^^ d4) 20
  let b07 := rotl64Fast (a10 ^^^ d0) 3
  let b17 := rotl64Fast (a11 ^^^ d1) 10
  let b02 := rotl64Fast (a12 ^^^ d2) 43
  let b12 := rotl64Fast (a13 ^^^ d3) 25
  let b22 := rotl64Fast (a14 ^^^ d4) 39
  let b23 := rotl64Fast (a15 ^^^ d0) 41
  let b08 := rotl64Fast (a16 ^^^ d1) 45
  let b18 := rotl64Fast (a17 ^^^ d2) 15
  let b03 := rotl64Fast (a18 ^^^ d3) 21
  let b13 := rotl64Fast (a19 ^^^ d4) 8
  let b14 := rotl64Fast (a20 ^^^ d0) 18
  let b24 := rotl64Fast (a21 ^^^ d1) 2
  let b09 := rotl64Fast (a22 ^^^ d2) 61
  let b19 := rotl64Fast (a23 ^^^ d3) 56
  let b04 := rotl64Fast (a24 ^^^ d4) 14
  k ((b00 ^^^ ((~~~b01) &&& b02)) ^^^ rc)
    (b01 ^^^ ((~~~b02) &&& b03))
    (b02 ^^^ ((~~~b03) &&& b04))
    (b03 ^^^ ((~~~b04) &&& b00))
    (b04 ^^^ ((~~~b00) &&& b01))
    (b05 ^^^ ((~~~b06) &&& b07))
    (b06 ^^^ ((~~~b07) &&& b08))
    (b07 ^^^ ((~~~b08) &&& b09))
    (b08 ^^^ ((~~~b09) &&& b05))
    (b09 ^^^ ((~~~b05) &&& b06))
    (b10 ^^^ ((~~~b11) &&& b12))
    (b11 ^^^ ((~~~b12) &&& b13))
    (b12 ^^^ ((~~~b13) &&& b14))
    (b13 ^^^ ((~~~b14) &&& b10))
    (b14 ^^^ ((~~~b10) &&& b11))
    (b15 ^^^ ((~~~b16) &&& b17))
    (b16 ^^^ ((~~~b17) &&& b18))
    (b17 ^^^ ((~~~b18) &&& b19))
    (b18 ^^^ ((~~~b19) &&& b15))
    (b19 ^^^ ((~~~b15) &&& b16))
    (b20 ^^^ ((~~~b21) &&& b22))
    (b21 ^^^ ((~~~b22) &&& b23))
    (b22 ^^^ ((~~~b23) &&& b24))
    (b23 ^^^ ((~~~b24) &&& b20))
    (b24 ^^^ ((~~~b20) &&& b21))

def permuteAbsorb25 (s : State25)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : UInt64) : State25 :=
  round25CPS (s.a00 ^^^ w0) (s.a01 ^^^ w1) (s.a02 ^^^ w2) (s.a03 ^^^ w3) (s.a04 ^^^ w4)
    (s.a05 ^^^ w5) (s.a06 ^^^ w6) (s.a07 ^^^ w7) (s.a08 ^^^ w8) (s.a09 ^^^ w9)
    (s.a10 ^^^ w10) (s.a11 ^^^ w11) (s.a12 ^^^ w12) (s.a13 ^^^ w13) (s.a14 ^^^ w14)
    (s.a15 ^^^ w15) (s.a16 ^^^ w16) s.a17 s.a18 s.a19 s.a20 s.a21 s.a22 s.a23 s.a24
    0x0000000000000001
    fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x0000000000008082 fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x800000000000808a fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x8000000080008000 fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x000000000000808b fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x0000000080000001 fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x8000000080008081 fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x8000000000008009 fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x000000000000008a fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x0000000000000088 fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x0000000080008009 fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x000000008000000a fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x000000008000808b fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x800000000000008b fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x8000000000008089 fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x8000000000008003 fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x8000000000008002 fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x8000000000000080 fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x000000000000800a fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x800000008000000a fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x8000000080008081 fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x8000000000008080 fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x0000000080000001 fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x8000000080008008 fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  ⟨a00, a01, a02, a03, a04, a05, a06, a07, a08, a09, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24⟩

def keccak1Block16 (w0 w1 w2 w3 w4 w5 w6 w7 w8 : UInt64) : Pair64 :=
  round25CPS w0 w1 w2 w3 w4 w5 w6 w7 w8 0 0 0 0 0 0 0 0x8000000000000000 0 0 0 0 0 0 0 0
    0x0000000000000001
    fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x0000000000008082 fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x800000000000808a fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x8000000080008000 fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x000000000000808b fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x0000000080000001 fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x8000000080008081 fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x8000000000008009 fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x000000000000008a fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x0000000000000088 fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x0000000080008009 fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x000000008000000a fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x000000008000808b fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x800000000000008b fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x8000000000008089 fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x8000000000008003 fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x8000000000008002 fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x8000000000000080 fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x000000000000800a fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x800000008000000a fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x8000000080008081 fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x8000000000008080 fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x0000000080000001 fun a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 =>
  round25CPS a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    0x8000000080008008 fun a00 a01 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
  ⟨a00, a01⟩

def zeroState25Fast : State25 :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

@[inline] def readWordLEProof (b : @& ByteArray) (offset : Nat) (_ : offset + 7 < b.size) : UInt64 :=
  (b[offset]).toUInt64 |||
  ((b[offset + 1]).toUInt64 <<< 8) |||
  ((b[offset + 2]).toUInt64 <<< 16) |||
  ((b[offset + 3]).toUInt64 <<< 24) |||
  ((b[offset + 4]).toUInt64 <<< 32) |||
  ((b[offset + 5]).toUInt64 <<< 40) |||
  ((b[offset + 6]).toUInt64 <<< 48) |||
  ((b[offset + 7]).toUInt64 <<< 56)

@[inline] def readWordLEFast (b : @& ByteArray) (offset : Nat) : UInt64 :=
  if h : offset + 7 < b.size then
    readWordLEProof b offset h
  else
    Fin.foldl 8 (fun w j =>
      let idx := offset + j.val
      if h2 : idx < b.size then w ||| ((b[idx]).toUInt64 <<< (8 * j.val).toUInt64) else w) 0

@[inline] def pushU64LE (b : ByteArray) (w : UInt64) : ByteArray :=
  b.push w.toUInt8
    |>.push (w >>> 8).toUInt8
    |>.push (w >>> 16).toUInt8
    |>.push (w >>> 24).toUInt8
    |>.push (w >>> 32).toUInt8
    |>.push (w >>> 40).toUInt8
    |>.push (w >>> 48).toUInt8
    |>.push (w >>> 56).toUInt8

theorem usize_1073741824_lt : 1073741824 < USize.size := by
  cases USize.size_eq with
  | inl h32 => rw [h32]; decide
  | inr h64 => rw [h64]; decide

theorem usize_ofNat_small (k : Nat) (hk : k ≤ 256) : (USize.ofNat k).toNat = k := by
  have h1 := usize_1073741824_lt
  exact USize.toNat_ofNat_of_lt (by omega)

theorem add_usize_k {a : USize} {k n : Nat}
    (hk : k ≤ 256) (hn : n < USize.size) (ha : a.toNat + k < n) :
    (a + USize.ofNat k).toNat < n := by
  have h1 : (a + USize.ofNat k).toNat = (a.toNat + (USize.ofNat k).toNat) % USize.size :=
    USize.toNat_add a (USize.ofNat k)
  rw [h1, usize_ofNat_small k hk, Nat.mod_eq_of_lt (by omega)]
  exact ha

@[inline] def readWordLEUSize1 (b : @& ByteArray) (off : USize)
    (hsz : b.size < USize.size) (h : off.toNat + 7 < b.size) : UInt64 :=
  (b.uget off (by omega)).toUInt64 |||
  ((b.uget (off + USize.ofNat 1) (add_usize_k (k := 1) (by omega) hsz (by omega))).toUInt64 <<< 8) |||
  ((b.uget (off + USize.ofNat 2) (add_usize_k (k := 2) (by omega) hsz (by omega))).toUInt64 <<< 16) |||
  ((b.uget (off + USize.ofNat 3) (add_usize_k (k := 3) (by omega) hsz (by omega))).toUInt64 <<< 24) |||
  ((b.uget (off + USize.ofNat 4) (add_usize_k (k := 4) (by omega) hsz (by omega))).toUInt64 <<< 32) |||
  ((b.uget (off + USize.ofNat 5) (add_usize_k (k := 5) (by omega) hsz (by omega))).toUInt64 <<< 40) |||
  ((b.uget (off + USize.ofNat 6) (add_usize_k (k := 6) (by omega) hsz (by omega))).toUInt64 <<< 48) |||
  ((b.uget (off + USize.ofNat 7) (add_usize_k (k := 7) (by omega) hsz (by omega))).toUInt64 <<< 56)

@[inline] def rdWordAt (b : @& ByteArray) (baseU : USize) (k : Nat)
    (hk : k ≤ 128) (hsz : b.size < USize.size) (hblk : baseU.toNat + 135 < b.size) : UInt64 :=
  have hadd : (baseU + USize.ofNat k).toNat + 7 < b.size := by
    have h1 : (baseU + USize.ofNat k).toNat = (baseU.toNat + (USize.ofNat k).toNat) % USize.size :=
      USize.toNat_add baseU (USize.ofNat k)
    rw [h1, usize_ofNat_small k (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  readWordLEUSize1 b (baseU + USize.ofNat k) hsz hadd

def absorbFullBlocksAtCPS (st : State25) (b : @& ByteArray) (startOff : Nat) : State25 :=
  if hle : startOff ≤ b.size then
    let nFull := (b.size - startOff) / 136
    if hsz : b.size < 1073741824 then
      have hszU : b.size < USize.size := Nat.lt_trans hsz usize_1073741824_lt
      let startU : USize := startOff.toUSize
      have hstartU : startU.toNat = startOff := USize.toNat_ofNat_of_lt (by omega)
      Fin.foldl nFull (fun s i =>
        let idxU : USize := i.val.toUSize
        let baseU : USize := startU + idxU * USize.ofNat 136
        have hbase : baseU.toNat = startOff + i.val * 136 := by
          have hi : i.val < (b.size - startOff) / 136 := i.isLt
          have hiU : i.val < USize.size := by omega
          have hidx : idxU.toNat = i.val := USize.toNat_ofNat_of_lt hiU
          have hmul : (idxU * USize.ofNat 136).toNat = i.val * 136 := by
            have hm : (idxU * USize.ofNat 136).toNat = (idxU.toNat * (USize.ofNat 136).toNat) % USize.size :=
              USize.toNat_mul idxU (USize.ofNat 136)
            rw [hm, hidx, usize_ofNat_small 136 (by omega), Nat.mod_eq_of_lt (by omega)]
          have hadd : baseU.toNat = (startU.toNat + (idxU * USize.ofNat 136).toNat) % USize.size :=
            USize.toNat_add startU (idxU * USize.ofNat 136)
          rw [hadd, hstartU, hmul, Nat.mod_eq_of_lt (by omega)]
        have hblk : baseU.toNat + 135 < b.size := by
          have hi : i.val < (b.size - startOff) / 136 := i.isLt
          omega
        permuteAbsorb25 s
          (readWordLEUSize1 b baseU hszU (by omega))
          (rdWordAt b baseU 8 (by omega) hszU hblk)
          (rdWordAt b baseU 16 (by omega) hszU hblk)
          (rdWordAt b baseU 24 (by omega) hszU hblk)
          (rdWordAt b baseU 32 (by omega) hszU hblk)
          (rdWordAt b baseU 40 (by omega) hszU hblk)
          (rdWordAt b baseU 48 (by omega) hszU hblk)
          (rdWordAt b baseU 56 (by omega) hszU hblk)
          (rdWordAt b baseU 64 (by omega) hszU hblk)
          (rdWordAt b baseU 72 (by omega) hszU hblk)
          (rdWordAt b baseU 80 (by omega) hszU hblk)
          (rdWordAt b baseU 88 (by omega) hszU hblk)
          (rdWordAt b baseU 96 (by omega) hszU hblk)
          (rdWordAt b baseU 104 (by omega) hszU hblk)
          (rdWordAt b baseU 112 (by omega) hszU hblk)
          (rdWordAt b baseU 120 (by omega) hszU hblk)
          (rdWordAt b baseU 128 (by omega) hszU hblk)) st
    else
      Fin.foldl nFull (fun s i =>
        let base := startOff + 136 * i.val
        have hblk : base + 135 < b.size := by
          have hi : i.val < (b.size - startOff) / 136 := i.isLt
          omega
        permuteAbsorb25 s
          (readWordLEProof b base (by omega))
          (readWordLEProof b (base + 8) (by omega))
          (readWordLEProof b (base + 16) (by omega))
          (readWordLEProof b (base + 24) (by omega))
          (readWordLEProof b (base + 32) (by omega))
          (readWordLEProof b (base + 40) (by omega))
          (readWordLEProof b (base + 48) (by omega))
          (readWordLEProof b (base + 56) (by omega))
          (readWordLEProof b (base + 64) (by omega))
          (readWordLEProof b (base + 72) (by omega))
          (readWordLEProof b (base + 80) (by omega))
          (readWordLEProof b (base + 88) (by omega))
          (readWordLEProof b (base + 96) (by omega))
          (readWordLEProof b (base + 104) (by omega))
          (readWordLEProof b (base + 112) (by omega))
          (readWordLEProof b (base + 120) (by omega))
          (readWordLEProof b (base + 128) (by omega))) st
  else st

def absorbChunkCPS (st : State25) (carry : ByteArray) (c : @& ByteArray) : State25 × ByteArray :=
  if carry.size == 0 then
    let nFull := c.size / 136
    let st' := absorbFullBlocksAtCPS st c 0
    let tailStart := 136 * nFull
    (st', c.extract tailStart c.size)
  else if carry.size + c.size < 136 then
    let b := ByteArray.emptyWithCapacity (carry.size + c.size)
    let b := Fin.foldl carry.size (fun acc j =>
      if hj : j.val < carry.size then acc.push carry[j.val] else acc) b
    let b := Fin.foldl c.size (fun acc j =>
      if hj : j.val < c.size then acc.push c[j.val] else acc) b
    (st, b)
  else
    let need := 136 - carry.size
    let blk := ByteArray.emptyWithCapacity 136
    let blk := Fin.foldl carry.size (fun acc j =>
      if hj : j.val < carry.size then acc.push carry[j.val] else acc) blk
    let blk := Fin.foldl need (fun acc j =>
      if hj : j.val < c.size then acc.push c[j.val] else acc) blk
    let st1 := absorbFullBlocksAtCPS st blk 0
    let remLen := c.size - need
    let nFull := remLen / 136
    let st2 := absorbFullBlocksAtCPS st1 c need
    let tailStart := need + 136 * nFull
    (st2, c.extract tailStart c.size)

def absorbFullBlocksCPS (st : State25) (b : @& ByteArray) : State25 :=
  absorbFullBlocksAtCPS st b 0

def finalizeKeccak256CPS (st : State25) (tail : @& ByteArray) (tailStart tailLen : Nat) : ByteArray :=
  let pad := Fin.foldl tailLen (fun blk i =>
    let idx := tailStart + i.val
    if h : idx < tail.size then blk.set! i.val tail[idx] else blk) (ByteArray.mk (Array.replicate 136 0))
  let pad := pad.set! tailLen ((pad[tailLen]?.getD 0) ^^^ 1)
  let pad := pad.set! 135 ((pad[135]?.getD 0) ^^^ 128)
  let stFinal :=
    if hpad : 135 < pad.size then
      permuteAbsorb25 st
        (readWordLEProof pad 0 (by omega))
        (readWordLEProof pad 8 (by omega))
        (readWordLEProof pad 16 (by omega))
        (readWordLEProof pad 24 (by omega))
        (readWordLEProof pad 32 (by omega))
        (readWordLEProof pad 40 (by omega))
        (readWordLEProof pad 48 (by omega))
        (readWordLEProof pad 56 (by omega))
        (readWordLEProof pad 64 (by omega))
        (readWordLEProof pad 72 (by omega))
        (readWordLEProof pad 80 (by omega))
        (readWordLEProof pad 88 (by omega))
        (readWordLEProof pad 96 (by omega))
        (readWordLEProof pad 104 (by omega))
        (readWordLEProof pad 112 (by omega))
        (readWordLEProof pad 120 (by omega))
        (readWordLEProof pad 128 (by omega))
    else st
  let out := ByteArray.emptyWithCapacity 32
  let out := pushU64LE out stFinal.a00
  let out := pushU64LE out stFinal.a01
  let out := pushU64LE out stFinal.a02
  pushU64LE out stFinal.a03

def keccak256CPS (b : @& ByteArray) : ByteArray :=
  let nFull := b.size / 136
  let st := absorbFullBlocksCPS zeroState25Fast b
  let tailStart := 136 * nFull
  finalizeKeccak256CPS st b tailStart (b.size - tailStart)

end LeanVmXmss.Model.Keccak
