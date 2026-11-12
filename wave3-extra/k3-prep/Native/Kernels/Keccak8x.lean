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
