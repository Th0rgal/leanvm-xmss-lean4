import Model.Field.Operations

namespace LeanVmXmss.Model.Field

@[inline] def nativeSelect (a b i : UInt64) : UInt64 :=
  a &&& (0 - ((b >>> i) &&& 1))

@[inline] def nativeClmulByte (a b : UInt64) : UInt64 :=
  nativeSelect a b 0 ^^^ nativeSelect (a <<< 1) b 1 ^^^
  nativeSelect (a <<< 2) b 2 ^^^ nativeSelect (a <<< 3) b 3 ^^^
  nativeSelect (a <<< 4) b 4 ^^^ nativeSelect (a <<< 5) b 5 ^^^
  nativeSelect (a <<< 6) b 6 ^^^ nativeSelect (a <<< 7) b 7

@[inline] def nativeClmulByteHi (a b : UInt64) : UInt64 :=
  nativeSelect (a >>> 63) b 1 ^^^ nativeSelect (a >>> 62) b 2 ^^^
  nativeSelect (a >>> 61) b 3 ^^^ nativeSelect (a >>> 60) b 4 ^^^
  nativeSelect (a >>> 59) b 5 ^^^ nativeSelect (a >>> 58) b 6 ^^^
  nativeSelect (a >>> 57) b 7

@[inline, export shard_a_clmul_lo]
def nativeClmulLo (a b : UInt64) : UInt64 :=
  nativeClmulByte a b ^^^ (nativeClmulByte a (b >>> 8) <<< 8) ^^^
  (nativeClmulByte a (b >>> 16) <<< 16) ^^^ (nativeClmulByte a (b >>> 24) <<< 24) ^^^
  (nativeClmulByte a (b >>> 32) <<< 32) ^^^ (nativeClmulByte a (b >>> 40) <<< 40) ^^^
  (nativeClmulByte a (b >>> 48) <<< 48) ^^^ (nativeClmulByte a (b >>> 56) <<< 56)

@[inline] def nativeClmulUpper (a b i j : UInt64) : UInt64 :=
  (nativeClmulByte a (b >>> i) >>> j) ^^^ (nativeClmulByteHi a (b >>> i) <<< i)

@[inline, export shard_a_clmul_hi]
def nativeClmulHi (a b : UInt64) : UInt64 :=
  nativeSelect (a >>> 63) b 1 ^^^ nativeSelect (a >>> 62) b 2 ^^^
  nativeSelect (a >>> 61) b 3 ^^^ nativeSelect (a >>> 60) b 4 ^^^
  nativeSelect (a >>> 59) b 5 ^^^ nativeSelect (a >>> 58) b 6 ^^^
  nativeSelect (a >>> 57) b 7 ^^^ nativeSelect (a >>> 56) b 8 ^^^
  nativeSelect (a >>> 55) b 9 ^^^ nativeSelect (a >>> 54) b 10 ^^^
  nativeSelect (a >>> 53) b 11 ^^^ nativeSelect (a >>> 52) b 12 ^^^
  nativeSelect (a >>> 51) b 13 ^^^ nativeSelect (a >>> 50) b 14 ^^^
  nativeSelect (a >>> 49) b 15 ^^^ nativeSelect (a >>> 48) b 16 ^^^
  nativeSelect (a >>> 47) b 17 ^^^ nativeSelect (a >>> 46) b 18 ^^^
  nativeSelect (a >>> 45) b 19 ^^^ nativeSelect (a >>> 44) b 20 ^^^
  nativeSelect (a >>> 43) b 21 ^^^ nativeSelect (a >>> 42) b 22 ^^^
  nativeSelect (a >>> 41) b 23 ^^^ nativeSelect (a >>> 40) b 24 ^^^
  nativeSelect (a >>> 39) b 25 ^^^ nativeSelect (a >>> 38) b 26 ^^^
  nativeSelect (a >>> 37) b 27 ^^^ nativeSelect (a >>> 36) b 28 ^^^
  nativeSelect (a >>> 35) b 29 ^^^ nativeSelect (a >>> 34) b 30 ^^^
  nativeSelect (a >>> 33) b 31 ^^^ nativeSelect (a >>> 32) b 32 ^^^
  nativeSelect (a >>> 31) b 33 ^^^ nativeSelect (a >>> 30) b 34 ^^^
  nativeSelect (a >>> 29) b 35 ^^^ nativeSelect (a >>> 28) b 36 ^^^
  nativeSelect (a >>> 27) b 37 ^^^ nativeSelect (a >>> 26) b 38 ^^^
  nativeSelect (a >>> 25) b 39 ^^^ nativeSelect (a >>> 24) b 40 ^^^
  nativeSelect (a >>> 23) b 41 ^^^ nativeSelect (a >>> 22) b 42 ^^^
  nativeSelect (a >>> 21) b 43 ^^^ nativeSelect (a >>> 20) b 44 ^^^
  nativeSelect (a >>> 19) b 45 ^^^ nativeSelect (a >>> 18) b 46 ^^^
  nativeSelect (a >>> 17) b 47 ^^^ nativeSelect (a >>> 16) b 48 ^^^
  nativeSelect (a >>> 15) b 49 ^^^ nativeSelect (a >>> 14) b 50 ^^^
  nativeSelect (a >>> 13) b 51 ^^^ nativeSelect (a >>> 12) b 52 ^^^
  nativeSelect (a >>> 11) b 53 ^^^ nativeSelect (a >>> 10) b 54 ^^^
  nativeSelect (a >>> 9) b 55 ^^^ nativeSelect (a >>> 8) b 56 ^^^
  nativeSelect (a >>> 7) b 57 ^^^ nativeSelect (a >>> 6) b 58 ^^^
  nativeSelect (a >>> 5) b 59 ^^^ nativeSelect (a >>> 4) b 60 ^^^
  nativeSelect (a >>> 3) b 61 ^^^ nativeSelect (a >>> 2) b 62 ^^^
  nativeSelect (a >>> 1) b 63

@[inline, export shard_a_reduce]
def nativeReduce (lo hi : UInt64) : UInt64 :=
  let spill := (hi >>> 63) ^^^ (hi >>> 61) ^^^ (hi >>> 60)
  let v := hi ^^^ spill
  lo ^^^ v ^^^ (v <<< 1) ^^^ (v <<< 3) ^^^ (v <<< 4)

@[export shard_a_mul]
def nativeMul (a b : UInt64) : UInt64 :=
  nativeReduce (nativeClmulLo a b) (nativeClmulHi a b)

@[export shard_a_square]
def nativeSquare (a : UInt64) : UInt64 := nativeMul a a

def nativeSquare3 (a : UInt64) : UInt64 :=
  nativeSquare (nativeSquare (nativeSquare a))

def nativeSquare6 (a : UInt64) : UInt64 := nativeSquare3 (nativeSquare3 a)

def nativeSquare12 (a : UInt64) : UInt64 := nativeSquare6 (nativeSquare6 a)

def nativeSquare24 (a : UInt64) : UInt64 := nativeSquare12 (nativeSquare12 a)

def nativeInv3 (a : UInt64) : UInt64 :=
  let t2 := nativeMul (nativeSquare a) a
  nativeMul (nativeSquare t2) a

def nativeInv6 (t3 : UInt64) : UInt64 := nativeMul (nativeSquare3 t3) t3

def nativeInv12 (t6 : UInt64) : UInt64 := nativeMul (nativeSquare6 t6) t6

def nativeInv24 (t12 : UInt64) : UInt64 := nativeMul (nativeSquare12 t12) t12

def nativeInv48 (t24 : UInt64) : UInt64 := nativeMul (nativeSquare24 t24) t24

def nativeInv60 (t48 t12 : UInt64) : UInt64 := nativeMul (nativeSquare12 t48) t12

def nativeInv63 (t60 t3 : UInt64) : UInt64 := nativeMul (nativeSquare3 t60) t3

@[export shard_a_inv]
def nativeInv (a : UInt64) : UInt64 :=
  let t3 := nativeInv3 a
  let t12 := nativeInv12 (nativeInv6 t3)
  let t48 := nativeInv48 (nativeInv24 t12)
  nativeSquare (nativeInv63 (nativeInv60 t48 t12) t3)

@[export shard_a_karatsuba_c0]
def nativeKaratsuba0 (a0 a1 a2 b0 b1 b2 : UInt64) : UInt64 :=
  let p0 := nativeMul a0 b0
  let p1 := nativeMul a1 b1
  let p2 := nativeMul a2 b2
  let e3 := nativeMul (a1 ^^^ a2) (b1 ^^^ b2) ^^^ p1 ^^^ p2
  p0 ^^^ e3

@[export shard_a_karatsuba_c1]
def nativeKaratsuba1 (a0 a1 a2 b0 b1 b2 : UInt64) : UInt64 :=
  let p0 := nativeMul a0 b0
  let p1 := nativeMul a1 b1
  let p2 := nativeMul a2 b2
  let e1 := nativeMul (a0 ^^^ a1) (b0 ^^^ b1) ^^^ p0 ^^^ p1
  let e3 := nativeMul (a1 ^^^ a2) (b1 ^^^ b2) ^^^ p1 ^^^ p2
  e1 ^^^ e3 ^^^ p2

@[export shard_a_karatsuba_c2]
def nativeKaratsuba2 (a0 a1 a2 b0 b1 b2 : UInt64) : UInt64 :=
  let p0 := nativeMul a0 b0
  let p1 := nativeMul a1 b1
  let p2 := nativeMul a2 b2
  let e2 := nativeMul (a0 ^^^ a2) (b0 ^^^ b2) ^^^ p0 ^^^ p2 ^^^ p1
  e2 ^^^ p2

def nativeKaratsuba (a b : Spec.Field.E) : Spec.Field.E :=
  ⟨nativeKaratsuba0 a.c0 a.c1 a.c2 b.c0 b.c1 b.c2,
   nativeKaratsuba1 a.c0 a.c1 a.c2 b.c0 b.c1 b.c2,
   nativeKaratsuba2 a.c0 a.c1 a.c2 b.c0 b.c1 b.c2⟩

def nativeEinv (a : Spec.Field.E) : Spec.Field.E :=
  let f := frobenius a
  let ff := frobenius f
  let p := nativeKaratsuba f ff
  let n := nativeKaratsuba0 a.c0 a.c1 a.c2 p.c0 p.c1 p.c2
  let v := nativeInv n
  ⟨nativeMul p.c0 v, nativeMul p.c1 v, nativeMul p.c2 v⟩

end LeanVmXmss.Model.Field
