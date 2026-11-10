import Tests.Field.Intrinsic

@[noinline]
def shardAReduceHw (lo hi : UInt64) : UInt64 :=
  let spill := (hi >>> 63) ^^^ (hi >>> 61) ^^^ (hi >>> 60)
  let v := hi ^^^ spill
  lo ^^^ v ^^^ (v <<< 1) ^^^ (v <<< 3) ^^^ (v <<< 4)

@[noinline, export shard_a_clmul_lo]
def shardAClmulLoHw (a b : UInt64) : UInt64 := clmul64 a b

@[noinline, export shard_a_clmul_hi]
def shardAClmulHiHw (a b : UInt64) : UInt64 := clmul64Hi a b

@[noinline, export shard_a_mul]
def shardAMulHw (a b : UInt64) : UInt64 :=
  let lo := clmul64 a b
  let hi := clmul64Hi a b
  shardAReduceHw lo hi

@[noinline, export shard_a_square]
def shardASquareHw (a : UInt64) : UInt64 := shardAMulHw a a

@[noinline, export shard_a_karatsuba_c0]
def shardAKaratsuba0Hw (a0 a1 a2 b0 b1 b2 : UInt64) : UInt64 :=
  let p0 := shardAMulHw a0 b0
  let p1 := shardAMulHw a1 b1
  let p2 := shardAMulHw a2 b2
  let x := a1 ^^^ a2
  let y := b1 ^^^ b2
  let m := shardAMulHw x y
  let e3 := m ^^^ p1 ^^^ p2
  p0 ^^^ e3

@[noinline, export shard_a_karatsuba_c1]
def shardAKaratsuba1Hw (a0 a1 a2 b0 b1 b2 : UInt64) : UInt64 :=
  let p0 := shardAMulHw a0 b0
  let p1 := shardAMulHw a1 b1
  let p2 := shardAMulHw a2 b2
  let x1 := a0 ^^^ a1
  let y1 := b0 ^^^ b1
  let m1 := shardAMulHw x1 y1
  let e1 := m1 ^^^ p0 ^^^ p1
  let x3 := a1 ^^^ a2
  let y3 := b1 ^^^ b2
  let m3 := shardAMulHw x3 y3
  let e3 := m3 ^^^ p1 ^^^ p2
  e1 ^^^ e3 ^^^ p2

@[noinline, export shard_a_karatsuba_c2]
def shardAKaratsuba2Hw (a0 a1 a2 b0 b1 b2 : UInt64) : UInt64 :=
  let p0 := shardAMulHw a0 b0
  let p1 := shardAMulHw a1 b1
  let p2 := shardAMulHw a2 b2
  let x2 := a0 ^^^ a2
  let y2 := b0 ^^^ b2
  let m2 := shardAMulHw x2 y2
  let e2 := m2 ^^^ p0 ^^^ p2 ^^^ p1
  e2 ^^^ p2
