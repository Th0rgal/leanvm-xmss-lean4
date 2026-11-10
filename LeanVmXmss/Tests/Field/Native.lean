import Tests.Field.Intrinsic

@[noinline]
def nativeTestReduce (lo hi : UInt64) : UInt64 :=
  let spill := (hi >>> 63) ^^^ (hi >>> 61) ^^^ (hi >>> 60)
  let v := hi ^^^ spill
  lo ^^^ v ^^^ (v <<< 1) ^^^ (v <<< 3) ^^^ (v <<< 4)

@[noinline, export shard_a_test_mul]
def nativeTestMul (a b : UInt64) : UInt64 :=
  let lo := clmul64 a b
  let hi := clmul64Hi a b
  nativeTestReduce lo hi

@[noinline, export shard_a_test_square]
def nativeTestSquare (a : UInt64) : UInt64 := nativeTestMul a a

@[noinline]
def nativeMulHop1 (a b : UInt64) : UInt64 := nativeTestMul a b

@[noinline]
def nativeMulHop2 (a b : UInt64) : UInt64 := nativeMulHop1 a b

@[noinline]
def nativeMulHop3 (a b : UInt64) : UInt64 := nativeMulHop2 a b

@[noinline]
def nativeMulHop4 (a b : UInt64) : UInt64 := nativeMulHop3 a b

@[noinline]
def nativeMulHop5 (a b : UInt64) : UInt64 := nativeMulHop4 a b

@[noinline]
def nativeSqHop (a : UInt64) : UInt64 := nativeMulHop5 a a

@[noinline]
def nativeTestSquare3 (a : UInt64) : UInt64 :=
  let s1 := nativeSqHop a
  let s2 := nativeSqHop s1
  nativeSqHop s2

@[noinline]
def nativeTestSquare6 (a : UInt64) : UInt64 :=
  let s3 := nativeTestSquare3 a
  nativeTestSquare3 s3

@[noinline]
def nativeTestSquare12 (a : UInt64) : UInt64 :=
  let s6 := nativeTestSquare6 a
  nativeTestSquare6 s6

@[noinline]
def nativeTestSquare24 (a : UInt64) : UInt64 :=
  let s12 := nativeTestSquare12 a
  nativeTestSquare12 s12

@[noinline, export shard_a_test_inv]
def nativeTestInv (a : UInt64) : UInt64 :=
  let s1 := nativeSqHop a
  let t2 := nativeMulHop5 s1 a
  let s2 := nativeSqHop t2
  let t3 := nativeMulHop5 s2 a
  let q3 := nativeTestSquare3 t3
  let t6 := nativeMulHop5 q3 t3
  let r6 := nativeTestSquare6 t6
  let t12 := nativeMulHop5 r6 t6
  let u12 := nativeTestSquare12 t12
  let t24 := nativeMulHop5 u12 t12
  let v24 := nativeTestSquare24 t24
  let t48 := nativeMulHop5 v24 t24
  let w12 := nativeTestSquare12 t48
  let t60 := nativeMulHop5 w12 t12
  let z3 := nativeTestSquare3 t60
  let t63 := nativeMulHop5 z3 t3
  nativeSqHop t63

@[noinline, export shard_a_test_karatsuba_c0]
def nativeTestKaratsuba0 (a0 a1 a2 b0 b1 b2 : UInt64) : UInt64 :=
  let p0 := nativeMulHop5 a0 b0
  let p1 := nativeMulHop5 a1 b1
  let p2 := nativeMulHop5 a2 b2
  let x := a1 ^^^ a2
  let y := b1 ^^^ b2
  let m := nativeMulHop5 x y
  let e3 := m ^^^ p1 ^^^ p2
  p0 ^^^ e3

@[noinline, export shard_a_test_karatsuba_c1]
def nativeTestKaratsuba1 (a0 a1 a2 b0 b1 b2 : UInt64) : UInt64 :=
  let p0 := nativeMulHop5 a0 b0
  let p1 := nativeMulHop5 a1 b1
  let p2 := nativeMulHop5 a2 b2
  let x1 := a0 ^^^ a1
  let y1 := b0 ^^^ b1
  let m1 := nativeMulHop5 x1 y1
  let e1 := m1 ^^^ p0 ^^^ p1
  let x3 := a1 ^^^ a2
  let y3 := b1 ^^^ b2
  let m3 := nativeMulHop5 x3 y3
  let e3 := m3 ^^^ p1 ^^^ p2
  e1 ^^^ e3 ^^^ p2

@[noinline, export shard_a_test_karatsuba_c2]
def nativeTestKaratsuba2 (a0 a1 a2 b0 b1 b2 : UInt64) : UInt64 :=
  let p0 := nativeMulHop5 a0 b0
  let p1 := nativeMulHop5 a1 b1
  let p2 := nativeMulHop5 a2 b2
  let x := a0 ^^^ a2
  let y := b0 ^^^ b2
  let m := nativeMulHop5 x y
  let e2 := m ^^^ p0 ^^^ p2 ^^^ p1
  e2 ^^^ p2

def main (args : List String) : IO Unit := do
  let ns := args.map (fun s => s.toNat!.toUInt64)
  if ns.length != 7 then throw (IO.userError "expected seven words")
  let a0 := ns[0]!
  let a1 := ns[1]!
  let a2 := ns[2]!
  let b0 := ns[3]!
  let b1 := ns[4]!
  let b2 := ns[5]!
  let p0 := nativeTestKaratsuba0 a0 a1 a2 b0 b1 b2
  let p1 := nativeTestKaratsuba1 a0 a1 a2 b0 b1 b2
  let p2 := nativeTestKaratsuba2 a0 a1 a2 b0 b1 b2
  let f0 := a0
  let f1 := a2
  let f2 := a1 ^^^ a2
  let ff0 := f0
  let ff1 := f2
  let ff2 := f1 ^^^ f2
  let q0 := nativeTestKaratsuba0 f0 f1 f2 ff0 ff1 ff2
  let q1 := nativeTestKaratsuba1 f0 f1 f2 ff0 ff1 ff2
  let q2 := nativeTestKaratsuba2 f0 f1 f2 ff0 ff1 ff2
  let n := nativeTestKaratsuba0 a0 a1 a2 q0 q1 q2
  let v := nativeTestInv n
  let i0 := nativeTestMul q0 v
  let i1 := nativeTestMul q1 v
  let i2 := nativeTestMul q2 v
  let values := [nativeTestMul a0 b0,
    nativeTestInv a0, p0, p1, p2, i0, i1, i2, nativeTestSquare a0]
  IO.println (String.intercalate " " (values.map (fun x => toString x.toNat)))
