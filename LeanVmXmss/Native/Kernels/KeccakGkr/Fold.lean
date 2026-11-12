import Native.Kernels.KeccakGkr.Support

namespace LeanVmXmss.Native.Kernels.KeccakGkr

set_option compiler.ignoreBorrowAnnotation true

@[noinline]
def foldStepOne (lo hi : ByteArray) (i : USize) (c0 c1 c2 : UInt64) (acc : ByteArray) : ByteArray :=
  let base := 3 * i
  let l0 := readWordAt lo base
  let l1 := readWordAt lo (base + 1)
  let l2 := readWordAt lo (base + 2)
  let h0 := readWordAt hi base
  let h1 := readWordAt hi (base + 1)
  let h2 := readWordAt hi (base + 2)
  let d0 := l0 ^^^ h0
  let d1 := l1 ^^^ h1
  let d2 := l2 ^^^ h2
  let m0 := karatsuba0 c0 c1 c2 d0 d1 d2
  let m1 := karatsuba1 c0 c1 c2 d0 d1 d2
  let m2 := karatsuba2 c0 c1 c2 d0 d1 d2
  let a0 := pushU64LE acc (l0 ^^^ m0)
  let a1 := pushU64LE a0 (l1 ^^^ m1)
  pushU64LE a1 (l2 ^^^ m2)

@[noinline, export lean_xmss_gkr_fold_even_odd]
def gkrFoldEvenOdd (lo hi : ByteArray) (n : USize) (c0 c1 c2 : UInt64) : ByteArray :=
  let cap := n.toNat * 24
  Nat.rec (motive := fun _ => ByteArray) (ByteArray.emptyWithCapacity cap)
    (fun i prev => foldStepOne lo hi (USize.ofNat i) c0 c1 c2 prev)
    n.toNat

end LeanVmXmss.Native.Kernels.KeccakGkr
