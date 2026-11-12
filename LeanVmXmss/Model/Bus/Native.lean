import Model.Bus.Scalar

namespace LeanVmXmss.Model.Bus

open Spec.Field (K E zero one)
open Model.Field

@[inline] def planarEadd0 (a0 b0 : UInt64) : UInt64 := a0 ^^^ b0
@[inline] def planarEadd1 (a1 b1 : UInt64) : UInt64 := a1 ^^^ b1
@[inline] def planarEadd2 (a2 b2 : UInt64) : UInt64 := a2 ^^^ b2

@[inline] def planarEmul0 (a0 a1 a2 b0 b1 b2 : UInt64) : UInt64 :=
  let p0 := nativeMul a0 b0
  let p1 := nativeMul a1 b1
  let p2 := nativeMul a2 b2
  let m12 := nativeMul (a1 ^^^ a2) (b1 ^^^ b2)
  (p0 ^^^ m12) ^^^ p1 ^^^ p2

@[inline] def planarEmul1 (a0 a1 a2 b0 b1 b2 : UInt64) : UInt64 :=
  let p0 := nativeMul a0 b0
  let m01 := nativeMul (a0 ^^^ a1) (b0 ^^^ b1)
  let m12 := nativeMul (a1 ^^^ a2) (b1 ^^^ b2)
  (p0 ^^^ m12) ^^^ m01

@[inline] def planarEmul2 (a0 a1 a2 b0 b1 b2 : UInt64) : UInt64 :=
  let p0 := nativeMul a0 b0
  let p1 := nativeMul a1 b1
  let m02 := nativeMul (a0 ^^^ a2) (b0 ^^^ b2)
  p0 ^^^ p1 ^^^ m02

@[inline] def planarMulBase0 (a0 k : UInt64) : UInt64 := nativeMul a0 k
@[inline] def planarMulBase1 (a1 k : UInt64) : UInt64 := nativeMul a1 k
@[inline] def planarMulBase2 (a2 k : UInt64) : UInt64 := nativeMul a2 k

@[inline] def planarEadd (a b : E) : E :=
  ⟨planarEadd0 a.c0 b.c0, planarEadd1 a.c1 b.c1, planarEadd2 a.c2 b.c2⟩

@[inline] def planarEmul (a b : E) : E :=
  let p0 := nativeMul a.c0 b.c0
  let p1 := nativeMul a.c1 b.c1
  let p2 := nativeMul a.c2 b.c2
  let m01 := nativeMul (a.c0 ^^^ a.c1) (b.c0 ^^^ b.c1)
  let m02 := nativeMul (a.c0 ^^^ a.c2) (b.c0 ^^^ b.c2)
  let m12 := nativeMul (a.c1 ^^^ a.c2) (b.c1 ^^^ b.c2)
  let q := p0 ^^^ m12
  ⟨q ^^^ p1 ^^^ p2, q ^^^ m01, p0 ^^^ p1 ^^^ m02⟩

@[inline] def planarMulBase (a : E) (k : K) : E :=
  ⟨planarMulBase0 a.c0 k, planarMulBase1 a.c1 k, planarMulBase2 a.c2 k⟩

end LeanVmXmss.Model.Bus
