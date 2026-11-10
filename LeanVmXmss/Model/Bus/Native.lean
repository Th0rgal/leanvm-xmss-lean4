import Model.Bus.Scalar

namespace LeanVmXmss.Model.Bus

open Spec.Field (K E zero one)
open Model.Field

@[noinline]
def planarEadd0 (a0 b0 : UInt64) : UInt64 := a0 ^^^ b0

@[noinline]
def planarEadd1 (a1 b1 : UInt64) : UInt64 := a1 ^^^ b1

@[noinline]
def planarEadd2 (a2 b2 : UInt64) : UInt64 := a2 ^^^ b2

@[noinline]
def planarEmul0 (a0 a1 a2 b0 b1 b2 : UInt64) : UInt64 :=
  nativeKaratsuba0 a0 a1 a2 b0 b1 b2

@[noinline]
def planarEmul1 (a0 a1 a2 b0 b1 b2 : UInt64) : UInt64 :=
  nativeKaratsuba1 a0 a1 a2 b0 b1 b2

@[noinline]
def planarEmul2 (a0 a1 a2 b0 b1 b2 : UInt64) : UInt64 :=
  nativeKaratsuba2 a0 a1 a2 b0 b1 b2

@[noinline]
def planarMulBase0 (a0 k : UInt64) : UInt64 := nativeMul a0 k

@[noinline]
def planarMulBase1 (a1 k : UInt64) : UInt64 := nativeMul a1 k

@[noinline]
def planarMulBase2 (a2 k : UInt64) : UInt64 := nativeMul a2 k

def planarEadd (a b : E) : E :=
  ⟨planarEadd0 a.c0 b.c0, planarEadd1 a.c1 b.c1, planarEadd2 a.c2 b.c2⟩

def planarEmul (a b : E) : E :=
  ⟨planarEmul0 a.c0 a.c1 a.c2 b.c0 b.c1 b.c2,
   planarEmul1 a.c0 a.c1 a.c2 b.c0 b.c1 b.c2,
   planarEmul2 a.c0 a.c1 a.c2 b.c0 b.c1 b.c2⟩

def planarMulBase (a : E) (k : K) : E :=
  ⟨planarMulBase0 a.c0 k, planarMulBase1 a.c1 k, planarMulBase2 a.c2 k⟩

end LeanVmXmss.Model.Bus
