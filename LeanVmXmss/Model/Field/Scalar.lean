import Spec.Field.Basic

namespace LeanVmXmss.Model.Field

open Spec.Field (K E)

def clmulSteps (a b : BitVec 64) : Nat → BitVec 128 :=
  Nat.rec 0 (fun n prev => prev ^^^ if b.getLsbD n then a.setWidth 128 <<< n else 0)

@[simp] theorem clmulSteps.zero (a b : BitVec 64) : clmulSteps a b 0 = 0 := rfl

@[simp] theorem clmulSteps.succ (a b : BitVec 64) (n : Nat) :
    clmulSteps a b (n + 1) = clmulSteps a b n ^^^
      if b.getLsbD n then a.setWidth 128 <<< n else 0 := rfl

def clmul (a b : K) : BitVec 128 := clmulSteps a.toBitVec b.toBitVec 64

def reduce (p : BitVec 128) : K :=
  let lo := p.setWidth 64
  let hi := (p >>> 64).setWidth 64
  let spill := (hi >>> 63) ^^^ (hi >>> 61) ^^^ (hi >>> 60)
  let v := hi ^^^ spill
  UInt64.ofBitVec (lo ^^^ v ^^^ (v <<< 1) ^^^ (v <<< 3) ^^^ (v <<< 4))

def add (a b : K) : K := a ^^^ b

def mul (a b : K) : K := reduce (clmul a b)

def spreadSteps (a : BitVec 64) : Nat → BitVec 128 :=
  Nat.rec 0 (fun n prev => prev ^^^ if a.getLsbD n then (1 : BitVec 128) <<< (2 * n) else 0)

@[simp] theorem spreadSteps.zero (a : BitVec 64) : spreadSteps a 0 = 0 := rfl

@[simp] theorem spreadSteps.succ (a : BitVec 64) (n : Nat) :
    spreadSteps a (n + 1) = spreadSteps a n ^^^
      if a.getLsbD n then (1 : BitVec 128) <<< (2 * n) else 0 := rfl

def square (a : K) : K := reduce (spreadSteps a.toBitVec 64)

def eadd (a b : E) : E := ⟨a.c0 ^^^ b.c0, a.c1 ^^^ b.c1, a.c2 ^^^ b.c2⟩

def polynomialMul (a b : E) : E :=
  let p0 := mul a.c0 b.c0
  let p1 := mul a.c0 b.c1 ^^^ mul a.c1 b.c0
  let p2 := mul a.c0 b.c2 ^^^ mul a.c1 b.c1 ^^^ mul a.c2 b.c0
  let p3 := mul a.c1 b.c2 ^^^ mul a.c2 b.c1
  let p4 := mul a.c2 b.c2
  ⟨p0 ^^^ p3, p1 ^^^ p3 ^^^ p4, p2 ^^^ p4⟩

def karatsubaMul (a b : E) : E :=
  let p0 := mul a.c0 b.c0
  let p1 := mul a.c1 b.c1
  let p2 := mul a.c2 b.c2
  let e1 := mul (a.c0 ^^^ a.c1) (b.c0 ^^^ b.c1) ^^^ p0 ^^^ p1
  let e2 := mul (a.c0 ^^^ a.c2) (b.c0 ^^^ b.c2) ^^^ p0 ^^^ p2 ^^^ p1
  let e3 := mul (a.c1 ^^^ a.c2) (b.c1 ^^^ b.c2) ^^^ p1 ^^^ p2
  ⟨p0 ^^^ e3, e1 ^^^ e3 ^^^ p2, e2 ^^^ p2⟩

def mulBase (a : E) (b : K) : E := ⟨mul a.c0 b, mul a.c1 b, mul a.c2 b⟩

def esquare (a : E) : E :=
  let s0 := square a.c0
  let s1 := square a.c1
  let s2 := square a.c2
  ⟨s0, s2, s1 ^^^ s2⟩

end LeanVmXmss.Model.Field
