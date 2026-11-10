import Model.Field.Scalar
import Spec.Field.Operations

namespace LeanVmXmss.Model.Field

open Spec.Field (K E)

def pow (a : K) (n : Nat) : K := Spec.Field.powWith mul 1 a n

def inv (a : K) : K := Spec.Field.inverseChainWith mul square a

def masked (a mask : K) : K := a &&& mask

def sum (as : List K) : K := as.foldl add 0

def powers (a : K) (count : Nat) : List K := (List.range count).map (pow a)

def epow (a : E) (n : Nat) : E := Spec.Field.powWith karatsubaMul Spec.Field.one a n

def frobenius (a : E) : E := ⟨a.c0, a.c2, a.c1 ^^^ a.c2⟩

def frobenius2 (a : E) : E := frobenius (frobenius a)

def norm (a : E) : K := (karatsubaMul a (karatsubaMul (frobenius a) (frobenius2 a))).c0

def einv (a : E) : E := mulBase (karatsubaMul (frobenius a) (frobenius2 a)) (inv (norm a))

def emasked (a : E) (mask : K) : E := ⟨masked a.c0 mask, masked a.c1 mask, masked a.c2 mask⟩

def esum (as : List E) : E := as.foldl eadd Spec.Field.zero

def epowers (a : E) (count : Nat) : List E := (List.range count).map (epow a)

def encodeBytesK (a : K) : ByteArray :=
  ⟨#[UInt8.ofNat a.toNat, UInt8.ofNat (a.toNat >>> 8),
    UInt8.ofNat (a.toNat >>> 16), UInt8.ofNat (a.toNat >>> 24),
    UInt8.ofNat (a.toNat >>> 32), UInt8.ofNat (a.toNat >>> 40),
    UInt8.ofNat (a.toNat >>> 48), UInt8.ofNat (a.toNat >>> 56)]⟩

def readLimb (bytes : ByteArray) (offset : Nat) : K :=
  UInt64.ofNat (bytes.data.toList[offset]!.toNat +
    (bytes.data.toList[offset + 1]!.toNat <<< 8) +
    (bytes.data.toList[offset + 2]!.toNat <<< 16) +
    (bytes.data.toList[offset + 3]!.toNat <<< 24) +
    (bytes.data.toList[offset + 4]!.toNat <<< 32) +
    (bytes.data.toList[offset + 5]!.toNat <<< 40) +
    (bytes.data.toList[offset + 6]!.toNat <<< 48) +
    (bytes.data.toList[offset + 7]!.toNat <<< 56))

def decodeBytesK? (bytes : ByteArray) : Option K :=
  if bytes.size = 8 then some (readLimb bytes 0) else none

def encodeBytesE (a : E) : ByteArray :=
  encodeBytesK a.c0 ++ encodeBytesK a.c1 ++ encodeBytesK a.c2

def decodeBytesE? (bytes : ByteArray) : Option E :=
  if bytes.size = 24 then some ⟨readLimb bytes 0, readLimb bytes 8, readLimb bytes 16⟩ else none

abbrev Scaled := Spec.Field.Scaled

def scaled (r : E) : Scaled := ⟨fun l w n => karatsubaMul r (Spec.Field.windowElement l w n)⟩

def scaledLimb (s : Scaled) (limb : Fin 3) (a : K) (acc : E) : Nat → E :=
  Nat.rec acc (fun n prev =>
    if h : n < 11 then
      eadd prev (s.table limb ⟨n, h⟩ ⟨(a.toNat >>> (6 * n)) % 64, Nat.mod_lt _ (by decide)⟩)
    else prev)

@[simp] theorem scaledLimb.zero (s : Scaled) (limb : Fin 3) (a : K) (acc : E) :
    scaledLimb s limb a acc 0 = acc := rfl

@[simp] theorem scaledLimb.succ (s : Scaled) (limb : Fin 3) (a : K) (acc : E) (n : Nat) :
    scaledLimb s limb a acc (n + 1) =
      if h : n < 11 then
        eadd (scaledLimb s limb a acc n)
          (s.table limb ⟨n, h⟩ ⟨(a.toNat >>> (6 * n)) % 64, Nat.mod_lt _ (by decide)⟩)
      else scaledLimb s limb a acc n := rfl

def scaledMul (s : Scaled) (a : E) : E :=
  scaledLimb s 2 a.c2 (scaledLimb s 1 a.c1 (scaledLimb s 0 a.c0 Spec.Field.zero 11) 11) 11

end LeanVmXmss.Model.Field
