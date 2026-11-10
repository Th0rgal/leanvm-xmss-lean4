import Spec.Pcs.RingSwitch
import Model.Field.NativeKernel

namespace LeanVmXmss.Model.Pcs.RingSwitch

open Spec.Field (K E)
open Model.Field (nativeMul nativeKaratsuba)

def nativeMulBase (a : E) (b : K) : E := ⟨nativeMul a.c0 b, nativeMul a.c1 b, nativeMul a.c2 b⟩

def nativeEpow (x : E) (n : Nat) : E := Spec.Field.powWith nativeKaratsuba Spec.Field.one x n

def nativeSquareN (a : E) (n : Nat) : E :=
  Spec.Field.squareNWith (fun x => nativeKaratsuba x x) a n

def packingWidth := Spec.Pcs.RingSwitch.packingWidth
def degreeE := Spec.Pcs.RingSwitch.degreeE
def soundnessDegree := Spec.Pcs.RingSwitch.soundnessDegree
def compositionShifts := Spec.Pcs.RingSwitch.compositionShifts
def coordinateBasis := Spec.Pcs.RingSwitch.coordinateBasis

@[noinline] def applyComposed (value : E) (challenges : Array E) : E :=
  (Array.range compositionShifts.size).foldl (fun value t =>
    let shift := compositionShifts.getD t 0
    let challenge := challenges.getD t Spec.Field.zero
    Spec.Field.eadd value (nativeKaratsuba challenge (nativeSquareN value shift))) value

def coordinateWeights (challenges : Array E) : Array E :=
  (Array.range degreeE).map fun w => applyComposed (coordinateBasis w) challenges

def frobeniusCoefficient (challenges : Array E) (k : Nat) : E :=
  (Array.range compositionShifts.size).foldl (fun acc p =>
    let shift := compositionShifts.getD p 0
    if (k &&& shift) != 0 then
      nativeKaratsuba acc (nativeSquareN (challenges.getD p Spec.Field.zero) (k % shift))
    else acc) Spec.Field.one

def frobeniusCoefficients (challenges : Array E) : Array E :=
  (Array.range packingWidth).map (frobeniusCoefficient challenges)

@[noinline] def ringWeightAt (point rPrime coefficients : Array E) : E :=
  (Array.range coefficients.size).foldl (fun (frobenius, total) k =>
    let step := (Array.range (min frobenius.size rPrime.size)).foldl
      (fun (product, next) n =>
        let value := frobenius.getD n Spec.Field.zero
        (nativeKaratsuba product
          (Spec.Field.eadd Spec.Field.one (Spec.Field.eadd value (rPrime.getD n Spec.Field.zero))),
         next.push (nativeKaratsuba value value)))
      (coefficients.getD k Spec.Field.zero, #[])
    (step.2, Spec.Field.eadd total step.1)) (point, Spec.Field.zero) |>.2

@[noinline] def fold1b (words : Array K) (weights : Array E) : Array E :=
  (Array.range packingWidth).map fun bit =>
    (Array.range (min words.size weights.size)).foldl (fun acc y =>
      if (words.getD y 0).toNat.testBit bit then
        Spec.Field.eadd acc (weights.getD y Spec.Field.zero)
      else acc) Spec.Field.zero

def transposeSlices := Spec.Pcs.RingSwitch.transposeSlices

def batchedTarget (slices challenges : Array E) : E :=
  (Array.range (min slices.size packingWidth)).foldl (fun acc i =>
    Spec.Field.eadd acc
      (nativeMulBase (applyComposed (slices.getD i Spec.Field.zero) challenges) (1 <<< UInt64.ofNat i)))
    Spec.Field.zero

end LeanVmXmss.Model.Pcs.RingSwitch
