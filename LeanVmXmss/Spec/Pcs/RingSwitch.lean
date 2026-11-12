import Spec.Field.Operations
import Spec.Transcript.Replay

namespace LeanVmXmss.Spec.Pcs.RingSwitch

open Spec.Field (K E zero one eadd emul esquare epow mulBase embed)
open Spec.Transcript (ProverState)

def packingWidth : Nat := 64
def degreeE : Nat := 192
def soundnessDegree : Nat :=
  (1 <<< 31) + (1 <<< 15) + (1 <<< 7) + (1 <<< 3) + (1 <<< 1) + 1

def compositionShifts : Array Nat := #[32, 16, 8, 4, 2, 1]

def coordinateBasis (w : Nat) : E :=
  let i := w % 64
  let j := w / 64
  match j with
  | 0 => embed (1 <<< UInt64.ofNat i)
  | 1 => ⟨0, 1 <<< UInt64.ofNat i, 0⟩
  | _ => ⟨0, 0, 1 <<< UInt64.ofNat i⟩

def esquareN (a : E) (n : Nat) : E :=
  Spec.Field.squareNWith esquare a n

def applyComposed (value : E) (challenges : Array E) : E :=
  (Array.range compositionShifts.size).foldl (fun value t =>
    let shift := compositionShifts.getD t 0
    let challenge := challenges.getD t zero
    eadd value (emul challenge (esquareN value shift))) value

def coordinateWeights (challenges : Array E) : Array E :=
  (Array.range degreeE).map fun w => applyComposed (coordinateBasis w) challenges

def frobeniusCoefficient (challenges : Array E) (k : Nat) : E :=
  (Array.range compositionShifts.size).foldl (fun acc p =>
    let shift := compositionShifts.getD p 0
    if (k &&& shift) != 0 then
      emul acc (esquareN (challenges.getD p zero) (k % shift))
    else acc) one

def frobeniusCoefficients (challenges : Array E) : Array E :=
  (Array.range packingWidth).map (frobeniusCoefficient challenges)

def ringMap (value : E) (challenges : Array E) : E := applyComposed value challenges

def ringWeightAt (point rPrime coefficients : Array E) : E :=
  (Array.range coefficients.size).foldl (fun (frobenius, total) k =>
    let step := (Array.range (min frobenius.size rPrime.size)).foldl
      (fun (product, next) n =>
        let value := frobenius.getD n zero
        (emul product (eadd one (eadd value (rPrime.getD n zero))), next.push (esquare value)))
      (coefficients.getD k zero, #[])
    (step.2, eadd total step.1)) (point, zero) |>.2

def bitOf (word : K) (i : Nat) : E := embed (if word.toNat.testBit i then 1 else 0)

def fold1b (words : Array K) (weights : Array E) : Array E :=
  (Array.range packingWidth).map fun bit =>
    (Array.range (min words.size weights.size)).foldl (fun acc y =>
      if (words.getD y 0).toNat.testBit bit then eadd acc (weights.getD y zero) else acc) zero

def transposeSlices (slices : Array E) : Array K :=
  (Array.range degreeE).map fun w =>
    let limb := w / 64
    let bit := UInt64.ofNat (w % 64)
    (Array.range packingWidth).foldl (fun acc i =>
      let x := slices.getD i zero
      let word := if limb = 0 then x.c0 else if limb = 1 then x.c1 else x.c2
      if ((word >>> bit) &&& 1).toNat != 0 then acc ||| (1 <<< UInt64.ofNat i) else acc) 0

def batchedTarget (slices challenges : Array E) : E :=
  (Array.range (min slices.size packingWidth)).foldl (fun acc i =>
    eadd acc (mulBase (ringMap (slices.getD i zero) challenges) (1 <<< UInt64.ofNat i))) zero

def rsEq (point : Array E) (index : Nat) : E :=
  (Array.range point.size).foldl (fun acc k =>
    let r := point.getD k zero
    let bit := embed (if index.testBit k then 1 else 0)
    emul acc (eadd one (eadd r bit))) one

def weightAt (point challenges : Array E) (index : Nat) : E :=
  ringMap (rsEq point index) challenges

def polyEval (coeffs : Array E) (point : E) : E :=
  coeffs.foldr (fun c acc => eadd (emul acc point) c) zero

def foldPair (left right : Array E) (r : E) : Array E :=
  (Array.range (min left.size right.size)).map fun i =>
    let lo := left.getD i zero
    eadd lo (emul r (eadd lo (right.getD i zero)))

def foldLone (row : Array E) (r : E) : Array E :=
  (Array.range (row.size / 2)).map fun i =>
    let lo := row.getD (2 * i) zero
    eadd lo (emul r (eadd lo (row.getD (2 * i + 1) zero)))

def sumcheckMessage (left right : Array E) : Array E :=
  #[dotEval left right, dotEval (left.map esquare) right]
where
  dotEval (a b : Array E) : E :=
    (Array.range (min a.size b.size)).foldl (fun acc i =>
      eadd acc (emul (a.getD i zero) (b.getD i zero))) zero

def proveComposition (s : ProverState) (slices : Array E) :
    Option (Array E × E × ProverState) :=
  let (challenges, s) := (Array.range compositionShifts.size).foldl (fun (acc, s) _ =>
    let (x, s) := Spec.Transcript.sample s
    (acc.push x, s)) (#[], s)
  let images := slices.map fun v => applyComposed v challenges
  let target := polyEval images ⟨2, 0, 0⟩
  some (challenges, target, s)

end LeanVmXmss.Spec.Pcs.RingSwitch
