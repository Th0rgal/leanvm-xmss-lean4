import Spec.Pcs.StackOpen
import Model.Pcs.RingSwitch

namespace LeanVmXmss.Model.Pcs.StackOpen

open Spec.Field (E)
open Spec.Pcs.StackOpen (StackClaim RingSwitchClaim RingSwitchOpen Placement)

def StackClaim.value := Spec.Pcs.StackOpen.StackClaim.value
def StackClaim.span := Spec.Pcs.StackOpen.StackClaim.span
def aligned := Spec.Pcs.StackOpen.aligned
def within := Spec.Pcs.StackOpen.within

@[noinline] def eqEval (left right : Array E) : E :=
  (Array.range (min left.size right.size)).foldl (fun acc i =>
    Model.Field.nativeKaratsuba acc
      (Spec.Field.eadd Spec.Field.one (Spec.Field.eadd (left.getD i Spec.Field.zero) (right.getD i Spec.Field.zero))))
    Spec.Field.one

def indexBits := Spec.Pcs.StackOpen.indexBits

def eqAbove (p : Placement) (full : Array E) : E :=
  if decide (full.size ≥ p.variables) then
    eqEval (indexBits (p.index >>> p.variables) (full.size - p.variables))
      (full.extract p.variables full.size)
  else Spec.Field.zero

def place (p : Placement) (low full : Array E) : E :=
  if decide (low.size = p.variables) && decide (full.size ≥ p.variables) then
    Model.Field.nativeKaratsuba (eqEval low (full.extract 0 p.variables)) (eqAbove p full)
  else Spec.Field.zero

@[noinline] def ringWeight (point challenges full : Array E) : E :=
  if decide (full.size < point.size) then Spec.Field.zero else
    RingSwitch.ringWeightAt point (full.extract 0 point.size) (RingSwitch.frobeniusCoefficients challenges)

def batch (lambda : E) (weights values : Array E) : E × E :=
  let (_, target, weight) := (Array.range (min weights.size values.size)).foldl
    (fun (scale, target, weight) i =>
      (Model.Field.nativeKaratsuba scale lambda,
       Spec.Field.eadd target (Model.Field.nativeKaratsuba scale (values.getD i Spec.Field.zero)),
       Spec.Field.eadd weight (Model.Field.nativeKaratsuba scale (weights.getD i Spec.Field.zero))))
    (Spec.Field.one, Spec.Field.zero, Spec.Field.zero)
  (target, weight)

def openingTarget (lambda : E) (values : Array E) : E := (batch lambda values values).1

def prepareRing := Spec.Pcs.StackOpen.prepareRing
def finishRing := Spec.Pcs.StackOpen.finishRing
def stackedTarget := Spec.Pcs.StackOpen.stackedTarget

end LeanVmXmss.Model.Pcs.StackOpen
