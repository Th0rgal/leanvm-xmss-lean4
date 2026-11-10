import Spec.Pcs.RingSwitch

namespace LeanVmXmss.Spec.Pcs.StackOpen

open Spec.Field (K E zero one eadd emul embed mulBase)

inductive StackClaim where
  | point (offset : Nat) (lowPoint : Array E) (value : E)

def StackClaim.value : StackClaim → E
  | .point _ _ value => value

def StackClaim.span : StackClaim → Nat
  | .point _ lowPoint _ => 1 <<< lowPoint.size

def StackClaim.range : StackClaim → Nat × Nat
  | .point offset lowPoint _ => (offset, offset + (1 <<< lowPoint.size))

structure RingSwitchClaim where
  suffixPoint : Array E
  slices : Array E
  deriving Inhabited

structure RingSwitchOpen where
  offset : Nat
  claims : Array RingSwitchClaim
  deriving Inhabited

def RingSwitchOpen.qkeccakVars (ring : RingSwitchOpen) : Nat :=
  ring.claims[0]?.map (fun claim => claim.suffixPoint.size) |>.getD 0

def aligned (offset vars : Nat) : Bool :=
  decide (offset % (1 <<< vars) = 0)

def within (stackLen : Nat) (offset span : Nat) : Bool :=
  decide (offset + span ≤ stackLen)

def ringFits (stackLen : Nat) (ring : RingSwitchOpen) : Bool :=
  let vars := ring.qkeccakVars
  aligned ring.offset vars && within stackLen ring.offset (1 <<< vars) &&
    ring.claims.all fun claim =>
      decide (claim.suffixPoint.size = vars) && decide (claim.slices.size = RingSwitch.packingWidth)

def pointsFit (stackLen : Nat) (points : Array StackClaim) : Bool :=
  points.all fun claim => within stackLen claim.range.1 (claim.span)

def eqEval (left right : Array E) : E :=
  (Array.range (min left.size right.size)).foldl (fun acc i =>
    emul acc (eadd one (eadd (left.getD i zero) (right.getD i zero)))) one

def indexBits (index len : Nat) : Array E :=
  (Array.range len).map fun k => embed (if index.testBit k then 1 else 0)

structure Placement where
  variables : Nat
  index : Nat
  deriving Inhabited, DecidableEq

def eqAbove (p : Placement) (full : Array E) : E :=
  if decide (full.size ≥ p.variables) then
    let high := full.extract p.variables full.size
    eqEval (indexBits (p.index >>> p.variables) high.size) high
  else zero

def place (p : Placement) (low : Array E) (full : Array E) : E :=
  if decide (low.size = p.variables) && decide (full.size ≥ p.variables) then
    emul (eqEval low (full.extract 0 p.variables)) (eqAbove p full)
  else zero

def ringWeight (point challenges full : Array E) : E :=
  let cut := point.size
  if decide (full.size < cut) then zero else
    let low := full.extract 0 cut
    RingSwitch.ringWeightAt point low (RingSwitch.frobeniusCoefficients challenges)

def batch (lambda : E) (weights values : Array E) : E × E :=
  let (_, target, weight) := (Array.range (min weights.size values.size)).foldl
    (fun (scale, target, weight) i =>
      (emul scale lambda,
       eadd target (emul scale (values.getD i zero)),
       eadd weight (emul scale (weights.getD i zero))))
    (one, zero, zero)
  (target, weight)

def openingTarget (lambda : E) (values : Array E) : E :=
  (batch lambda values values).1

structure PreparedRing where
  slices : Array E
  point : Array E

def prepareRing (packed : Array K) (point : Array E) (precomputed : Option (Array E)) :
    Option PreparedRing :=
  if decide (packed.size ≠ 1 <<< point.size) then none else
    match precomputed with
    | some slices =>
      if decide (slices.size = RingSwitch.packingWidth) then some ⟨slices, point⟩ else none
    | none =>
      let weights := (Array.range packed.size).map (RingSwitch.rsEq point)
      some ⟨RingSwitch.fold1b packed weights, point⟩

def finishRing (state : PreparedRing) (challenges : Array E) (lambda : E) :
    E × Array E × Array E :=
  let weights := RingSwitch.coordinateWeights challenges
  let columns := RingSwitch.transposeSlices state.slices
  let claim := (Array.range (min columns.size weights.size)).foldl (fun acc i =>
    eadd acc (mulBase (weights.getD i zero) (columns.getD i 0))) zero
  (emul lambda claim, weights.map (emul lambda), state.point)

def stackedTarget (lambda : E) (ringClaims pointValues : Array E) : E :=
  openingTarget lambda (ringClaims ++ pointValues)

end LeanVmXmss.Spec.Pcs.StackOpen
