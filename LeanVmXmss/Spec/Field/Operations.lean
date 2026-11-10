import Spec.Field.Basic

namespace LeanVmXmss.Spec.Field

def powWith {α : Type} (multiply : α → α → α) (unit a : α) : Nat → α :=
  Nat.rec unit (fun _ prev => multiply prev a)

@[simp] theorem powWith.zero {α : Type} (m : α → α → α) (u a : α) : powWith m u a 0 = u := rfl

@[simp] theorem powWith.succ {α : Type} (m : α → α → α) (u a : α) (n : Nat) :
    powWith m u a (n + 1) = m (powWith m u a n) a := rfl

def squareNWith {α : Type} (sq : α → α) (a : α) : Nat → α :=
  Nat.rec a (fun _ prev => sq prev)

@[simp] theorem squareNWith.zero {α : Type} (sq : α → α) (a : α) : squareNWith sq a 0 = a := rfl

@[simp] theorem squareNWith.succ {α : Type} (sq : α → α) (a : α) (n : Nat) :
    squareNWith sq a (n + 1) = sq (squareNWith sq a n) := rfl

def inverseChainWith (multiply : K → K → K) (sq : K → K) (a : K) : K :=
  let t2 := multiply (sq a) a
  let t3 := multiply (sq t2) a
  let t6 := multiply (squareNWith sq t3 3) t3
  let t12 := multiply (squareNWith sq t6 6) t6
  let t24 := multiply (squareNWith sq t12 12) t12
  let t48 := multiply (squareNWith sq t24 24) t24
  let t60 := multiply (squareNWith sq t48 12) t12
  let t63 := multiply (squareNWith sq t60 3) t3
  sq t63

def pow (a : K) (n : Nat) : K := powWith mul 1 a n

def inv (a : K) : K := inverseChainWith mul square a

def masked (a mask : K) : K := a &&& mask

def sum (as : List K) : K := as.foldl add 0

def powers (a : K) (count : Nat) : List K := (List.range count).map (pow a)

def epow (a : E) (n : Nat) : E := powWith emul one a n

def frobenius (a : E) : E := ⟨a.c0, a.c2, add a.c1 a.c2⟩

def frobenius2 (a : E) : E := frobenius (frobenius a)

def norm (a : E) : K := (emul a (emul (frobenius a) (frobenius2 a))).c0

def einv (a : E) : E := mulBase (emul (frobenius a) (frobenius2 a)) (inv (norm a))

def emasked (a : E) (mask : K) : E := ⟨masked a.c0 mask, masked a.c1 mask, masked a.c2 mask⟩

def esum (as : List E) : E := as.foldl eadd zero

def epowers (a : E) (count : Nat) : List E := (List.range count).map (epow a)

def encodeBytesK (a : K) : ByteArray :=
  ⟨((List.range 8).map fun i => UInt8.ofNat (a.toNat >>> (8 * i))).toArray⟩

def readLimb (bytes : ByteArray) (offset : Nat) : K :=
  UInt64.ofNat ((List.range 8).foldl
    (fun acc i => acc + (bytes.data.toList[offset + i]!.toNat <<< (8 * i))) 0)

def decodeBytesK? (bytes : ByteArray) : Option K :=
  if bytes.size = 8 then some (readLimb bytes 0) else none

def encodeBytesE (a : E) : ByteArray :=
  encodeBytesK a.c0 ++ encodeBytesK a.c1 ++ encodeBytesK a.c2

def decodeBytesE? (bytes : ByteArray) : Option E :=
  if bytes.size = 24 then some ⟨readLimb bytes 0, readLimb bytes 8, readLimb bytes 16⟩ else none

structure Scaled where
  table : Fin 3 → Fin 11 → Fin 64 → E

def windowElement (limb : Fin 3) (window : Fin 11) (value : Fin 64) : E :=
  let k := UInt64.ofNat (remainder (value.val <<< (6 * window.val)))
  if limb.val = 0 then ⟨k, 0, 0⟩ else if limb.val = 1 then ⟨0, k, 0⟩ else ⟨0, 0, k⟩

def scaled (r : E) : Scaled := ⟨fun l w n => emul r (windowElement l w n)⟩

def scaledMul (s : Scaled) (a : E) : E :=
  ((List.finRange 3).flatMap fun l => (List.finRange 11).map fun w =>
    let k := if l.val = 0 then a.c0 else if l.val = 1 then a.c1 else a.c2
    s.table l w ⟨(k.toNat >>> (6 * w.val)) % 64, Nat.mod_lt _ (by decide)⟩).foldl eadd zero

end LeanVmXmss.Spec.Field
