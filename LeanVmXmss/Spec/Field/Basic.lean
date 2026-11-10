import Std

namespace LeanVmXmss.Spec.Field

abbrev K := UInt64

def modulus : Nat := 2^64 + 2^4 + 2^3 + 2 + 1

def bit (a : K) (i : Nat) : Bool := a.toBitVec.getLsbD i

def parity (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec false (fun i acc => acc ^^ f i) n

@[simp] theorem parity.zero (f : Nat → Bool) : parity 0 f = false := rfl

@[simp] theorem parity.succ (n : Nat) (f : Nat → Bool) :
    parity (n + 1) f = (parity n f ^^ f n) := rfl

def productCoeff (a b : K) (k : Nat) : Bool :=
  parity 64 fun i => if i ≤ k then bit a (k - i) && bit b i else false

def pack (n : Nat) (f : Nat → Bool) : BitVec n :=
  Nat.rec (motive := fun n => BitVec n) 0 (fun i acc => BitVec.cons (f i) acc) n

@[simp] theorem pack.zero (f : Nat → Bool) : pack 0 f = 0 := rfl

@[simp] theorem pack.succ (n : Nat) (f : Nat → Bool) :
    pack (n + 1) f = BitVec.cons (f n) (pack n f) := rfl

def polynomialProduct (a b : K) : Nat := (pack 128 (productCoeff a b)).toNat

def remainderSteps (degree divisor : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun n prev p => prev (if p.testBit (degree + n) then p ^^^ (divisor <<< n) else p))

@[simp] theorem remainderSteps.zero (degree divisor p : Nat) :
    remainderSteps degree divisor 0 p = p := rfl

@[simp] theorem remainderSteps.succ (degree divisor n p : Nat) :
    remainderSteps degree divisor (n + 1) p = remainderSteps degree divisor n
      (if p.testBit (degree + n) then p ^^^ (divisor <<< n) else p) := rfl

def remainder (p : Nat) : Nat := remainderSteps 64 modulus 64 p

def add (a b : K) : K := a ^^^ b

def mul (a b : K) : K := UInt64.ofNat (remainder (polynomialProduct a b))

def square (a : K) : K := mul a a

def embedBit (b : Bool) : K := if b then 1 else 0

structure E where
  c0 : K
  c1 : K
  c2 : K
  deriving DecidableEq, Repr

instance : BEq E where
  beq a b := a.c0.toNat == b.c0.toNat && a.c1.toNat == b.c1.toNat && a.c2.toNat == b.c2.toNat

def encode (a : E) : UInt64 × UInt64 × UInt64 := (a.c0, a.c1, a.c2)

def decode (a : UInt64 × UInt64 × UInt64) : E := ⟨a.1, a.2.1, a.2.2⟩

def embed (a : K) : E := ⟨a, 0, 0⟩

def zero : E := ⟨0, 0, 0⟩

def one : E := embed 1

def y : E := ⟨0, 1, 0⟩

def eadd (a b : E) : E := ⟨add a.c0 b.c0, add a.c1 b.c1, add a.c2 b.c2⟩

def extensionProduct (a b : E) : Fin 5 → K
  | 0 => mul a.c0 b.c0
  | 1 => add (mul a.c0 b.c1) (mul a.c1 b.c0)
  | 2 => add (add (mul a.c0 b.c2) (mul a.c1 b.c1)) (mul a.c2 b.c0)
  | 3 => add (mul a.c1 b.c2) (mul a.c2 b.c1)
  | 4 => mul a.c2 b.c2

def extensionRemainder (p : Fin 5 → K) : E :=
  ⟨add (p 0) (p 3), add (add (p 1) (p 3)) (p 4), add (p 2) (p 4)⟩

def emul (a b : E) : E := extensionRemainder (extensionProduct a b)

def mulBase (a : E) (b : K) : E := emul a (embed b)

def esquare (a : E) : E := emul a a

end LeanVmXmss.Spec.Field
