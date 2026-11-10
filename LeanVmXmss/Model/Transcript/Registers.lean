import Model.Keccak.Registers
import Spec.Transcript.Replay

namespace LeanVmXmss.Model.Transcript.Registers

open Spec.Field (E)
open Model.Keccak (State25)

structure Elem24 where
  c0 : UInt64 := 0
  c1 : UInt64 := 0
  c2 : UInt64 := 0
  tag : UInt64 := 0
  deriving Inhabited, Repr

structure Sponge where
  state : State25
  p0 : Elem24 := default
  p1 : Elem24 := default
  p2 : Elem24 := default
  p3 : Elem24 := default
  pending : Nat := 0

def input (s : Sponge) : State25 :=
  let p0 := if s.pending > 0 then s.p0 else ⟨0, 0, 0, 0⟩
  let p1 := if s.pending > 1 then s.p1 else ⟨0, 0, 0, 0⟩
  let p2 := if s.pending > 2 then s.p2 else ⟨0, 0, 0, 0⟩
  let p3 := if s.pending > 3 then s.p3 else ⟨0, 0, 0, 0⟩
  ⟨p0.c0, p0.c1, p0.c2, p0.tag, p1.c0, p1.c1, p1.c2, p1.tag,
    p2.c0, p2.c1, p2.c2, p2.tag, p3.c0, p3.c1, p3.c2, p3.tag,
    s.state.a16, s.state.a17, s.state.a18, s.state.a19, s.state.a20,
    s.state.a21, s.state.a22, s.state.a23, s.state.a24⟩

def duplex (s : Sponge) : E × Sponge :=
  let state := Model.Keccak.keccakF1600 (input s)
  (⟨state.a00, state.a01, state.a02⟩, {s with state, pending := 0})

def absorb (s : Sponge) (x : E) (tag : UInt64) : Sponge :=
  let s := if s.pending = 4 then (duplex s).2 else s
  let value : Elem24 := ⟨x.c0, x.c1, x.c2, tag⟩
  match s.pending with
  | 0 => {s with p0 := value, pending := 1}
  | 1 => {s with p1 := value, pending := 2}
  | 2 => {s with p2 := value, pending := 3}
  | _ => {s with p3 := value, pending := 4}

def observe (s : Sponge) (x : E) : Sponge := absorb s x 1

def sample (s : Sponge) : E × Sponge := duplex s

def init (iv publicInput : ByteArray) : Sponge :=
  let state : State25 :=
    ⟨Spec.Keccak.wordAt iv 0, Spec.Keccak.wordAt iv 8,
      Spec.Keccak.wordAt iv 16, Spec.Keccak.wordAt iv 24,
      Spec.Keccak.wordAt publicInput 0, Spec.Keccak.wordAt publicInput 8,
      Spec.Keccak.wordAt publicInput 16, Spec.Keccak.wordAt publicInput 24,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  ⟨Model.Keccak.keccakF1600 state, default, default, default, default, 0⟩

def toSpec (s : Sponge) : Spec.Transcript.Sponge := ⟨(input s).toSpec, s.pending⟩

def nonceProbe (s : Sponge) (nonce : E) : E × Sponge := sample (absorb s nonce 4)

def powBitsOk (s : Sponge) (nonce : E) (bits : Nat) : Bool :=
  decide ((nonceProbe s nonce).1.c0 &&& Spec.Transcript.mask bits = 0)

def verifyPow (s : Sponge) (nonce : E) (bits : Nat) : Bool × Sponge :=
  let result := nonceProbe s nonce
  (if bits = 0 then decide (nonce = Spec.Field.zero)
    else decide (result.1.c0 &&& Spec.Transcript.mask bits = 0), result.2)

def searchNonce (s : Sponge) (bits fuel : Nat) : UInt64 → Option UInt64 :=
  Nat.rec (fun _ => none) (fun _ previous n =>
    if powBitsOk s ⟨n, 0, 0⟩ bits then some n else previous (n + 1)) fuel

def grind (s : Sponge) (bits fuel : Nat) : Option (UInt64 × Sponge) := do
  if bits ≥ 64 then none else
    let n ← if bits = 0 then some 0 else searchNonce s bits fuel 0
    some (n, (nonceProbe s ⟨n, 0, 0⟩).2)

end LeanVmXmss.Model.Transcript.Registers
