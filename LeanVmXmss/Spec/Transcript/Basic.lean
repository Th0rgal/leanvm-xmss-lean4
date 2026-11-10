import Spec.Merkle.Basic

namespace LeanVmXmss.Spec.Transcript

open Spec.Field (E)

def DS_OBSERVE : UInt64 := 1
def DS_POW_NONCE : UInt64 := 4

structure Sponge where
  state : Keccak.State
  pending : Nat

def duplex (s : Sponge) : E × Sponge :=
  let a := Keccak.permute s.state
  (⟨a[0]!, a[1]!, a[2]!⟩,
    ⟨(Array.range 25).map (fun i => if i < 16 then 0 else a[i]!), 0⟩)

def absorb (s : Sponge) (x : E) (tag : UInt64) : Sponge :=
  let s := if s.pending == 4 then (duplex s).2 else s
  let i := 4 * s.pending
  ⟨(((s.state.set! i x.c0).set! (i + 1) x.c1).set! (i + 2) x.c2).set! (i + 3) tag,
    s.pending + 1⟩

def observe (s : Sponge) (x : E) : Sponge := absorb s x DS_OBSERVE
def challenge (s : Sponge) : E × Sponge := duplex s

def init (iv publicInput : ByteArray) : Sponge :=
  (duplex ⟨(Array.range 25).map (fun i =>
    if i < 4 then Keccak.wordAt iv (8 * i)
    else if i < 8 then Keccak.wordAt publicInput (8 * (i - 4)) else 0), 0⟩).2

def fromLabel (label : ByteArray) : Sponge := init (Keccak.keccak256 label) ByteArray.empty

def observeDigest (s : Sponge) (d : ByteArray) : Sponge :=
  let p := Merkle.hashToScalars d
  observe (observe s p.1) p.2

def nonceProbe (s : Sponge) (nonce : E) : E × Sponge := challenge (absorb s nonce DS_POW_NONCE)

def mask (bits : Nat) : UInt64 := if bits < 64 then (1 <<< UInt64.ofNat bits) - 1 else 0xffffffffffffffff

def powBitsOk (s : Sponge) (nonce : E) (bits : Nat) : Bool :=
  decide ((nonceProbe s nonce).1.c0 &&& mask bits = 0)

def verifyPow (s : Sponge) (nonce : E) (bits : Nat) : Bool × Sponge :=
  let p := nonceProbe s nonce
  (if bits == 0 then decide (nonce.c0 = 0 ∧ nonce.c1 = 0 ∧ nonce.c2 = 0)
   else decide (p.1.c0 &&& mask bits = 0), p.2)

def searchNonce (s : Sponge) (bits fuel : Nat) : UInt64 → Option UInt64 :=
  Nat.rec (fun _ => none) (fun _ previous n =>
    if powBitsOk s ⟨n, 0, 0⟩ bits then some n else previous (n + 1)) fuel

def powGrinding (s : Sponge) (bits fuel : Nat) : Option (UInt64 × Sponge) :=
  if bits ≥ 64 then none else
  let n := if bits == 0 then some 0 else searchNonce s bits fuel 0
  n.map fun n => (n, (nonceProbe s ⟨n, 0, 0⟩).2)

structure ProverState where
  sponge : Sponge
  stream : Array E
  merkle : Array ByteArray

def proverNew (iv publicInput : ByteArray) : ProverState := ⟨init iv publicInput, #[], #[]⟩
def proverFromLabel (label : ByteArray) : ProverState := ⟨fromLabel label, #[], #[]⟩

def addScalar (s : ProverState) (x : E) : ProverState :=
  { s with sponge := observe s.sponge x, stream := s.stream.push x }

def addScalars (s : ProverState) (xs : Array E) : ProverState := xs.foldl addScalar s

def addRoot (s : ProverState) (d : ByteArray) : ProverState :=
  let p := Merkle.hashToScalars d
  addScalar (addScalar s p.1) p.2

def addRoundPoly (s : ProverState) (coeffs : Array E) (eq : Bool) : ProverState :=
  ((Array.range coeffs.size).filter fun i => i != (if eq then 0 else 1)).foldl
    (fun s i => addScalar s (coeffs[i]?.getD ⟨0, 0, 0⟩)) s

def hintMerkle (s : ProverState) (bytes : ByteArray) : ProverState :=
  { s with merkle := s.merkle.push bytes }

def sample (s : ProverState) : E × ProverState :=
  let p := challenge s.sponge
  (p.1, { s with sponge := p.2 })

def grind (s : ProverState) (bits fuel : Nat) : Option (UInt64 × ProverState) :=
  (powGrinding s.sponge bits fuel).map fun (n, fs) =>
    (n, { s with sponge := fs, stream := s.stream.push ⟨n, 0, 0⟩ })

def scalarBytes (x : E) : ByteArray := Keccak.wordsBytes #[x.c0, x.c1, x.c2]

def proofBytes (s : ProverState) : ByteArray :=
  s.stream.foldl (fun b x => b ++ scalarBytes x) ByteArray.empty

end LeanVmXmss.Spec.Transcript
