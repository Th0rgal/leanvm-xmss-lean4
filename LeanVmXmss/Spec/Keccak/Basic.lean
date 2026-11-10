import Std

namespace LeanVmXmss.Spec.Keccak

abbrev State := Array UInt64

def zero : State := Array.replicate 25 0

def rc : Array UInt64 := #[0x1, 0x8082, 0x800000000000808a, 0x8000000080008000,
  0x808b, 0x80000001, 0x8000000080008081, 0x8000000000008009, 0x8a, 0x88,
  0x80008009, 0x8000000a, 0x8000808b, 0x800000000000008b, 0x8000000000008089,
  0x8000000000008003, 0x8000000000008002, 0x8000000000000080, 0x800a,
  0x800000008000000a, 0x8000000080008081, 0x8000000000008080, 0x80000001,
  0x8000000080008008]

def rho : Array Nat := #[0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43,
  25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]

def rotl (a : UInt64) (n : Nat) : UInt64 :=
  if n % 64 == 0 then a else (a <<< UInt64.ofNat (n % 64)) ||| (a >>> UInt64.ofNat (64 - n % 64))

def theta (a : State) : State :=
  let c := (Array.range 5).map fun x =>
    a[x]! ^^^ a[x + 5]! ^^^ a[x + 10]! ^^^ a[x + 15]! ^^^ a[x + 20]!
  (Array.range 25).map fun i => a[i]! ^^^ c[(i % 5 + 4) % 5]! ^^^ rotl c[(i % 5 + 1) % 5]! 1

def rhoPi (a : State) : State :=
  (Array.range 25).map fun i =>
    let j := (i % 5 + 3 * (i / 5)) % 5 + 5 * (i % 5)
    rotl a[j]! rho[j]!

def chi (a : State) : State :=
  (Array.range 25).map fun i =>
    a[i]! ^^^ ((~~~a[5 * (i / 5) + (i % 5 + 1) % 5]!) &&& a[5 * (i / 5) + (i % 5 + 2) % 5]!)

def iota (a : State) (r : UInt64) : State := a.set! 0 (a[0]! ^^^ r)

def round (a : State) (r : UInt64) : State := iota (chi (rhoPi (theta a))) r

def permute (a : State) : State := rc.foldl round a

def rounds (count : Nat) : Nat → State → State :=
  Nat.rec (fun _ s => s) (fun _ previous i s => previous (i + 1) (round s rc[i]!)) count

def keccakF1600 (s : State) : State := rounds 24 0 s

def wordAt (b : ByteArray) (offset : Nat) : UInt64 :=
  (List.range 8).foldl (fun w j => w ||| (UInt64.ofNat (b.data[offset + j]?.getD 0).toNat <<< UInt64.ofNat (8 * j))) 0

def wordBytes (w : UInt64) : ByteArray :=
  ⟨(Array.range 8).map fun j => (w >>> UInt64.ofNat (8 * j)).toUInt8⟩

def wordsBytes (ws : Array UInt64) : ByteArray :=
  ⟨ws.foldl (fun b w => b ++ (wordBytes w).data) #[]⟩

def finalBlock (tail : ByteArray) (domain : UInt8 := 1) : ByteArray :=
  let b := (List.range tail.size).foldl (fun b i => b.set! i tail[i]!) (ByteArray.mk (Array.replicate 136 0))
  let b := b.set! tail.size (b[tail.size]! ^^^ domain)
  b.set! 135 (b[135]! ^^^ 128)

def blocks (b : ByteArray) (domain : UInt8 := 1) : Array ByteArray :=
  ((Array.range (b.size / 136)).map fun i => b.extract (136 * i) (136 * (i + 1))).push
    (finalBlock (b.extract (136 * (b.size / 136)) b.size) domain)

def absorbBlock (a : State) (b : ByteArray) : State :=
  permute ((Array.range 25).map fun i => if i < 17 then a[i]! ^^^ wordAt b (8 * i) else a[i]!)

def hashWithDomain (b : ByteArray) (domain : UInt8) : ByteArray :=
  let a := (blocks b domain).foldl absorbBlock zero
  wordsBytes (a.extract 0 4)

def keccak256 (b : ByteArray) : ByteArray := hashWithDomain b 1

end LeanVmXmss.Spec.Keccak
