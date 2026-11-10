import Std

namespace LeanVmXmss.Spec.Field

abbrev K := UInt64

def modulus : Nat := 2^64 + 2^4 + 2^3 + 2 + 1

def bit (a : K) (i : Nat) : Bool := a.toBitVec.getLsbD i

def parity (n : Nat) (f : Nat → Bool) : Bool :=
  match n with
  | 0 => false
  | n + 1 => parity n f ^^ f n

def productCoeff (a b : K) (k : Nat) : Bool :=
  parity 64 fun i => if i ≤ k then bit a (k - i) && bit b i else false

def pack (n : Nat) (f : Nat → Bool) : BitVec n :=
  match n with
  | 0 => 0
  | n + 1 => BitVec.cons (f n) (pack n f)

def polynomialProduct (a b : K) : Nat := (pack 128 (productCoeff a b)).toNat

def remainderSteps (degree divisor : Nat) : Nat → Nat → Nat
  | 0, p => p
  | n + 1, p => remainderSteps degree divisor n
      (if p.testBit (degree + n) then p ^^^ (divisor <<< n) else p)

def remainder (p : Nat) : Nat := remainderSteps 64 modulus 64 p

def add (a b : K) : K := a ^^^ b

def mul (a b : K) : K := UInt64.ofNat (remainder (polynomialProduct a b))

def square (a : K) : K := mul a a

def embedBit (b : Bool) : K := if b then 1 else 0

structure E where
  c0 : K
  c1 : K
  c2 : K
  deriving DecidableEq, BEq, Repr

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

namespace LeanVmXmss.Model.Field

open Spec.Field (K E)

def clmulSteps (a b : BitVec 64) : Nat → BitVec 128
  | 0 => 0
  | n + 1 => clmulSteps a b n ^^^ if b.getLsbD n then a.setWidth 128 <<< n else 0

def clmul (a b : K) : BitVec 128 := clmulSteps a.toBitVec b.toBitVec 64

def reduce (p : BitVec 128) : K :=
  let lo := p.setWidth 64
  let hi := (p >>> 64).setWidth 64
  let spill := (hi >>> 63) ^^^ (hi >>> 61) ^^^ (hi >>> 60)
  let v := hi ^^^ spill
  UInt64.ofBitVec (lo ^^^ v ^^^ (v <<< 1) ^^^ (v <<< 3) ^^^ (v <<< 4))

def add (a b : K) : K := a ^^^ b

def mul (a b : K) : K := reduce (clmul a b)

def spreadSteps (a : BitVec 64) : Nat → BitVec 128
  | 0 => 0
  | n + 1 => spreadSteps a n ^^^ if a.getLsbD n then (1 : BitVec 128) <<< (2 * n) else 0

def square (a : K) : K := reduce (spreadSteps a.toBitVec 64)

def eadd (a b : E) : E := ⟨a.c0 ^^^ b.c0, a.c1 ^^^ b.c1, a.c2 ^^^ b.c2⟩

def polynomialMul (a b : E) : E :=
  let p0 := mul a.c0 b.c0
  let p1 := mul a.c0 b.c1 ^^^ mul a.c1 b.c0
  let p2 := mul a.c0 b.c2 ^^^ mul a.c1 b.c1 ^^^ mul a.c2 b.c0
  let p3 := mul a.c1 b.c2 ^^^ mul a.c2 b.c1
  let p4 := mul a.c2 b.c2
  ⟨p0 ^^^ p3, p1 ^^^ p3 ^^^ p4, p2 ^^^ p4⟩

def karatsubaMul (a b : E) : E :=
  let p0 := mul a.c0 b.c0
  let p1 := mul a.c1 b.c1
  let p2 := mul a.c2 b.c2
  let e1 := mul (a.c0 ^^^ a.c1) (b.c0 ^^^ b.c1) ^^^ p0 ^^^ p1
  let e2 := mul (a.c0 ^^^ a.c2) (b.c0 ^^^ b.c2) ^^^ p0 ^^^ p2 ^^^ p1
  let e3 := mul (a.c1 ^^^ a.c2) (b.c1 ^^^ b.c2) ^^^ p1 ^^^ p2
  ⟨p0 ^^^ e3, e1 ^^^ e3 ^^^ p2, e2 ^^^ p2⟩

def mulBase (a : E) (b : K) : E := ⟨mul a.c0 b, mul a.c1 b, mul a.c2 b⟩

def esquare (a : E) : E :=
  let s0 := square a.c0
  let s1 := square a.c1
  let s2 := square a.c2
  ⟨s0, s2, s1 ^^^ s2⟩

end LeanVmXmss.Model.Field

namespace LeanVmXmss.Spec.Vm.KeccakInternal

def rotations : Array Nat := #[0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]

def constants : Array UInt64 := #[0x0000000000000001, 0x0000000000008082,
  0x800000000000808a, 0x8000000080008000, 0x000000000000808b, 0x0000000080000001,
  0x8000000080008081, 0x8000000000008009, 0x000000000000008a, 0x0000000000000088,
  0x0000000080008009, 0x000000008000000a, 0x000000008000808b, 0x800000000000008b,
  0x8000000000008089, 0x8000000000008003, 0x8000000000008002, 0x8000000000000080,
  0x000000000000800a, 0x800000008000000a, 0x8000000080008081, 0x8000000000008080,
  0x0000000080000001, 0x8000000080008008]

def rot (x : UInt64) (n : Nat) : UInt64 :=
  if n == 0 then x else (x <<< n.toUInt64) ||| (x >>> (64 - n).toUInt64)

def round (s : Array UInt64) (rc : UInt64) : Array UInt64 := Id.run do
  let mut c := Array.replicate 5 (0 : UInt64)
  for x in [:5] do
    c := c.set! x (s[x]! ^^^ s[x+5]! ^^^ s[x+10]! ^^^ s[x+15]! ^^^ s[x+20]!)
  let mut b := Array.replicate 25 (0 : UInt64)
  for y in [:5] do
    for x in [:5] do
      let d := c[(x+4)%5]! ^^^ rot c[(x+1)%5]! 1
      b := b.set! (y + 5*((2*x+3*y)%5)) (rot (s[x+5*y]! ^^^ d) rotations[x+5*y]!)
  let mut out := Array.replicate 25 (0 : UInt64)
  for y in [:5] do
    for x in [:5] do
      out := out.set! (x+5*y) (b[x+5*y]! ^^^ ((~~~b[(x+1)%5+5*y]!) &&& b[(x+2)%5+5*y]!))
  return out.set! 0 (out[0]! ^^^ rc)

def permute (s : Array UInt64) : Array UInt64 := constants.foldl round s

def hash (bytes : ByteArray) : ByteArray := Id.run do
  let padding := 136 - bytes.size % 136
  let mut input := bytes
  for i in [:padding] do
    input := input.push ((if i == 0 then 1 else 0) ||| (if i+1 == padding then 128 else 0))
  let mut s := Array.replicate 25 (0 : UInt64)
  for block in [:input.size / 136] do
    for i in [:136] do
      let offset := block*136+i
      let lane := i/8
      s := s.set! lane (s[lane]! ^^^ (input[offset]!.toUInt64 <<< ((i%8)*8).toUInt64))
    s := permute s
  let mut out := ByteArray.empty
  for i in [:32] do
    out := out.push ((s[i/8]! >>> ((i%8)*8).toUInt64).toUInt8)
  return out

def cellLanes (odd : Bool) (c : Nat) : Option Nat × Option Nat :=
  if c >= 9 || (odd && c >= 1) then (some (2*c-1), some (2*c))
  else if odd then (none, some 0)
  else if c == 8 then (some 16, none)
  else (some (2*c), some (2*c+1))

def stateOfCells (odd : Bool) (cells : Array Spec.Field.E) : Array UInt64 := Id.run do
  let mut s := Array.replicate 25 (0 : UInt64)
  for c in [:13] do
    let (lo, hi) := cellLanes odd c
    if let some i := lo then s := s.set! i (cells[c]?.getD Spec.Field.zero).c0
    if let some i := hi then s := s.set! i (cells[c]?.getD Spec.Field.zero).c1
  return s

def cellsOfState (odd : Bool) (s : Array UInt64) : Array Spec.Field.E :=
  (Array.range 13).map fun c =>
    let (lo, hi) := cellLanes odd c
    ⟨lo.map (s[·]!) |>.getD 0, hi.map (s[·]!) |>.getD 0, 0⟩

end LeanVmXmss.Spec.Vm.KeccakInternal

namespace LeanVmXmss.Spec.Xmss

open Spec.Field (E)

def readLE (bytes : ByteArray) (offset size : Nat) : UInt64 :=
  (List.range size).foldl (fun acc i => acc ||| (bytes[offset+i]!.toUInt64 <<< (8*i).toUInt64)) 0

def writeLE (x : UInt64) (size : Nat) : ByteArray :=
  ⟨(Array.range size).map fun i => if i < 8 then (x >>> (8*i).toUInt64).toUInt8 else 0⟩

def packCell (bytes : ByteArray) (offset : Nat := 0) : E :=
  ⟨readLE bytes offset 8, readLE bytes (offset+8) 8, 0⟩

def cellBytes (x : E) : ByteArray := writeLE x.c0 8 ++ writeLE x.c1 8

def cellsBytes (xs : Array E) : ByteArray := xs.foldl (fun acc x => acc ++ cellBytes x) ByteArray.empty

def gpow : Nat → UInt64
  | 0 => 1
  | n+1 =>
    let x := gpow n
    (x <<< 1) ^^^ (if x.toNat / 2^63 == 0 then 0 else 0x1b)

def count (n : Nat) : E := ⟨gpow n, 0, 0⟩

def claimGroup : Nat := 17
def bigGroups : Nat := 8

def listSplit (n : Nat) : Array E :=
  #[count (n / (claimGroup * bigGroups)), count (n % (claimGroup * bigGroups) / claimGroup), count (n % claimGroup)]

structure RawSignature where
  publicKey : ByteArray
  message : ByteArray
  signature : ByteArray
  deriving Inhabited

def recordSize : Nat := 2468

def parseRaw (bytes : ByteArray) : Except String (Array RawSignature) := do
  if bytes.size % recordSize != 0 then throw "raw record length is not a multiple of 2468"
  let mut out := #[]
  for i in [:bytes.size / recordSize] do
    let offset := i*recordSize
    out := out.push ⟨bytes.extract offset (offset+32), bytes.extract (offset+32) (offset+64), bytes.extract (offset+64) (offset+recordSize)⟩
  return out

def validateProofEnvelope (bytes : ByteArray) : Bool :=
  bytes.size >= 8 && (readLE bytes 0 8).toNat == bytes.size - 8

def claimBytes (raw : RawSignature) : ByteArray := raw.publicKey ++ raw.message

def bytesLT (a b : ByteArray) : Bool :=
  a.data.toList < b.data.toList

def sortedUnique (raw : Array RawSignature) : Array RawSignature := Id.run do
  let sorted := raw.qsort fun a b => bytesLT (claimBytes a) (claimBytes b)
  let mut out := #[]
  for x in sorted do
    if out.back?.map (fun y => claimBytes y == claimBytes x) != some true then
      out := out.push x
  return out

structure Coverage where
  signers : Array RawSignature
  rawSlots : Array Nat
  duplicates : Array RawSignature

def planCoverage (raw : Array RawSignature) : Coverage := Id.run do
  let signers := sortedUnique raw
  let mut claimed := Array.replicate signers.size false
  let mut duplicates := #[]
  let mut slots := #[]
  for x in raw do
    let pos := signers.findIdx? (fun y => claimBytes x == claimBytes y)
    match pos with
    | some p =>
      if !claimed[p]! then
        slots := slots.push p
        claimed := claimed.set! p true
      else
        slots := slots.push (signers.size + duplicates.size)
        duplicates := duplicates.push x
    | none =>
      slots := slots.push (signers.size + duplicates.size)
      duplicates := duplicates.push x
  return ⟨signers, slots, duplicates⟩

end LeanVmXmss.Spec.Xmss

namespace LeanVmXmss.Spec.Xmss

open Spec.Field (E)

def w : Nat := 2
def chainLen : Nat := 4
def layerHeight : Nat := 16
def seedTag : ByteArray := "leanXMSS".toUTF8
def top : Nat := 1 <<< 23
def digitGroup : Nat := 4
def window : Nat := 8
def recursionAggLabel : ByteArray := "leanvm/recursion-aggregation/v1".toUTF8

structure HintEntry where
  name : String
  values : Array E

def address (kind layer field index step : Nat) : ByteArray :=
  writeLE index.toUInt64 4 ++ writeLE (field ||| (layer * top)).toUInt64 3 ++
    ⟨#[UInt8.ofNat (kind ||| (step <<< 5))]⟩ ++ ⟨Array.replicate 8 0⟩

def tweakHash (pp : ByteArray) (kind layer field index step : Nat) (payload : ByteArray) : ByteArray :=
  (Vm.KeccakInternal.hash (pp ++ address kind layer field index step ++ payload)).extract 0 16

def codeword (digest : ByteArray) : Option (Array Nat) := do
  let digits := (Array.range 64).map fun i => ((digest[i/4]!.toNat >>> ((i%4)*2)) &&& 3)
  if (digits.extract 58 64).any (· != 0) || (digits.extract 0 58).foldl (· + ·) 0 != 106 then none
  else some (digits.extract 0 58)

def chain (pp : ByteArray) (layer index i start : Nat) (value : ByteArray) : ByteArray :=
  (List.range (3-start)).foldl (fun current k =>
    tweakHash pp 1 layer 0 index (start+k) (current ++ writeLE i.toUInt64 16)) value

def signatureHints (raw : RawSignature) : Except String (Array HintEntry × ByteArray) := do
  if raw.publicKey.size != 32 || raw.message.size != 32 || raw.signature.size != 2404 then
    throw "invalid XMSS record dimensions"
  let pp := raw.publicKey.extract 16 32
  let index := (readLE raw.signature 0 4).toNat
  let shifts := (Array.range 4).map fun i => index >>> (i*window)
  let mut hints : Array HintEntry := #[⟨"lx_index", shifts.map fun x => ⟨x.toUInt64, 0, 0⟩⟩,
    ⟨"lx_windows", shifts.map fun x => count (x%256)⟩]
  let mut root := raw.message
  for layer in [:2] do
    let offset := 4 + layer*1200
    let e := index >>> (layer*16)
    let randomizer := raw.signature.extract offset (offset+16)
    let digest := tweakHash pp 12 layer 0 e 0 (root ++ randomizer)
    let some digits := codeword digest | throw "invalid WOTS+C codeword"
    let starts := (Array.range 58).map fun i => raw.signature.extract (offset+16+i*16) (offset+32+i*16)
    let ends := starts.mapIdx fun i v => chain pp layer e i digits[i]! v
    root := tweakHash pp 2 layer 0 e 0 (ends.foldl (· ++ ·) ByteArray.empty)
    for level in [:16] do
      let sibling := raw.signature.extract (offset+944+level*16) (offset+960+level*16)
      hints := hints.push ⟨"lx_path", #[packCell sibling]⟩
      let pair := if (e >>> level) &&& 1 == 0 then root ++ sibling else sibling ++ root
      root := tweakHash pp 3 layer (level+1) (e >>> (level+1)) 0 pair
    hints := hints.push ⟨"randomizer", #[packCell randomizer]⟩
    hints := hints.push ⟨"lx_digits", (Array.range 15).map fun group =>
      count ((List.range (min 4 (58-group*4))).foldl (fun n j => n + digits[group*4+j]! * 4^j) 0)⟩
    for value in starts do
      hints := hints.push ⟨"chain_starts", #[packCell value]⟩
  return (hints, root)

def verifySignature (raw : RawSignature) : Bool :=
  match signatureHints raw with
  | .error _ => false
  | .ok (_, root) => root == raw.publicKey.extract 0 16

def claimListDigest (raw : Array RawSignature) : ByteArray :=
  Vm.KeccakInternal.hash (raw.foldl (fun acc x => acc ++ claimBytes x) ByteArray.empty)

def statementDigest (seed : ByteArray) (raw : Array RawSignature) (bytecodeValue : E)
    (bytecodeVars : Nat := 23) : ByteArray := Id.run do
  let header := seed ++ claimListDigest raw ++ Vm.KeccakInternal.hash ByteArray.empty ++ ⟨Array.replicate 32 0⟩
  let mut deferred := Array.replicate bytecodeVars Spec.Field.zero
  deferred := deferred.push bytecodeValue
  if deferred.size % 2 == 1 then deferred := deferred.push Spec.Field.zero
  let bytes := deferred.foldl (fun acc x => acc ++ writeLE x.c0 8 ++ writeLE x.c1 8 ++ writeLE x.c2 8) ByteArray.empty
  return Vm.KeccakInternal.hash (header ++ bytes)

def workloadHints (seed : Array E) (raw : Array RawSignature) (bytecodeValue : E) : Except String (Array HintEntry) := do
  let signers := sortedUnique raw
  let mut hints : Array HintEntry := #[⟨"meta", #[count signers.size, count 0, count signers.size,
    count 0, count 0, count 0, count 0, count 0]⟩, ⟨"fs_seed", seed⟩]
  if !signers.isEmpty then hints := hints.push ⟨"signers_split", listSplit signers.size⟩
  for x in signers do
    hints := hints.push ⟨"claims", #[packCell x.publicKey, packCell x.publicKey 16, packCell x.message, packCell x.message 16]⟩
  for i in [:signers.size] do
    hints := hints.push ⟨"raw_index", #[count i]⟩
    let (sub, _) ← signatureHints signers[i]!
    hints := hints ++ sub
  hints := hints.push ⟨"leaf_defer", #[bytecodeValue]⟩
  hints := hints.push ⟨"da_pick", #[count 0]⟩
  return hints

end LeanVmXmss.Spec.Xmss

namespace LeanVmXmss.Model.Xmss

def signatureHints := Spec.Xmss.signatureHints
def workloadHints := Spec.Xmss.workloadHints
def statementDigest := Spec.Xmss.statementDigest

end LeanVmXmss.Model.Xmss

namespace LeanVmXmss.Spec.Vm

def wordBEq (a b : Spec.Field.E) : Bool :=
  a.c0.toNat == b.c0.toNat && a.c1.toNat == b.c1.toNat && a.c2.toNat == b.c2.toNat

scoped instance : BEq Spec.Field.E := ⟨wordBEq⟩

end LeanVmXmss.Spec.Vm

namespace LeanVmXmss.Spec.Vm

open Spec.Field (E)

def maxCells : Nat := 1 <<< 28

inductive DerefMode where
  | cell | pc | fp
  deriving DecidableEq, Repr

inductive Op where
  | xor (a b c : Nat)
  | mul (a b c : Nat)
  | set (offset : Nat) (value : E)
  | deref (o1 o2 o3 : Nat) (mode : DerefMode)
  | jump (condition target frame : Nat)
  | keccak (message : Array Nat) (tail b8 cap output : Nat) (inOdd outOdd : Bool)
  deriving DecidableEq, Repr

structure Cell where
  word : E := Spec.Field.zero
  written : Bool := false
  accesses : Nat := 0
  deriving DecidableEq, Repr, Inhabited

structure Memory where
  cells : Array Cell := #[]
  links : Array (Nat × Nat) := #[]
  unconstrainedReads : Array Nat := #[]
  used : Nat := 0
  deriving DecidableEq, Repr, Inhabited

inductive Fault where
  | conflict (address : Nat) (had value : E)
  | outOfMemory
  | wildPointer (value : E)
  | notInK (value : E)
  | notCanonical (value : E)
  | backSolveThroughZero
  | badProgram
  | witness (name : String)
  | stepLimit
  deriving DecidableEq, Repr

def Memory.get (m : Memory) (address : Nat) : Cell := m.cells[address]?.getD {}

def Memory.ensure (m : Memory) (address : Nat) : Except Fault Memory :=
  if address >= maxCells then .error .outOfMemory
  else if address < m.cells.size then .ok {m with used := max m.used (address+1)}
  else .ok {m with cells := m.cells ++ Array.replicate (max (address+1) (max 65536 (2*m.cells.size))-m.cells.size) {}, used := max m.used (address+1)}

def Memory.store (m : Memory) (address : Nat) (value : E) : Except Fault Memory :=
  match m.ensure address with
  | .error fault => .error fault
  | .ok m =>
    let old := m.get address
    if old.written = true ∧ old.word ≠ value then .error (.conflict address old.word value)
    else .ok {m with cells := m.cells.set! address {old with word := value, written := true}}

def spread (fuel : Nat) (todo : List Nat) (initial : Memory) (value : E) : Except Fault Memory := do
  let mut m := initial
  let mut pending := todo
  for _ in [:fuel] do
    match pending with
    | [] => return m
    | a::rest =>
      pending := rest
      let neighbors := m.links.toList.filterMap fun (x,y) => if x == a then some y else none
      m := {m with links := m.links.filter fun (x,_) => x != a}
      for b in neighbors do
        if !(m.get b).written then pending := b::pending
        m ← m.store b value
  if pending.isEmpty then return m else throw .badProgram

def Memory.put (m : Memory) (address : Nat) (value : E) : Except Fault Memory := do
  let fuel := m.links.size+1
  let next ← m.store address value
  spread fuel [address] next value

def Memory.read (m : Memory) (address : Nat) : Except Fault (E × Memory) := do
  let m ← m.ensure address
  let old := m.get address
  let m := if old.written then m else
    {m with
      cells := m.cells.set! address {old with written := true}
      unconstrainedReads := m.unconstrainedReads.push address}
  return (old.word, m)

def Memory.bump (m : Memory) (address : Nat) : Except Fault Memory := do
  let m ← m.ensure address
  let old := m.get address
  return {m with cells := m.cells.set! address {old with accesses := old.accesses+1}}

def Memory.link (m : Memory) (a b : Nat) : Except Fault Memory := do
  let m ← m.ensure a
  let m ← m.ensure b
  return {m with links := m.links.push (a,b) |>.push (b,a)}

def epow (a : E) : Nat → E
  | 0 => Spec.Field.one
  | n+1 => Model.Field.karatsubaMul (epow a n) a

def inverse (a : E) : E := Id.run do
  let mut x := Spec.Field.one
  for i in [:192] do
    x := Model.Field.karatsubaMul x x
    if i < 191 then x := Model.Field.karatsubaMul x a
  return x

structure GPow where
  powers : Array UInt64 := #[1]
  coarse : Array (List (Nat × Nat)) := (Array.replicate 65536 []).set! 1 [(1,0)]
  deriving Inhabited

def GPow.grow (g : GPow) (n : Nat) : GPow := Id.run do
  let mut powers := g.powers
  let mut coarse := g.coarse
  for _ in [:n+1-powers.size] do
    let x := powers.back?.getD 1
    let value := (x <<< 1) ^^^ (if x.toNat / 2^63 == 0 then 0 else 0x1b)
    let index := powers.size
    powers := powers.push value
    if index % 64 == 0 then
      let bucket := value.toNat % 65536
      coarse := coarse.modify bucket (fun xs => (value.toNat,index)::xs)
  return ⟨powers, coarse⟩

def GPow.log (g : GPow) (value : E) : Except Fault Nat := do
  if value.c1.toNat != 0 || value.c2.toNat != 0 then throw (.notInK value)
  let mut y := value.c0
  for j in [:64] do
    if let some (_, index) := (g.coarse[y.toNat % 65536]?.getD []).find? (fun pair => pair.1 == y.toNat) then
      if index+j < g.powers.size then return index+j
    y := if y.toNat % 2 == 1 then ((y ^^^ 0x1b) >>> 1) ||| ((1 : UInt64) <<< 63) else y >>> 1
  throw (.wildPointer value)

structure State where
  memory : Memory := {}
  pc : Nat := 0
  fp : Nat := 0
  nextFree : Nat := 2
  g : GPow := {}
  cycles : Nat := 0
  opcodeCounts : Array Nat := Array.replicate 6 0
  deriving Inhabited

def opcode : Op → Nat
  | .xor .. => 0
  | .mul .. => 1
  | .set .. => 2
  | .deref .. => 3
  | .jump .. => 4
  | .keccak .. => 5

def step (op : Op) (s : State) : Except Fault State := do
  let ⟨memory, oldPc, oldFp, nextFree, oldG, cycles, opcodeCounts⟩ := s
  let mut m := memory
  let mut pc := oldPc+1
  let mut fp := oldFp
  let g := oldG.grow (max (oldPc+2) oldFp)
  let mut addresses := #[]
  match op with
  | .set offset value =>
    m ← m.put (fp+offset) value
    addresses := #[fp+offset]
  | .xor a b c | .mul a b c =>
    let isMul := match op with | .mul .. => true | _ => false
    let aa := fp+a
    let ab := fp+b
    let ac := fp+c
    if isMul && (m.get ac).written then
      let ha := (m.get aa).written
      let hb := (m.get ab).written
      if ha != hb then
        let known := (m.get (if ha then aa else ab)).word
        if wordBEq known Spec.Field.zero then throw .backSolveThroughZero
        m ← m.put (if ha then ab else aa) (Model.Field.karatsubaMul (m.get ac).word (inverse known))
    let (va, next) ← m.read aa
    m := next
    let (vb, next) ← m.read ab
    m := next
    m ← m.put ac (if isMul then Model.Field.karatsubaMul va vb else Spec.Field.eadd va vb)
    addresses := #[aa,ab,ac]
  | .deref o1 o2 o3 mode =>
    let a1 := fp+o1
    let (p, next) ← m.read a1
    m := next
    let base ← g.log p
    let a2 := base+o2
    let a3 := fp+o3
    match mode with
    | .cell =>
      if (m.get a2).written then m ← m.put a3 (m.get a2).word
      else if (m.get a3).written then m ← m.put a2 (m.get a3).word
      else m ← m.link a2 a3
    | .pc => m ← m.put a2 ⟨g.powers[oldPc+2]?.getD 0,0,0⟩
    | .fp => m ← m.put a2 ⟨g.powers[fp]?.getD 0,0,0⟩
    addresses := #[a1,a2,a3]
  | .jump oc od of =>
    let (c, next) ← m.read (fp+oc)
    m := next
    let (d, next) ← m.read (fp+od)
    m := next
    let (f, next) ← m.read (fp+of)
    m := next
    for value in #[c,d,f] do
      if value.c1.toNat != 0 || value.c2.toNat != 0 then throw (.notInK value)
    addresses := #[fp+oc,fp+od,fp+of]
    if c.c0.toNat != 0 then
      pc ← g.log d
      fp ← g.log f
  | .keccak message tail b8 cap output inOdd outOdd =>
    if message.size != 4 then throw .badProgram
    let inputs := (message ++ (Array.range 4).map (tail+·) |>.push b8) ++ (Array.range 4).map (cap+·)
    let mut cells := #[]
    for address in inputs do
      let (value, next) ← m.read (fp+address)
      m := next
      if value.c2.toNat != 0 then throw (.notCanonical value)
      cells := cells.push value
    let result := KeccakInternal.cellsOfState outOdd (KeccakInternal.permute (KeccakInternal.stateOfCells inOdd cells))
    for i in [:13] do
      m ← m.put (fp+output+i) (result[i]?.getD Spec.Field.zero)
    addresses := inputs.map (fp+·) ++ (Array.range 13).map (fun i => fp+output+i)
  for address in addresses do m ← m.bump address
  let counts := opcodeCounts.modify (opcode op) (·+1)
  return ⟨m, pc, fp, nextFree, g, cycles+1, counts⟩

end LeanVmXmss.Spec.Vm

namespace LeanVmXmss.Spec.Vm

def encodeOp (op : Op) : ByteArray := Id.run do
  let (tag, words) : Nat × Array UInt64 := match op with
    | .xor a b c => (0, #[a.toUInt64,b.toUInt64,c.toUInt64])
    | .mul a b c => (1, #[a.toUInt64,b.toUInt64,c.toUInt64])
    | .set o k => (2, #[o.toUInt64,k.c0,k.c1,k.c2])
    | .deref a b c mode => (3, #[a.toUInt64,b.toUInt64,c.toUInt64,
        match mode with | .cell => 0 | .pc => 1 | .fp => 2])
    | .jump a b c => (4, #[a.toUInt64,b.toUInt64,c.toUInt64])
    | .keccak m tail b8 cap out i o => (5, m.map Nat.toUInt64 ++
        #[tail.toUInt64,b8.toUInt64,cap.toUInt64,out.toUInt64,if i then 1 else 0,if o then 1 else 0])
  return words.foldl (fun acc n => acc ++ Xmss.writeLE n 8) ⟨#[tag.toUInt8]⟩

def decodeOp (bytes : ByteArray) (offset : Nat) : Except String (Op × Nat) := do
  if offset >= bytes.size then throw "missing opcode"
  let tag := bytes[offset]!.toNat
  let n := if tag == 5 then 10 else if tag == 2 || tag == 3 then 4 else 3
  let endOffset := offset+1+8*n
  if endOffset > bytes.size then throw "truncated instruction"
  let words := (Array.range n).map fun i => Xmss.readLE bytes (offset+1+8*i) 8
  let a := words[0]!.toNat
  let b := words[1]!.toNat
  let c := words[2]!.toNat
  let op ← match tag with
    | 0 => pure (.xor a b c)
    | 1 => pure (.mul a b c)
    | 2 => pure (.set a ⟨words[1]!,words[2]!,words[3]!⟩)
    | 3 => do
      let mode ← match words[3]!.toNat with
        | 0 => pure DerefMode.cell
        | 1 => pure DerefMode.pc
        | 2 => pure DerefMode.fp
        | _ => throw "invalid dereference mode"
      pure (.deref a b c mode)
    | 4 => pure (.jump a b c)
    | 5 => do
      if words[8]!.toNat > 1 || words[9]!.toNat > 1 then throw "invalid Keccak parity"
      pure (.keccak ((words.extract 0 4).map UInt64.toNat) words[4]!.toNat words[5]!.toNat
        words[6]!.toNat words[7]!.toNat (words[8]!.toNat == 1) (words[9]!.toNat == 1))
    | _ => throw "unknown opcode"
  return (op,endOffset)

def load (bytes : ByteArray) : Except String (Array Op) := do
  let mut offset := 0
  let mut out := #[]
  for _ in [:bytes.size+1] do
    if offset == bytes.size then return out
    let (op, next) ← decodeOp bytes offset
    offset := next
    out := out.push op
  throw "bytecode load limit"

def exportBytes (ops : Array Op) : ByteArray := ops.foldl (fun acc op => acc ++ encodeOp op) ByteArray.empty

end LeanVmXmss.Spec.Vm

namespace LeanVmXmss.Tests.Xmss

open Spec.Xmss

def hintBytes (hints : Array HintEntry) : ByteArray := hints.foldl (fun acc h =>
  let name := h.name.toUTF8
  let header := writeLE name.size.toUInt64 4 ++ name ++ writeLE h.values.size.toUInt64 4
  let words := h.values.foldl (fun bytes x => bytes ++ writeLE x.c0 8 ++ writeLE x.c1 8 ++ writeLE x.c2 8) ByteArray.empty
  acc ++ header ++ words) ByteArray.empty

def hex (bytes : ByteArray) : String := String.ofList (bytes.data.toList.flatMap fun b =>
  let digits := "0123456789abcdef".toList.toArray
  [digits[b.toNat/16]!, digits[b.toNat%16]!])

def execute (input output : System.FilePath) : IO Unit := do
  let bytes ← IO.FS.readBinFile input
  let raw ← match parseRaw bytes with
    | .ok raw => pure raw
    | .error e => throw (IO.userError e)
  let seed ← IO.FS.readBinFile (output / "seed.bin")
  let value ← IO.FS.readBinFile (output / "bytecode-value.bin")
  let value : Spec.Field.E := ⟨readLE value 0 8,0,0⟩
  for x in raw do
    unless verifySignature x do throw (IO.userError "Lean signature verification failed")
  let hints ← match workloadHints #[packCell seed, packCell seed 16] raw value with
    | .ok hints => pure hints
    | .error e => throw (IO.userError e)
  let encoded := hintBytes hints
  let expected ← IO.FS.readBinFile (output / "hints.bin")
  unless encoded == expected do throw (IO.userError "Lean/Rust hint byte mismatch")
  let digest := statementDigest seed (sortedUnique raw) value
  let expectedDigest ← IO.FS.readBinFile (output / "statement.bin")
  unless digest == expectedDigest do throw (IO.userError "Lean/Rust statement mismatch")
  let bytecode ← IO.FS.readBinFile (output / "bytecode.bin")
  let ops ← match Spec.Vm.load bytecode with
    | .ok ops => pure ops
    | .error e => throw (IO.userError e)
  unless Spec.Vm.exportBytes ops == bytecode do throw (IO.userError "bytecode roundtrip failed")
  IO.println s!"records={raw.size} hint_entries={hints.size} hint_bytes={encoded.size} instructions={ops.size}"
  IO.println s!"statement_digest={hex digest}"
  IO.println s!"hints_keccak256={hex (Spec.Vm.KeccakInternal.hash encoded)}"

end LeanVmXmss.Tests.Xmss

def main (args : List String) : IO Unit := do
  match args with
  | [input, output] => LeanVmXmss.Tests.Xmss.execute input output
  | _ => throw (IO.userError "expected raw input and oracle output directory")