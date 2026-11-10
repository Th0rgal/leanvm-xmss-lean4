import Spec.Xmss.Encoding
import Spec.Vm.KeccakInternal

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
