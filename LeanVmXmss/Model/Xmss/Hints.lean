import Spec.Xmss.Hints
import Model.Keccak.Fast
import Model.Layout.Scalar
import Model.Pcs.Ntt

namespace LeanVmXmss.Model.Xmss

open Spec.Field (E)
open Spec.Xmss
open Model.Keccak (State25 keccakF1600Fast keccak256FastStream)
open Model.Layout (zeroState25 readWordLE pushWordLE gpowTable)
open Model.Pcs.Ntt (foldRange)

def signatureHints := Spec.Xmss.signatureHints
def workloadHints := Spec.Xmss.workloadHints
def statementDigest := Spec.Xmss.statementDigest

@[inline] def countFast (gpows : @& Array UInt64) (n : Nat) : E :=
  ⟨gpows.getD n 0, 0, 0⟩

@[inline] def listSplitFast (gpows : @& Array UInt64) (n : Nat) : Array E :=
  #[countFast gpows (n / (claimGroup * bigGroups)),
    countFast gpows (n % (claimGroup * bigGroups) / claimGroup),
    countFast gpows (n % claimGroup)]

@[inline] def addressWords (kind layer field index step : Nat) : UInt64 × UInt64 :=
  let idx32 := index.toUInt64 &&& 0xffffffff
  let fl24 := ((field ||| (layer * top)).toUInt64 &&& 0xffffff) <<< 32
  let ks8 := ((kind ||| (step <<< 5)).toUInt64 &&& 0xff) <<< 56
  (idx32 ||| fl24 ||| ks8, 0)

@[inline] def tweakHash2w (pp0 pp1 : UInt64) (kind layer field index step : Nat)
    (m0 m1 : UInt64) : UInt64 × UInt64 :=
  let (ad0, ad1) := addressWords kind layer field index step
  let st := keccakF1600Fast
    { zeroState25 with
      a00 := pp0
      a01 := pp1
      a02 := ad0
      a03 := ad1
      a04 := m0
      a05 := m1
      a06 := 1
      a16 := 0x8000000000000000 }
  (st.a00, st.a01)

@[inline] def tweakHash4w (pp0 pp1 : UInt64) (kind layer field index step : Nat)
    (m0 m1 m2 m3 : UInt64) : UInt64 × UInt64 :=
  let (ad0, ad1) := addressWords kind layer field index step
  let st := keccakF1600Fast
    { zeroState25 with
      a00 := pp0
      a01 := pp1
      a02 := ad0
      a03 := ad1
      a04 := m0
      a05 := m1
      a06 := m2
      a07 := m3
      a08 := 1
      a16 := 0x8000000000000000 }
  (st.a00, st.a01)

@[inline] def codewordFast (d0 d1 : UInt64) : Option (Array Nat) := Id.run do
  let mut digits := Array.emptyWithCapacity 58
  let mut sum := 0
  for i in [:32] do
    let v := ((d0 >>> (2 * i).toUInt64) &&& 3).toNat
    sum := sum + v
    digits := digits.push v
  for i in [:26] do
    let v := ((d1 >>> (2 * i).toUInt64) &&& 3).toNat
    sum := sum + v
    digits := digits.push v
  let tail := d1 >>> 52
  if tail != 0 || sum != 106 then
    return none
  else
    return some digits

@[inline] def chainFast (pp0 pp1 : UInt64) (layer index i start : Nat)
    (v0 v1 : UInt64) : UInt64 × UInt64 :=
  let steps := 3 - start
  let iw := i.toUInt64
  foldRange steps
    (fun (c0, c1) k => tweakHash4w pp0 pp1 1 layer 0 index (start + k) c0 c1 iw 0)
    (v0, v1)

def tweakHashEnds58 (pp0 pp1 : UInt64) (layer e : Nat) (ends : @& Array (UInt64 × UInt64)) :
    UInt64 × UInt64 :=
  let (ad0, ad1) := addressWords 2 layer 0 e 0
  let p (k : Nat) : UInt64 × UInt64 := ends.getD k (0, 0)
  let s0 := keccakF1600Fast
    { zeroState25 with
      a00 := pp0, a01 := pp1, a02 := ad0, a03 := ad1,
      a04 := (p 0).1, a05 := (p 0).2, a06 := (p 1).1, a07 := (p 1).2,
      a08 := (p 2).1, a09 := (p 2).2, a10 := (p 3).1, a11 := (p 3).2,
      a12 := (p 4).1, a13 := (p 4).2, a14 := (p 5).1, a15 := (p 5).2,
      a16 := (p 6).1 }
  let s1 := keccakF1600Fast
    { s0 with
      a00 := s0.a00 ^^^ (p 6).2,
      a01 := s0.a01 ^^^ (p 7).1, a02 := s0.a02 ^^^ (p 7).2,
      a03 := s0.a03 ^^^ (p 8).1, a04 := s0.a04 ^^^ (p 8).2,
      a05 := s0.a05 ^^^ (p 9).1, a06 := s0.a06 ^^^ (p 9).2,
      a07 := s0.a07 ^^^ (p 10).1, a08 := s0.a08 ^^^ (p 10).2,
      a09 := s0.a09 ^^^ (p 11).1, a10 := s0.a10 ^^^ (p 11).2,
      a11 := s0.a11 ^^^ (p 12).1, a12 := s0.a12 ^^^ (p 12).2,
      a13 := s0.a13 ^^^ (p 13).1, a14 := s0.a14 ^^^ (p 13).2,
      a15 := s0.a15 ^^^ (p 14).1, a16 := s0.a16 ^^^ (p 14).2 }
  let s2 := keccakF1600Fast
    { s1 with
      a00 := s1.a00 ^^^ (p 15).1, a01 := s1.a01 ^^^ (p 15).2,
      a02 := s1.a02 ^^^ (p 16).1, a03 := s1.a03 ^^^ (p 16).2,
      a04 := s1.a04 ^^^ (p 17).1, a05 := s1.a05 ^^^ (p 17).2,
      a06 := s1.a06 ^^^ (p 18).1, a07 := s1.a07 ^^^ (p 18).2,
      a08 := s1.a08 ^^^ (p 19).1, a09 := s1.a09 ^^^ (p 19).2,
      a10 := s1.a10 ^^^ (p 20).1, a11 := s1.a11 ^^^ (p 20).2,
      a12 := s1.a12 ^^^ (p 21).1, a13 := s1.a13 ^^^ (p 21).2,
      a14 := s1.a14 ^^^ (p 22).1, a15 := s1.a15 ^^^ (p 22).2,
      a16 := s1.a16 ^^^ (p 23).1 }
  let s3 := keccakF1600Fast
    { s2 with
      a00 := s2.a00 ^^^ (p 23).2,
      a01 := s2.a01 ^^^ (p 24).1, a02 := s2.a02 ^^^ (p 24).2,
      a03 := s2.a03 ^^^ (p 25).1, a04 := s2.a04 ^^^ (p 25).2,
      a05 := s2.a05 ^^^ (p 26).1, a06 := s2.a06 ^^^ (p 26).2,
      a07 := s2.a07 ^^^ (p 27).1, a08 := s2.a08 ^^^ (p 27).2,
      a09 := s2.a09 ^^^ (p 28).1, a10 := s2.a10 ^^^ (p 28).2,
      a11 := s2.a11 ^^^ (p 29).1, a12 := s2.a12 ^^^ (p 29).2,
      a13 := s2.a13 ^^^ (p 30).1, a14 := s2.a14 ^^^ (p 30).2,
      a15 := s2.a15 ^^^ (p 31).1, a16 := s2.a16 ^^^ (p 31).2 }
  let s4 := keccakF1600Fast
    { s3 with
      a00 := s3.a00 ^^^ (p 32).1, a01 := s3.a01 ^^^ (p 32).2,
      a02 := s3.a02 ^^^ (p 33).1, a03 := s3.a03 ^^^ (p 33).2,
      a04 := s3.a04 ^^^ (p 34).1, a05 := s3.a05 ^^^ (p 34).2,
      a06 := s3.a06 ^^^ (p 35).1, a07 := s3.a07 ^^^ (p 35).2,
      a08 := s3.a08 ^^^ (p 36).1, a09 := s3.a09 ^^^ (p 36).2,
      a10 := s3.a10 ^^^ (p 37).1, a11 := s3.a11 ^^^ (p 37).2,
      a12 := s3.a12 ^^^ (p 38).1, a13 := s3.a13 ^^^ (p 38).2,
      a14 := s3.a14 ^^^ (p 39).1, a15 := s3.a15 ^^^ (p 39).2,
      a16 := s3.a16 ^^^ (p 40).1 }
  let s5 := keccakF1600Fast
    { s4 with
      a00 := s4.a00 ^^^ (p 40).2,
      a01 := s4.a01 ^^^ (p 41).1, a02 := s4.a02 ^^^ (p 41).2,
      a03 := s4.a03 ^^^ (p 42).1, a04 := s4.a04 ^^^ (p 42).2,
      a05 := s4.a05 ^^^ (p 43).1, a06 := s4.a06 ^^^ (p 43).2,
      a07 := s4.a07 ^^^ (p 44).1, a08 := s4.a08 ^^^ (p 44).2,
      a09 := s4.a09 ^^^ (p 45).1, a10 := s4.a10 ^^^ (p 45).2,
      a11 := s4.a11 ^^^ (p 46).1, a12 := s4.a12 ^^^ (p 46).2,
      a13 := s4.a13 ^^^ (p 47).1, a14 := s4.a14 ^^^ (p 47).2,
      a15 := s4.a15 ^^^ (p 48).1, a16 := s4.a16 ^^^ (p 48).2 }
  let s6 := keccakF1600Fast
    { s5 with
      a00 := s5.a00 ^^^ (p 49).1, a01 := s5.a01 ^^^ (p 49).2,
      a02 := s5.a02 ^^^ (p 50).1, a03 := s5.a03 ^^^ (p 50).2,
      a04 := s5.a04 ^^^ (p 51).1, a05 := s5.a05 ^^^ (p 51).2,
      a06 := s5.a06 ^^^ (p 52).1, a07 := s5.a07 ^^^ (p 52).2,
      a08 := s5.a08 ^^^ (p 53).1, a09 := s5.a09 ^^^ (p 53).2,
      a10 := s5.a10 ^^^ (p 54).1, a11 := s5.a11 ^^^ (p 54).2,
      a12 := s5.a12 ^^^ (p 55).1, a13 := s5.a13 ^^^ (p 55).2,
      a14 := s5.a14 ^^^ (p 56).1, a15 := s5.a15 ^^^ (p 56).2,
      a16 := s5.a16 ^^^ (p 57).1 }
  let s7 := keccakF1600Fast
    { s6 with
      a00 := s6.a00 ^^^ (p 57).2,
      a01 := s6.a01 ^^^ 1,
      a16 := s6.a16 ^^^ 0x8000000000000000 }
  (s7.a00, s7.a01)

@[inline] def readU32LE (b : @& ByteArray) (offset : Nat) : UInt64 :=
  (b[offset]?.getD 0).toUInt64 |||
    ((b[offset + 1]?.getD 0).toUInt64 <<< 8) |||
    ((b[offset + 2]?.getD 0).toUInt64 <<< 16) |||
    ((b[offset + 3]?.getD 0).toUInt64 <<< 24)

def signatureHintsFastWith (gpows : @& Array UInt64) (raw : RawSignature) :
    Except String (Array HintEntry × (UInt64 × UInt64)) := do
  if raw.publicKey.size != 32 || raw.message.size != 32 || raw.signature.size != 2404 then
    throw "invalid XMSS record dimensions"
  let pp0 := readWordLE raw.publicKey 16
  let pp1 := readWordLE raw.publicKey 24
  let index := (readU32LE raw.signature 0).toNat
  let s0 := index
  let s1 := index >>> 8
  let s2 := index >>> 16
  let s3 := index >>> 24
  let mut hints : Array HintEntry := Array.emptyWithCapacity 154
  hints := hints.push ⟨"lx_index", #[⟨s0.toUInt64, 0, 0⟩, ⟨s1.toUInt64, 0, 0⟩, ⟨s2.toUInt64, 0, 0⟩, ⟨s3.toUInt64, 0, 0⟩]⟩
  hints := hints.push ⟨"lx_windows", #[countFast gpows (s0 % 256), countFast gpows (s1 % 256),
    countFast gpows (s2 % 256), countFast gpows (s3 % 256)]⟩
  let mut r0 := readWordLE raw.message 0
  let mut r1 := readWordLE raw.message 8
  for layer in [:2] do
    let offset := 4 + layer * 1200
    let e := index >>> (layer * 16)
    let rand0 := readWordLE raw.signature offset
    let rand1 := readWordLE raw.signature (offset + 8)
    let (d0, d1) :=
      if layer == 0 then
        let rm2 := readWordLE raw.message 16
        let rm3 := readWordLE raw.message 24
        let (ad0, ad1) := addressWords 12 0 0 e 0
        let st := keccakF1600Fast
          { zeroState25 with
            a00 := pp0, a01 := pp1, a02 := ad0, a03 := ad1,
            a04 := r0, a05 := r1, a06 := rm2, a07 := rm3,
            a08 := rand0, a09 := rand1, a10 := 1,
            a16 := 0x8000000000000000 }
        (st.a00, st.a01)
      else
        tweakHash4w pp0 pp1 12 1 0 e 0 r0 r1 rand0 rand1
    let some digits := codewordFast d0 d1 | throw "invalid WOTS+C codeword"
    let mut startsW := Array.emptyWithCapacity 58
    let mut endsW := Array.emptyWithCapacity 58
    for i in [:58] do
      let base := offset + 16 + i * 16
      let st0 := readWordLE raw.signature base
      let st1 := readWordLE raw.signature (base + 8)
      startsW := startsW.push (st0, st1)
      endsW := endsW.push (chainFast pp0 pp1 layer e i (digits.getD i 0) st0 st1)
    let (nr0, nr1) := tweakHashEnds58 pp0 pp1 layer e endsW
    r0 := nr0
    r1 := nr1
    for level in [:16] do
      let sbase := offset + 944 + level * 16
      let sib0 := readWordLE raw.signature sbase
      let sib1 := readWordLE raw.signature (sbase + 8)
      hints := hints.push ⟨"lx_path", #[⟨sib0, sib1, 0⟩]⟩
      let (pr0, pr1) :=
        if (e >>> level) &&& 1 == 0 then
          tweakHash4w pp0 pp1 3 layer (level + 1) (e >>> (level + 1)) 0 r0 r1 sib0 sib1
        else
          tweakHash4w pp0 pp1 3 layer (level + 1) (e >>> (level + 1)) 0 sib0 sib1 r0 r1
      r0 := pr0
      r1 := pr1
    hints := hints.push ⟨"randomizer", #[⟨rand0, rand1, 0⟩]⟩
    let mut digVals := Array.emptyWithCapacity 15
    for group in [:15] do
      let cnt := min 4 (58 - group * 4)
      let gval := foldRange cnt
        (fun n j => n + (digits.getD (group * 4 + j) 0) * (1 <<< (2 * j)))
        0
      digVals := digVals.push (countFast gpows gval)
    hints := hints.push ⟨"lx_digits", digVals⟩
    for i in [:58] do
      let (st0, st1) := startsW.getD i (0, 0)
      hints := hints.push ⟨"chain_starts", #[⟨st0, st1, 0⟩]⟩
  return (hints, (r0, r1))

def signatureHintsFast (raw : RawSignature) : Except String (Array HintEntry) := do
  let gpows := gpowTable 256
  let (hints, _) ← signatureHintsFastWith gpows raw
  return hints

def verifySignatureFastWith (gpows : @& Array UInt64) (raw : RawSignature) : Bool :=
  match signatureHintsFastWith gpows raw with
  | .error _ => false
  | .ok (_, (r0, r1)) =>
    r0 == readWordLE raw.publicKey 0 && r1 == readWordLE raw.publicKey 8

def verifySignatureFast (raw : RawSignature) : Bool :=
  verifySignatureFastWith (gpowTable 256) raw

def verifyAllSignaturesPar (raw : Array RawSignature) : Bool :=
  if raw.isEmpty then true
  else
    let gpows := gpowTable 256
    let n := raw.size
    let nTasks := min 16 n
    let tasks := (Array.range nTasks).map fun tid =>
      let lo := (tid * n) / nTasks
      let hi := ((tid + 1) * n) / nTasks
      Task.spawn fun _ =>
        foldRange (hi - lo)
          (fun ok step =>
            if !ok then false
            else match raw[lo + step]? with
              | some r => verifySignatureFastWith gpows r
              | none => true)
          true
    tasks.foldl (fun ok tk => ok && tk.get) true

@[inline] def cmpBytes32 (x y : @& ByteArray) : Ordering :=
  foldRange 32
    (fun acc idx =>
      match acc with
      | .eq =>
        let bx := x[idx]?.getD 0
        let by_ := y[idx]?.getD 0
        if bx < by_ then .lt
        else if bx > by_ then .gt
        else .eq
      | other => other)
    .eq

@[inline] def recordLT (a b : RawSignature) : Bool :=
  match cmpBytes32 a.publicKey b.publicKey with
  | .lt => true
  | .gt => false
  | .eq => cmpBytes32 a.message b.message == .lt

@[inline] def recordClaimEq (a b : RawSignature) : Bool :=
  a.publicKey == b.publicKey && a.message == b.message

def sortedUniqueFast (raw : Array RawSignature) : Array RawSignature := Id.run do
  let sorted := raw.qsort recordLT
  let mut out := Array.emptyWithCapacity sorted.size
  for x in sorted do
    match out.back? with
    | some y => if !recordClaimEq y x then out := out.push x
    | none => out := out.push x
  return out

def claimListDigestFast (signers : Array RawSignature) : ByteArray := Id.run do
  let mut bytes := ByteArray.emptyWithCapacity (signers.size * 64)
  for s in signers do
    bytes := bytes ++ s.publicKey ++ s.message
  return keccak256FastStream bytes

def emptyKeccak256 : ByteArray :=
  keccak256FastStream ByteArray.empty

def statementDigestFastOnSigners (seed : ByteArray) (signers : Array RawSignature)
    (bytecodeValue : E) (bytecodeVars : Nat := 23) : ByteArray := Id.run do
  let claimDigest := claimListDigestFast signers
  let totalDeferred := bytecodeVars + 1 + (if (bytecodeVars + 1) % 2 == 1 then 1 else 0)
  let mut buf := ByteArray.emptyWithCapacity (128 + totalDeferred * 24)
  buf := buf ++ seed ++ claimDigest ++ emptyKeccak256
  for _ in [:32] do buf := buf.push 0
  for _ in [:bytecodeVars] do
    buf := pushWordLE (pushWordLE (pushWordLE buf 0) 0) 0
  buf := pushWordLE (pushWordLE (pushWordLE buf bytecodeValue.c0) bytecodeValue.c1) bytecodeValue.c2
  if (bytecodeVars + 1) % 2 == 1 then
    buf := pushWordLE (pushWordLE (pushWordLE buf 0) 0) 0
  return keccak256FastStream buf

def statementDigestFast (seed : ByteArray) (raw : Array RawSignature)
    (bytecodeValue : E) (bytecodeVars : Nat := 23) : ByteArray :=
  statementDigestFastOnSigners seed (sortedUniqueFast raw) bytecodeValue bytecodeVars

def workloadHintsFastOnSigners (seed : Array E) (signers : Array RawSignature)
    (bytecodeValue : E) : Except String (Array HintEntry × Bool) := do
  let maxG := max 256 (signers.size + 16)
  let gpows := gpowTable maxG
  let n := signers.size
  let mut hints : Array HintEntry := Array.emptyWithCapacity (4 + n * 156)
  hints := hints.push ⟨"meta", #[countFast gpows n, countFast gpows 0, countFast gpows n,
    countFast gpows 0, countFast gpows 0, countFast gpows 0, countFast gpows 0, countFast gpows 0]⟩
  hints := hints.push ⟨"fs_seed", seed⟩
  if !signers.isEmpty then
    hints := hints.push ⟨"signers_split", listSplitFast gpows n⟩
  for x in signers do
    hints := hints.push ⟨"claims", #[
      ⟨readWordLE x.publicKey 0, readWordLE x.publicKey 8, 0⟩,
      ⟨readWordLE x.publicKey 16, readWordLE x.publicKey 24, 0⟩,
      ⟨readWordLE x.message 0, readWordLE x.message 8, 0⟩,
      ⟨readWordLE x.message 16, readWordLE x.message 24, 0⟩]⟩
  if n == 0 then
    hints := hints.push ⟨"leaf_defer", #[bytecodeValue]⟩
    hints := hints.push ⟨"da_pick", #[countFast gpows 0]⟩
    return (hints, true)
  let nTasks := min 16 n
  let tasks := (Array.range nTasks).map fun tid =>
    let lo := (tid * n) / nTasks
    let hi := ((tid + 1) * n) / nTasks
    Task.spawn fun _ => Id.run do
      let mut chunk : Array HintEntry := Array.emptyWithCapacity ((hi - lo) * 155)
      let mut allVerified := true
      for step in [:hi - lo] do
        let idx := lo + step
        let raw := signers.getD idx default
        chunk := chunk.push ⟨"raw_index", #[countFast gpows idx]⟩
        match signatureHintsFastWith gpows raw with
        | .error msg => return (Except.error msg : Except String (Array HintEntry × Bool))
        | .ok (sub, (r0, r1)) =>
          let ok := r0 == readWordLE raw.publicKey 0 && r1 == readWordLE raw.publicKey 8
          allVerified := allVerified && ok
          for entry in sub do
            chunk := chunk.push entry
      return .ok (chunk, allVerified)
  let mut allOk := true
  for tk in tasks do
    let (chunk, ok) ← tk.get
    allOk := allOk && ok
    for entry in chunk do
      hints := hints.push entry
  hints := hints.push ⟨"leaf_defer", #[bytecodeValue]⟩
  hints := hints.push ⟨"da_pick", #[countFast gpows 0]⟩
  return (hints, allOk)

def workloadHintsFast (seed : Array E) (raw : Array RawSignature)
    (bytecodeValue : E) : Except String (Array HintEntry) := do
  let (hints, _) ← workloadHintsFastOnSigners seed (sortedUniqueFast raw) bytecodeValue
  return hints

end LeanVmXmss.Model.Xmss
