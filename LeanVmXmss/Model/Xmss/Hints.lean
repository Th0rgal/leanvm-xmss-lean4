import Spec.Xmss.Hints
import Model.Layout.Scalar

namespace LeanVmXmss.Model.Xmss

open Spec.Xmss
open Spec.Field (E)

def signatureHints := Spec.Xmss.signatureHints

def hintGpowTable : Array UInt64 := Model.Layout.gpowTable 2048

def hintCount (t : Array UInt64) (n : Nat) : E := ⟨t[n]?.getD (Spec.Xmss.gpow n), 0, 0⟩

def hashFast (b : ByteArray) : ByteArray :=
  let n := b.size / 136
  let st := (Array.range n).foldl (fun s i => Model.Layout.absorb25 s b (136 * i)) Model.Layout.zeroState25
  let fin := Model.Layout.absorb25 st (Spec.Keccak.finalBlock (b.extract (136 * n) b.size) 1) 0
  Spec.Keccak.wordsBytes #[fin.a00, fin.a01, fin.a02, fin.a03]

def tweakFast (pp : ByteArray) (k l f i s : Nat) (p : ByteArray) : ByteArray :=
  (hashFast (pp ++ address k l f i s ++ p)).extract 0 16

def chainFast (pp : ByteArray) (l i j st : Nat) (v : ByteArray) : ByteArray :=
  (List.range (3 - st)).foldl (fun c k => tweakFast pp 1 l 0 i (st + k) (c ++ writeLE j.toUInt64 16)) v

def signatureHintsFast (t : Array UInt64) (raw : RawSignature) :
    Except String (Array HintEntry × ByteArray) := do
  if raw.publicKey.size != 32 || raw.message.size != 32 || raw.signature.size != 2404 then
    throw "invalid XMSS record dimensions"
  let pp := raw.publicKey.extract 16 32
  let idx := (readLE raw.signature 0 4).toNat
  let sh := (Array.range 4).map fun i => idx >>> (i * window)
  let mut hints : Array HintEntry := #[⟨"lx_index", sh.map fun x => ⟨x.toUInt64, 0, 0⟩⟩,
    ⟨"lx_windows", sh.map fun x => hintCount t (x % 256)⟩]
  let mut root := raw.message
  for layer in [:2] do
    let o := 4 + layer * 1200
    let e := idx >>> (layer * 16)
    let rnd := raw.signature.extract o (o + 16)
    let some digits := codeword (tweakFast pp 12 layer 0 e 0 (root ++ rnd)) | throw "invalid WOTS+C codeword"
    let starts := (Array.range 58).map fun i => raw.signature.extract (o + 16 + i * 16) (o + 32 + i * 16)
    root := tweakFast pp 2 layer 0 e 0 ((starts.mapIdx fun i v => chainFast pp layer e i digits[i]! v).foldl (· ++ ·) ByteArray.empty)
    for level in [:16] do
      let sib := raw.signature.extract (o + 944 + level * 16) (o + 960 + level * 16)
      hints := hints.push ⟨"lx_path", #[packCell sib]⟩
      root := tweakFast pp 3 layer (level + 1) (e >>> (level + 1)) 0
        (if (e >>> level) &&& 1 == 0 then root ++ sib else sib ++ root)
    hints := hints.push ⟨"randomizer", #[packCell rnd]⟩
    hints := hints.push ⟨"lx_digits", (Array.range 15).map fun g =>
      hintCount t ((List.range (min 4 (58 - g * 4))).foldl (fun n j => n + digits[g * 4 + j]! * 4 ^ j) 0)⟩
    for v in starts do hints := hints.push ⟨"chain_starts", #[packCell v]⟩
  return (hints, root)

def workloadHintsCore (t : Array UInt64) (seed : Array E) (raw : Array RawSignature) (bv : E) :
    Except String (Array HintEntry) := do
  let signers := sortedUnique raw
  let mut hints : Array HintEntry := #[⟨"meta", #[hintCount t signers.size, hintCount t 0,
    hintCount t signers.size, hintCount t 0, hintCount t 0, hintCount t 0, hintCount t 0, hintCount t 0]⟩,
    ⟨"fs_seed", seed⟩]
  if !signers.isEmpty then hints := hints.push ⟨"signers_split",
    #[hintCount t (signers.size / (claimGroup * bigGroups)),
      hintCount t (signers.size % (claimGroup * bigGroups) / claimGroup), hintCount t (signers.size % claimGroup)]⟩
  for x in signers do hints := hints.push ⟨"claims",
    #[packCell x.publicKey, packCell x.publicKey 16, packCell x.message, packCell x.message 16]⟩
  for i in [:signers.size] do
    hints := hints.push ⟨"raw_index", #[hintCount t i]⟩
    let (sub, _) ← signatureHintsFast t signers[i]!
    hints := hints ++ sub
  return hints.push ⟨"leaf_defer", #[bv]⟩ |>.push ⟨"da_pick", #[hintCount t 0]⟩

def workloadHints (seed : Array E) (raw : Array RawSignature) (bv : E) : Except String (Array HintEntry) :=
  workloadHintsCore hintGpowTable seed raw bv

def statementDigest (seed : ByteArray) (raw : Array RawSignature) (bv : E) (vars : Nat := 23) : ByteArray :=
  let header := seed ++ hashFast (raw.foldl (fun acc x => acc ++ claimBytes x) ByteArray.empty) ++
    hashFast ByteArray.empty ++ ⟨Array.replicate 32 0⟩
  let deferred := (Array.range vars).foldl (fun acc _ => acc.push Spec.Field.zero) #[] |>.push bv
  let deferred := if deferred.size % 2 == 1 then deferred.push Spec.Field.zero else deferred
  hashFast (deferred.foldl (fun acc x => acc ++ writeLE x.c0 8 ++ writeLE x.c1 8 ++ writeLE x.c2 8) header)

def workloadHintsParallel (seed : Array E) (raw : Array RawSignature) (bv : E) : IO (Array HintEntry) := do
  let t := hintGpowTable
  let signers := sortedUnique raw
  let mut head : Array HintEntry := #[⟨"meta", #[hintCount t signers.size, hintCount t 0,
    hintCount t signers.size, hintCount t 0, hintCount t 0, hintCount t 0, hintCount t 0, hintCount t 0]⟩,
    ⟨"fs_seed", seed⟩]
  if !signers.isEmpty then head := head.push ⟨"signers_split",
    #[hintCount t (signers.size / (claimGroup * bigGroups)),
      hintCount t (signers.size % (claimGroup * bigGroups) / claimGroup), hintCount t (signers.size % claimGroup)]⟩
  for x in signers do head := head.push ⟨"claims",
    #[packCell x.publicKey, packCell x.publicKey 16, packCell x.message, packCell x.message 16]⟩
  let n := signers.size
  let tasks ← (Array.range 16).mapM fun p =>
    IO.asTask (prio := .dedicated) <| IO.lazyPure fun () => Id.run do
      let mut out : Array HintEntry := #[]
      let mut failed : Option String := none
      for i in [p * n / 16:(p + 1) * n / 16] do
        out := out.push ⟨"raw_index", #[hintCount t i]⟩
        match signatureHintsFast t (signers[i]!) with
        | .ok (s, _) => out := out ++ s
        | .error msg => failed := some msg
      (failed, out)
  let mut body : Array HintEntry := #[]
  for task in tasks do
    match ← IO.wait task with
    | .ok (some msg, _) => throw (IO.userError msg)
    | .ok (none, e) => body := body ++ e
    | .error e => throw e
  return head ++ body ++ #[⟨"leaf_defer", #[bv]⟩, ⟨"da_pick", #[hintCount t 0]⟩]

end LeanVmXmss.Model.Xmss
