import Spec.Pcs.Commit
import Model.Pcs.Ntt
import Model.Layout.Scalar
import Model.Merkle.Heap

namespace LeanVmXmss.Model.Pcs.Commit

open Spec.Field (K)
open Model.Layout (zeroState25)
open Model.Pcs.Ntt (Vec8 foldRange foldRangeLoop)

def rowWords := Spec.Pcs.Commit.rowWords
def transpose := Spec.Pcs.Commit.transpose
def replicate := Spec.Pcs.Commit.replicate

def encodeMessage (message : Array K) (lanes logRows logInvRate : Nat) : Array K :=
  let width := rowWords lanes
  let first := transpose message lanes width logRows
  Model.Pcs.Ntt.encode (replicate first (1 <<< logInvRate)) width logInvRate

@[inline] def absorbWords17 (s : Model.Keccak.State25)
    (w00 w01 w02 w03 w04 w05 w06 w07 w08 w09 w10 w11 w12 w13 w14 w15 w16 : UInt64) :
    Model.Keccak.State25 :=
  Model.Keccak.keccakF1600
    { s with
      a00 := s.a00 ^^^ w00
      a01 := s.a01 ^^^ w01
      a02 := s.a02 ^^^ w02
      a03 := s.a03 ^^^ w03
      a04 := s.a04 ^^^ w04
      a05 := s.a05 ^^^ w05
      a06 := s.a06 ^^^ w06
      a07 := s.a07 ^^^ w07
      a08 := s.a08 ^^^ w08
      a09 := s.a09 ^^^ w09
      a10 := s.a10 ^^^ w10
      a11 := s.a11 ^^^ w11
      a12 := s.a12 ^^^ w12
      a13 := s.a13 ^^^ w13
      a14 := s.a14 ^^^ w14
      a15 := s.a15 ^^^ w15
      a16 := s.a16 ^^^ w16 }

@[inline] def absorbFinal13 (s : Model.Keccak.State25)
    (w00 w01 w02 w03 w04 w05 w06 w07 w08 w09 w10 w11 w12 : UInt64) :
    Model.Merkle.Digest32 :=
  let st := Model.Keccak.keccakF1600
    { s with
      a00 := s.a00 ^^^ w00
      a01 := s.a01 ^^^ w01
      a02 := s.a02 ^^^ w02
      a03 := s.a03 ^^^ w03
      a04 := s.a04 ^^^ w04
      a05 := s.a05 ^^^ w05
      a06 := s.a06 ^^^ w06
      a07 := s.a07 ^^^ w07
      a08 := s.a08 ^^^ w08
      a09 := s.a09 ^^^ w09
      a10 := s.a10 ^^^ w10
      a11 := s.a11 ^^^ w11
      a12 := s.a12 ^^^ w12
      a13 := s.a13 ^^^ 1
      a16 := s.a16 ^^^ 0x8000000000000000 }
  ⟨st.a00, st.a01, st.a02, st.a03⟩

@[inline] def hashPair25 (left right : Model.Merkle.Digest32) : Model.Merkle.Digest32 :=
  let st := Model.Keccak.keccakF1600
    { zeroState25 with
      a00 := left.lo0
      a01 := left.lo1
      a02 := left.hi0
      a03 := left.hi1
      a04 := right.lo0
      a05 := right.lo1
      a06 := right.hi0
      a07 := right.hi1
      a08 := 1
      a16 := 0x8000000000000000 }
  ⟨st.a00, st.a01, st.a02, st.a03⟩

def subtreeRoot (leafAt : Nat → Model.Merkle.Digest32) (k : Nat) : Nat → Model.Merkle.Digest32 :=
  Nat.rec (motive := fun _ => Nat → Model.Merkle.Digest32)
    (fun base => leafAt base)
    (fun k ih base => hashPair25 (ih base) (ih (base + (1 <<< k))))
    k

def zeroPrefixState (n : Nat) : Model.Keccak.State25 :=
  Nat.rec zeroState25 (fun _ st => Model.Keccak.keccakF1600 st) n

@[inline] def hashLeafVec8From (st1 st2 st3 : Model.Keccak.State25)
    (buf : Array Vec8) (nVecs row : Nat) : Model.Merkle.Digest32 :=
  let base := row * nVecs
  let z : Vec8 := default
  let (v0, v1, v2, v3, v4, v5, v6, v7) :=
    match nVecs with
    | 0 => (z, z, z, z, z, z, z, z)
    | 1 => (z, z, z, z, z, z, z, buf.getD base z)
    | 2 => (z, z, z, z, z, z, buf.getD base z, buf.getD (base + 1) z)
    | 3 =>
      (z, z, z, z, z, buf.getD base z, buf.getD (base + 1) z, buf.getD (base + 2) z)
    | 4 =>
      (z, z, z, z, buf.getD base z, buf.getD (base + 1) z,
        buf.getD (base + 2) z, buf.getD (base + 3) z)
    | 5 =>
      (z, z, z, buf.getD base z, buf.getD (base + 1) z, buf.getD (base + 2) z,
        buf.getD (base + 3) z, buf.getD (base + 4) z)
    | 6 =>
      (z, z, buf.getD base z, buf.getD (base + 1) z, buf.getD (base + 2) z,
        buf.getD (base + 3) z, buf.getD (base + 4) z, buf.getD (base + 5) z)
    | 7 =>
      (z, buf.getD base z, buf.getD (base + 1) z, buf.getD (base + 2) z,
        buf.getD (base + 3) z, buf.getD (base + 4) z,
        buf.getD (base + 5) z, buf.getD (base + 6) z)
    | _ =>
      (buf.getD base z, buf.getD (base + 1) z, buf.getD (base + 2) z,
        buf.getD (base + 3) z, buf.getD (base + 4) z, buf.getD (base + 5) z,
        buf.getD (base + 6) z, buf.getD (base + 7) z)
  let s1 :=
    if nVecs ≤ 5 then st1
    else
      absorbWords17 zeroState25
        v0.w0 v0.w1 v0.w2 v0.w3 v0.w4 v0.w5 v0.w6 v0.w7
        v1.w0 v1.w1 v1.w2 v1.w3 v1.w4 v1.w5 v1.w6 v1.w7 v2.w0
  let s2 :=
    if nVecs ≤ 3 then st2
    else
      absorbWords17 s1
        v2.w1 v2.w2 v2.w3 v2.w4 v2.w5 v2.w6 v2.w7
        v3.w0 v3.w1 v3.w2 v3.w3 v3.w4 v3.w5 v3.w6 v3.w7
        v4.w0 v4.w1
  let s3 :=
    if nVecs ≤ 1 then st3
    else
      absorbWords17 s2
        v4.w2 v4.w3 v4.w4 v4.w5 v4.w6 v4.w7
        v5.w0 v5.w1 v5.w2 v5.w3 v5.w4 v5.w5 v5.w6 v5.w7
        v6.w0 v6.w1 v6.w2
  absorbFinal13 s3
    v6.w3 v6.w4 v6.w5 v6.w6 v6.w7
    v7.w0 v7.w1 v7.w2 v7.w3 v7.w4 v7.w5 v7.w6 v7.w7

def subtreeRootBuf (st1 st2 st3 : Model.Keccak.State25)
    (buf : Array Vec8) (nVecs k : Nat) : Nat → Model.Merkle.Digest32 :=
  Nat.rec (motive := fun _ => Nat → Model.Merkle.Digest32)
    (fun base => hashLeafVec8From st1 st2 st3 buf nVecs base)
    (fun k ih base => hashPair25 (ih base) (ih (base + (1 <<< k))))
    k

@[inline] def firstCosetColLoop (message : Array K) (lanes width rows rowIndex : Nat)
    (rem v : Nat) (out : Array Vec8) : Array Vec8 :=
  foldRangeLoop (fun out curV =>
    let base := 8 * curV
    let word (j : Nat) : K :=
      let col := base + j
      if col + lanes ≥ width then
        message.getD ((width - 1 - col) * rows + rowIndex) 0
      else 0
    out.push ⟨word 0, word 1, word 2, word 3, word 4, word 5, word 6, word 7⟩) rem v out

@[inline] def firstCosetRowLoop (message : Array K) (lanes nVecs rows : Nat)
    (rem rowIndex : Nat) (out : Array Vec8) : Array Vec8 :=
  foldRangeLoop (fun out curRow =>
    firstCosetColLoop message lanes (8 * nVecs) rows curRow nVecs 0 out) rem rowIndex out

def firstCosetVec8 (message : Array K) (lanes nVecs logRows : Nat) : Array Vec8 :=
  let rows := 1 <<< logRows
  firstCosetRowLoop message lanes nVecs rows rows 0 (Array.emptyWithCapacity (rows * nVecs))

@[inline] def cosetRootsLoop (table : Array K) (first : Array Vec8)
    (st1 st2 st3 : Model.Keccak.State25)
    (nVecs logRows logInvRate : Nat)
    (rem c : Nat) (acc : Array Model.Merkle.Digest32) : Array Model.Merkle.Digest32 :=
  foldRangeLoop (fun acc curC =>
    let encoded := Model.Pcs.Ntt.encodeCosetVec8 table first nVecs logRows logInvRate curC
    let root := subtreeRootBuf st1 st2 st3 encoded nVecs logRows 0
    acc.push root) rem c acc

def commitRootFast (message : Array K) (lanes logRows logInvRate : Nat) : ByteArray :=
  let nVecs := rowWords lanes / 8
  let logD := logRows + logInvRate
  let table := Model.Pcs.Ntt.evals logD
  let first := firstCosetVec8 message lanes nVecs logRows
  let st1 := zeroPrefixState 1
  let st2 := zeroPrefixState 2
  let st3 := zeroPrefixState 3
  let rate := 1 <<< logInvRate
  let roots := cosetRootsLoop table first st1 st2 st3 nVecs logRows logInvRate rate 0 #[]
  (subtreeRoot (fun i => roots.getD i default) logInvRate 0).toBytes

def leafDigest (row : Array K) : Model.Merkle.Digest32 :=
  let padded := Array.replicate (Spec.Pcs.Commit.leafWords - row.size) (0 : K) ++ row
  let w (i : Nat) : K := padded.getD i 0
  let s1 := absorbWords17 zeroState25
    (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7)
    (w 8) (w 9) (w 10) (w 11) (w 12) (w 13) (w 14) (w 15) (w 16)
  let s2 := absorbWords17 s1
    (w 17) (w 18) (w 19) (w 20) (w 21) (w 22) (w 23) (w 24)
    (w 25) (w 26) (w 27) (w 28) (w 29) (w 30) (w 31) (w 32) (w 33)
  let s3 := absorbWords17 s2
    (w 34) (w 35) (w 36) (w 37) (w 38) (w 39) (w 40) (w 41)
    (w 42) (w 43) (w 44) (w 45) (w 46) (w 47) (w 48) (w 49) (w 50)
  absorbFinal13 s3
    (w 51) (w 52) (w 53) (w 54) (w 55) (w 56) (w 57)
    (w 58) (w 59) (w 60) (w 61) (w 62) (w 63)

def leafDigests (codeword : Array K) (width : Nat) : Array Model.Merkle.Digest32 :=
  (Array.range (codeword.size / width)).map fun pos =>
    leafDigest (codeword.extract (pos * width) ((pos + 1) * width))

def rootBytes (message : Array K) (lanes logRows logInvRate : Nat) : ByteArray :=
  if 1 ≤ lanes && lanes ≤ 64 then
    commitRootFast message lanes logRows logInvRate
  else
    Spec.Pcs.Commit.root message lanes logRows logInvRate

end LeanVmXmss.Model.Pcs.Commit
