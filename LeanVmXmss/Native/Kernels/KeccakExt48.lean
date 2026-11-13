import Native.Kernels.Keccak8x

namespace LeanVmXmss.Native.Kernels.KeccakExt48

open Native.Kernels.Ntt (loadU64 storeU64 zeroByteArray foldUSize)
open Native.Kernels.Keccak8x

/-- Exactly 48 data words: two full rate blocks and 14 words plus Keccak padding.
This is a separate format from the existing 64-word padded L0 leaf kernel. -/
@[inline] def hash8At (codeword : @& ByteArray) (rowBase : USize)
    (out : ByteArray) (outBase : USize) : ByteArray :=
  let s1 := absorb17x8 (splatState25 zeroState25)
    (gatherLeafWord8 codeword rowBase 384 48 0 0)
    (gatherLeafWord8 codeword rowBase 384 48 0 1)
    (gatherLeafWord8 codeword rowBase 384 48 0 2)
    (gatherLeafWord8 codeword rowBase 384 48 0 3)
    (gatherLeafWord8 codeword rowBase 384 48 0 4)
    (gatherLeafWord8 codeword rowBase 384 48 0 5)
    (gatherLeafWord8 codeword rowBase 384 48 0 6)
    (gatherLeafWord8 codeword rowBase 384 48 0 7)
    (gatherLeafWord8 codeword rowBase 384 48 0 8)
    (gatherLeafWord8 codeword rowBase 384 48 0 9)
    (gatherLeafWord8 codeword rowBase 384 48 0 10)
    (gatherLeafWord8 codeword rowBase 384 48 0 11)
    (gatherLeafWord8 codeword rowBase 384 48 0 12)
    (gatherLeafWord8 codeword rowBase 384 48 0 13)
    (gatherLeafWord8 codeword rowBase 384 48 0 14)
    (gatherLeafWord8 codeword rowBase 384 48 0 15)
    (gatherLeafWord8 codeword rowBase 384 48 0 16)
  let s2 := absorb17x8 s1
    (gatherLeafWord8 codeword rowBase 384 48 0 17)
    (gatherLeafWord8 codeword rowBase 384 48 0 18)
    (gatherLeafWord8 codeword rowBase 384 48 0 19)
    (gatherLeafWord8 codeword rowBase 384 48 0 20)
    (gatherLeafWord8 codeword rowBase 384 48 0 21)
    (gatherLeafWord8 codeword rowBase 384 48 0 22)
    (gatherLeafWord8 codeword rowBase 384 48 0 23)
    (gatherLeafWord8 codeword rowBase 384 48 0 24)
    (gatherLeafWord8 codeword rowBase 384 48 0 25)
    (gatherLeafWord8 codeword rowBase 384 48 0 26)
    (gatherLeafWord8 codeword rowBase 384 48 0 27)
    (gatherLeafWord8 codeword rowBase 384 48 0 28)
    (gatherLeafWord8 codeword rowBase 384 48 0 29)
    (gatherLeafWord8 codeword rowBase 384 48 0 30)
    (gatherLeafWord8 codeword rowBase 384 48 0 31)
    (gatherLeafWord8 codeword rowBase 384 48 0 32)
    (gatherLeafWord8 codeword rowBase 384 48 0 33)
  let s3 := absorb17x8 s2
    (gatherLeafWord8 codeword rowBase 384 48 0 34)
    (gatherLeafWord8 codeword rowBase 384 48 0 35)
    (gatherLeafWord8 codeword rowBase 384 48 0 36)
    (gatherLeafWord8 codeword rowBase 384 48 0 37)
    (gatherLeafWord8 codeword rowBase 384 48 0 38)
    (gatherLeafWord8 codeword rowBase 384 48 0 39)
    (gatherLeafWord8 codeword rowBase 384 48 0 40)
    (gatherLeafWord8 codeword rowBase 384 48 0 41)
    (gatherLeafWord8 codeword rowBase 384 48 0 42)
    (gatherLeafWord8 codeword rowBase 384 48 0 43)
    (gatherLeafWord8 codeword rowBase 384 48 0 44)
    (gatherLeafWord8 codeword rowBase 384 48 0 45)
    (gatherLeafWord8 codeword rowBase 384 48 0 46)
    (gatherLeafWord8 codeword rowBase 384 48 0 47)
    (splatLane8 1)
    zeroLane8
    (splatLane8 0x8000000000000000)
  storeDigests8x out outBase s3.a00 s3.a01 s3.a02 s3.a03

@[inline] def hash1At (codeword : @& ByteArray) (rowBase : USize)
    (out : ByteArray) (outBase : USize) : ByteArray :=
  let s1 := absorb17_1 zeroState25
    (loadU64 codeword (rowBase + 0))
    (loadU64 codeword (rowBase + 8))
    (loadU64 codeword (rowBase + 16))
    (loadU64 codeword (rowBase + 24))
    (loadU64 codeword (rowBase + 32))
    (loadU64 codeword (rowBase + 40))
    (loadU64 codeword (rowBase + 48))
    (loadU64 codeword (rowBase + 56))
    (loadU64 codeword (rowBase + 64))
    (loadU64 codeword (rowBase + 72))
    (loadU64 codeword (rowBase + 80))
    (loadU64 codeword (rowBase + 88))
    (loadU64 codeword (rowBase + 96))
    (loadU64 codeword (rowBase + 104))
    (loadU64 codeword (rowBase + 112))
    (loadU64 codeword (rowBase + 120))
    (loadU64 codeword (rowBase + 128))
  let s2 := absorb17_1 s1
    (loadU64 codeword (rowBase + 136))
    (loadU64 codeword (rowBase + 144))
    (loadU64 codeword (rowBase + 152))
    (loadU64 codeword (rowBase + 160))
    (loadU64 codeword (rowBase + 168))
    (loadU64 codeword (rowBase + 176))
    (loadU64 codeword (rowBase + 184))
    (loadU64 codeword (rowBase + 192))
    (loadU64 codeword (rowBase + 200))
    (loadU64 codeword (rowBase + 208))
    (loadU64 codeword (rowBase + 216))
    (loadU64 codeword (rowBase + 224))
    (loadU64 codeword (rowBase + 232))
    (loadU64 codeword (rowBase + 240))
    (loadU64 codeword (rowBase + 248))
    (loadU64 codeword (rowBase + 256))
    (loadU64 codeword (rowBase + 264))
  let s3 := absorb17_1 s2
    (loadU64 codeword (rowBase + 272))
    (loadU64 codeword (rowBase + 280))
    (loadU64 codeword (rowBase + 288))
    (loadU64 codeword (rowBase + 296))
    (loadU64 codeword (rowBase + 304))
    (loadU64 codeword (rowBase + 312))
    (loadU64 codeword (rowBase + 320))
    (loadU64 codeword (rowBase + 328))
    (loadU64 codeword (rowBase + 336))
    (loadU64 codeword (rowBase + 344))
    (loadU64 codeword (rowBase + 352))
    (loadU64 codeword (rowBase + 360))
    (loadU64 codeword (rowBase + 368))
    (loadU64 codeword (rowBase + 376))
    1
    0
    0x8000000000000000
  let out := storeU64 out outBase s3.a00
  let out := storeU64 out (outBase + 8) s3.a01
  let out := storeU64 out (outBase + 16) s3.a02
  storeU64 out (outBase + 24) s3.a03

/-- Hash explicit rows, including model-compatible zero defaults for missing bytes. -/
def hashLeaves (codeword : @& ByteArray) (startRow numRows : Nat) : ByteArray :=
  let out := zeroByteArray (numRows * 32)
  let groups := numRows / 8
  let base := USize.ofNat (startRow * 384)
  let out := foldUSize groups (fun out g =>
    hash8At codeword (base + g * 3072) out (g * 256)) out
  let tailBase := base + USize.ofNat (groups * 3072)
  let tailOut := USize.ofNat (groups * 256)
  foldUSize (numRows % 8) (fun out r =>
    hash1At codeword (tailBase + r * 384) out (tailOut + r * 32)) out

/-- Caller supplies a power-of-two subtree. Internal compression format is unchanged. -/
def subtreeRoot (codeword : @& ByteArray) (startRow numRows : Nat) : ByteArray :=
  let leaves := hashLeaves codeword startRow numRows
  let root := Model.Pcs.Ntt.foldRange numRows.log2
    (fun cur _ => lean_xmss_merkle_compress_level cur) leaves
  if root.size ≥ 32 then root.extract 0 32 else ByteArray.empty

end LeanVmXmss.Native.Kernels.KeccakExt48
