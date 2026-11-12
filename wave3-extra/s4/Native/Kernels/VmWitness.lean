namespace LeanVmXmss.Native.Kernels.VmWitness

@[inline] def uget64LE (b : ByteArray) (i : USize) : UInt64 :=
  (ByteArray.get! b (i * 8).toNat).toUInt64 |||
    ((ByteArray.get! b (i * 8 + 1).toNat).toUInt64 <<< 8) |||
    ((ByteArray.get! b (i * 8 + 2).toNat).toUInt64 <<< 16) |||
    ((ByteArray.get! b (i * 8 + 3).toNat).toUInt64 <<< 24) |||
    ((ByteArray.get! b (i * 8 + 4).toNat).toUInt64 <<< 32) |||
    ((ByteArray.get! b (i * 8 + 5).toNat).toUInt64 <<< 40) |||
    ((ByteArray.get! b (i * 8 + 6).toNat).toUInt64 <<< 48) |||
    ((ByteArray.get! b (i * 8 + 7).toNat).toUInt64 <<< 56)

@[inline] def uset64LE (wq : ByteArray) (i : USize) (v : UInt64) : ByteArray :=
  let r0 := wq.set! (i * 8).toNat v.toUInt8
  let r1 := r0.set! (i * 8 + 1).toNat (v >>> 8).toUInt8
  let r2 := r1.set! (i * 8 + 2).toNat (v >>> 16).toUInt8
  let r3 := r2.set! (i * 8 + 3).toNat (v >>> 24).toUInt8
  let r4 := r3.set! (i * 8 + 4).toNat (v >>> 32).toUInt8
  let r5 := r4.set! (i * 8 + 5).toNat (v >>> 40).toUInt8
  let r6 := r5.set! (i * 8 + 6).toNat (v >>> 48).toUInt8
  let r7 := r6.set! (i * 8 + 7).toNat (v >>> 56).toUInt8
  r7

@[inline] def kernelSelect (a b i : UInt64) : UInt64 :=
  a &&& (0 - ((b >>> i) &&& 1))

@[inline] def kernelClmulByte (a b : UInt64) : UInt64 :=
  kernelSelect a b 0 ^^^ kernelSelect (a <<< 1) b 1 ^^^
    kernelSelect (a <<< 2) b 2 ^^^ kernelSelect (a <<< 3) b 3 ^^^
    kernelSelect (a <<< 4) b 4 ^^^ kernelSelect (a <<< 5) b 5 ^^^
    kernelSelect (a <<< 6) b 6 ^^^ kernelSelect (a <<< 7) b 7

@[inline] def kernelClmulByteHi (a b : UInt64) : UInt64 :=
  kernelSelect (a >>> 63) b 1 ^^^ kernelSelect (a >>> 62) b 2 ^^^
    kernelSelect (a >>> 61) b 3 ^^^ kernelSelect (a >>> 60) b 4 ^^^
    kernelSelect (a >>> 59) b 5 ^^^ kernelSelect (a >>> 58) b 6 ^^^
    kernelSelect (a >>> 57) b 7

@[inline] def kernelClmulLo (a b : UInt64) : UInt64 :=
  kernelClmulByte a b ^^^ (kernelClmulByte a (b >>> 8) <<< 8) ^^^
    (kernelClmulByte a (b >>> 16) <<< 16) ^^^ (kernelClmulByte a (b >>> 24) <<< 24) ^^^
    (kernelClmulByte a (b >>> 32) <<< 32) ^^^ (kernelClmulByte a (b >>> 40) <<< 40) ^^^
    (kernelClmulByte a (b >>> 48) <<< 48) ^^^ (kernelClmulByte a (b >>> 56) <<< 56)

@[inline] def kernelClmulHi (a b : UInt64) : UInt64 :=
  kernelSelect (a >>> 63) b 1 ^^^ kernelSelect (a >>> 62) b 2 ^^^
    kernelSelect (a >>> 61) b 3 ^^^ kernelSelect (a >>> 60) b 4 ^^^
    kernelSelect (a >>> 59) b 5 ^^^ kernelSelect (a >>> 58) b 6 ^^^
    kernelSelect (a >>> 57) b 7 ^^^ kernelSelect (a >>> 56) b 8 ^^^
    kernelSelect (a >>> 55) b 9 ^^^ kernelSelect (a >>> 54) b 10 ^^^
    kernelSelect (a >>> 53) b 11 ^^^ kernelSelect (a >>> 52) b 12 ^^^
    kernelSelect (a >>> 51) b 13 ^^^ kernelSelect (a >>> 50) b 14 ^^^
    kernelSelect (a >>> 49) b 15 ^^^ kernelSelect (a >>> 48) b 16 ^^^
    kernelSelect (a >>> 47) b 17 ^^^ kernelSelect (a >>> 46) b 18 ^^^
    kernelSelect (a >>> 45) b 19 ^^^ kernelSelect (a >>> 44) b 20 ^^^
    kernelSelect (a >>> 43) b 21 ^^^ kernelSelect (a >>> 42) b 22 ^^^
    kernelSelect (a >>> 41) b 23 ^^^ kernelSelect (a >>> 40) b 24 ^^^
    kernelSelect (a >>> 39) b 25 ^^^ kernelSelect (a >>> 38) b 26 ^^^
    kernelSelect (a >>> 37) b 27 ^^^ kernelSelect (a >>> 36) b 28 ^^^
    kernelSelect (a >>> 35) b 29 ^^^ kernelSelect (a >>> 34) b 30 ^^^
    kernelSelect (a >>> 33) b 31 ^^^ kernelSelect (a >>> 32) b 32 ^^^
    kernelSelect (a >>> 31) b 33 ^^^ kernelSelect (a >>> 30) b 34 ^^^
    kernelSelect (a >>> 29) b 35 ^^^ kernelSelect (a >>> 28) b 36 ^^^
    kernelSelect (a >>> 27) b 37 ^^^ kernelSelect (a >>> 26) b 38 ^^^
    kernelSelect (a >>> 25) b 39 ^^^ kernelSelect (a >>> 24) b 40 ^^^
    kernelSelect (a >>> 23) b 41 ^^^ kernelSelect (a >>> 22) b 42 ^^^
    kernelSelect (a >>> 21) b 43 ^^^ kernelSelect (a >>> 20) b 44 ^^^
    kernelSelect (a >>> 19) b 45 ^^^ kernelSelect (a >>> 18) b 46 ^^^
    kernelSelect (a >>> 17) b 47 ^^^ kernelSelect (a >>> 16) b 48 ^^^
    kernelSelect (a >>> 15) b 49 ^^^ kernelSelect (a >>> 14) b 50 ^^^
    kernelSelect (a >>> 13) b 51 ^^^ kernelSelect (a >>> 12) b 52 ^^^
    kernelSelect (a >>> 11) b 53 ^^^ kernelSelect (a >>> 10) b 54 ^^^
    kernelSelect (a >>> 9) b 55 ^^^ kernelSelect (a >>> 8) b 56 ^^^
    kernelSelect (a >>> 7) b 57 ^^^ kernelSelect (a >>> 6) b 58 ^^^
    kernelSelect (a >>> 5) b 59 ^^^ kernelSelect (a >>> 4) b 60 ^^^
    kernelSelect (a >>> 3) b 61 ^^^ kernelSelect (a >>> 2) b 62 ^^^
    kernelSelect (a >>> 1) b 63

@[inline] def kernelReduce (lo hi : UInt64) : UInt64 :=
  let spill := (hi >>> 63) ^^^ (hi >>> 61) ^^^ (hi >>> 60)
  let v := hi ^^^ spill
  lo ^^^ v ^^^ (v <<< 1) ^^^ (v <<< 3) ^^^ (v <<< 4)

@[inline] def kernelMul64 (a b : UInt64) : UInt64 :=
  kernelReduce (kernelClmulLo a b) (kernelClmulHi a b)

@[inline] def kernelGpowStep (acc : UInt64) : UInt64 :=
  kernelMul64 acc 2

@[inline] def copy8 (dst src : ByteArray) (d s : USize) : ByteArray :=
  let r0 := uset64LE dst d (uget64LE src s)
  let r1 := uset64LE r0 (d + 1) (uget64LE src (s + 1))
  let r2 := uset64LE r1 (d + 2) (uget64LE src (s + 2))
  let r3 := uset64LE r2 (d + 3) (uget64LE src (s + 3))
  let r4 := uset64LE r3 (d + 4) (uget64LE src (s + 4))
  let r5 := uset64LE r4 (d + 5) (uget64LE src (s + 5))
  let r6 := uset64LE r5 (d + 6) (uget64LE src (s + 6))
  let r7 := uset64LE r6 (d + 7) (uget64LE src (s + 7))
  r7

def copyChunks (n : Nat) (dst src : ByteArray) (dOff sOff : USize) : ByteArray :=
  Fin.foldl n (fun acc k =>
    copy8 acc src (dOff + USize.ofNat k.val * 8) (sOff + USize.ofNat k.val * 8)) dst

def copyWords (n : Nat) (dst src : ByteArray) (dOff sOff : USize) : ByteArray :=
  Fin.foldl n (fun acc k =>
    uset64LE acc (dOff + USize.ofNat k.val) (uget64LE src (sOff + USize.ofNat k.val))) dst

@[noinline, export lean_xmss_copy_u64_slice]
def copyU64Slice (dst src : ByteArray) (dstOff srcOff n : USize) : ByteArray :=
  let chunks := n / 8
  let rem := n % 8
  let head := copyChunks chunks.toNat dst src dstOff srcOff
  copyWords rem.toNat head src (dstOff + chunks * 8) (srcOff + chunks * 8)

@[inline] def zero8 (wq : ByteArray) (base : USize) : ByteArray :=
  let r0 := uset64LE wq base 0
  let r1 := uset64LE r0 (base + 1) 0
  let r2 := uset64LE r1 (base + 2) 0
  let r3 := uset64LE r2 (base + 3) 0
  let r4 := uset64LE r3 (base + 4) 0
  let r5 := uset64LE r4 (base + 5) 0
  let r6 := uset64LE r5 (base + 6) 0
  let r7 := uset64LE r6 (base + 7) 0
  r7

def zeroChunks (n : Nat) (wq : ByteArray) (base : USize) : ByteArray :=
  Fin.foldl n (fun acc k => zero8 acc (base + USize.ofNat k.val * 8)) wq

def zeroWords (n : Nat) (wq : ByteArray) (base : USize) : ByteArray :=
  Fin.foldl n (fun acc k => uset64LE acc (base + USize.ofNat k.val) 0) wq

@[noinline, export lean_xmss_zero_u64_fill]
def zeroU64Fill (wq : ByteArray) (base n : USize) : ByteArray :=
  let chunks := n / 8
  let rem := n % 8
  let head := zeroChunks chunks.toNat wq base
  zeroWords rem.toNat head (base + chunks * 8)

@[noinline, export lean_xmss_pack_column_u64]
def packColumnU64 (wq src : ByteArray) (base srcLen height : USize) : ByteArray :=
  if srcLen.toNat <= height.toNat then
    let copied := copyU64Slice wq src base 0 srcLen
    zeroU64Fill copied (base + srcLen) (height - srcLen)
  else
    copyU64Slice wq src base 0 height

def gpowLoop (n : Nat) (wq : ByteArray) (base : USize) (acc : UInt64) : ByteArray :=
  (Fin.foldl n (fun st k =>
    (uset64LE st.1 (base + USize.ofNat k.val) st.2, kernelGpowStep st.2)) (wq, acc)).1

@[noinline, export lean_xmss_fill_gpow_u64]
def fillGpowU64 (wq : ByteArray) (base n : USize) : ByteArray :=
  gpowLoop n.toNat wq base 1

def zeroSource : ByteArray := ByteArray.mk (Array.replicate 32768 0)

def zeroBulkChunks (n : Nat) (wq : ByteArray) (byteOff : Nat) : ByteArray :=
  Fin.foldl n (fun acc k =>
    ByteArray.copySlice zeroSource 0 acc (byteOff + k.val * 32768) 32768 false) wq

@[noinline, export lean_xmss_zero_u64_bulk]
def zeroU64Bulk (wq : ByteArray) (base n : USize) : ByteArray :=
  let chunks := n / 4096
  let rem := n % 4096
  let byteBase := (base * 8).toNat
  let head := zeroBulkChunks chunks.toNat wq byteBase
  ByteArray.copySlice zeroSource 0 head (byteBase + chunks.toNat * 32768) (rem.toNat * 8) false

@[noinline, export lean_xmss_copy_u64_bulk]
def copyU64Bulk (dst src : ByteArray) (dstOff srcOff n : USize) : ByteArray :=
  ByteArray.copySlice src (srcOff * 8).toNat dst (dstOff * 8).toNat (n * 8).toNat

@[noinline, export lean_xmss_pack_column_bulk]
def packColumnBulk (wq src : ByteArray) (base srcLen height : USize) : ByteArray :=
  if srcLen.toNat <= height.toNat then
    let copied := copyU64Bulk wq src base 0 srcLen
    zeroU64Bulk copied (base + srcLen) (height - srcLen)
  else
    copyU64Bulk wq src base 0 height

@[noinline, export lean_xmss_vm_mem_pack_lanes]
def vmMemPackLanes (wq memC0 memC1 memC2 : ByteArray) (used cells : USize)
    (loBase hiBase topBase : USize) : ByteArray :=
  let w0 := packColumnBulk wq memC0 loBase used cells
  let w1 := packColumnBulk w0 memC1 hiBase used cells
  packColumnBulk w1 memC2 topBase used cells

end LeanVmXmss.Native.Kernels.VmWitness
