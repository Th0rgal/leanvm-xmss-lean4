import Model.Prim.Slice64

namespace LeanVmXmss.Native.Kernels

@[noinline, export ln_xmss_memslice_pack_pair]
def memslicePackPair (lo hi : UInt32) : UInt64 :=
  lo.toUInt64 ||| (hi.toUInt64 <<< 32)

@[noinline, export ln_xmss_memslice_unpack_lo]
def memsliceUnpackLo (packed : UInt64) : UInt32 :=
  packed.toUInt32

@[noinline, export ln_xmss_memslice_unpack_hi]
def memsliceUnpackHi (packed : UInt64) : UInt32 :=
  (packed >>> 32).toUInt32

@[inline] def memsliceReadWordLE (bs : ByteArray) (wordIdx : USize) : UInt64 :=
  Model.Prim.uget64LE bs wordIdx

@[noinline, export ln_xmss_memslice_xor8_words]
def memsliceXor8Words (w0 w1 w2 w3 w4 w5 w6 w7 : UInt64) : UInt64 :=
  (w0 ^^^ w1) ^^^ (w2 ^^^ w3) ^^^ (w4 ^^^ w5) ^^^ (w6 ^^^ w7)

end LeanVmXmss.Native.Kernels
