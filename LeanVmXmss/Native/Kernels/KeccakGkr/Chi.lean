import Native.Kernels.KeccakGkr.Support

namespace LeanVmXmss.Native.Kernels.KeccakGkr

set_option compiler.ignoreBorrowAnnotation true

@[inline]
def alongPos (j k : USize) : USize :=
  let lane := j / 64
  let z := j % 64
  let nextLane := (lane % 5 + k) % 5 + 5 * (lane / 5)
  64 * nextLane + z

def chiWordsAt (block : ByteArray) (n baseA baseB baseC : USize) (acc : ByteArray) : ByteArray :=
  Nat.rec (motive := fun _ => ByteArray) acc
    (fun w prev =>
      let uw := USize.ofNat w
      let wa := readWordAt block (baseA + uw)
      let wb := readWordAt block (baseB + uw)
      let wc := readWordAt block (baseC + uw)
      pushU64LE prev (chiWordD2 wa wb wc))
    n.toNat

@[noinline, export lean_xmss_keccak_chi_planes]
def keccakChiPlanes (block : ByteArray) (n : USize) : ByteArray :=
  let cap := 1600 * n.toNat * 8
  Nat.rec (motive := fun _ => ByteArray) (ByteArray.emptyWithCapacity cap)
    (fun j prev =>
      let uj := USize.ofNat j
      let p1 := alongPos uj 1
      let p2 := alongPos uj 2
      chiWordsAt block n (n * uj) (n * p1) (n * p2) prev)
    1600

end LeanVmXmss.Native.Kernels.KeccakGkr
