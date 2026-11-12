import Native.Kernels.KeccakGkr.Support

namespace LeanVmXmss.Native.Kernels.KeccakGkr

set_option compiler.ignoreBorrowAnnotation true

@[inline]
def rhoOffset (lane : USize) : USize :=
  let r0 : UInt64 := 0x1c3e0100
  let r1 : UInt64 := 0x062c241b
  let r2 : UInt64 := 0x0a031437
  let r3 : UInt64 := 0x2927192b
  let r4 : UInt64 := 0x08150f2d
  let r5 : UInt64 := 0x383d0212
  let idx := lane.toUInt64
  if idx < 4 then
    ((r0 >>> ((idx &&& 3) <<< 3)) &&& 0xff).toUSize
  else if idx < 8 then
    ((r1 >>> (((idx - 4) &&& 3) <<< 3)) &&& 0xff).toUSize
  else if idx < 12 then
    ((r2 >>> (((idx - 8) &&& 3) <<< 3)) &&& 0xff).toUSize
  else if idx < 16 then
    ((r3 >>> (((idx - 12) &&& 3) <<< 3)) &&& 0xff).toUSize
  else if idx < 20 then
    ((r4 >>> (((idx - 16) &&& 3) <<< 3)) &&& 0xff).toUSize
  else if idx < 24 then
    ((r5 >>> (((idx - 20) &&& 3) <<< 3)) &&& 0xff).toUSize
  else 14

@[inline]
def iotaMaskWord (rc : UInt64) (pos : USize) : UInt64 :=
  if pos < 64 then
    let bit := (rc >>> pos.toUInt64) &&& 1
    (0 : UInt64) - bit
  else 0

@[inline]
def readPlaneWordIota (inp : ByteArray) (n pos w : USize) (rc : UInt64) : UInt64 :=
  readWordAt inp (n * pos + w) ^^^ iotaMaskWord rc pos

@[inline]
def columnParityWord (inp : ByteArray) (n x z w : USize) (rc : UInt64) : UInt64 :=
  let p0 := 64 * x + z
  let p1 := 64 * (x + 5) + z
  let p2 := 64 * (x + 10) + z
  let p3 := 64 * (x + 15) + z
  let p4 := 64 * (x + 20) + z
  readPlaneWordIota inp n p0 w rc ^^^
  readPlaneWordIota inp n p1 w rc ^^^
  readPlaneWordIota inp n p2 w rc ^^^
  readPlaneWordIota inp n p3 w rc ^^^
  readPlaneWordIota inp n p4 w rc

def columnWordsAt (inp : ByteArray) (n x z : USize) (rc : UInt64) (acc : ByteArray) : ByteArray :=
  Nat.rec (motive := fun _ => ByteArray) acc
    (fun w prev =>
      let cw := columnParityWord inp n x z (USize.ofNat w) rc
      pushU64LE prev cw)
    n.toNat

def buildColumnParities (inp : ByteArray) (n : USize) (rc : UInt64) : ByteArray :=
  let cap := 320 * n.toNat * 8
  Nat.rec (motive := fun _ => ByteArray) (ByteArray.emptyWithCapacity cap)
    (fun col prev =>
      let ucol := USize.ofNat col
      columnWordsAt inp n (ucol / 64) (ucol % 64) rc prev)
    320

def linearPositionWords (inp cols : ByteArray) (n outPos : USize) (rc : UInt64) (acc : ByteArray) : ByteArray :=
  let outLane := outPos / 64
  let outZ := outPos % 64
  let srcLane := (outLane % 5 + 3 * (outLane / 5)) % 5 + 5 * (outLane % 5)
  let rot := rhoOffset srcLane
  let srcZ := (outZ + 64 - rot) % 64
  let srcPos := 64 * srcLane + srcZ
  let xm := (srcLane % 5 + 4) % 5
  let xp := (srcLane % 5 + 1) % 5
  let baseA := n * (64 * xm + srcZ)
  let baseB := n * (64 * xp + ((srcZ + 63) % 64))
  Nat.rec (motive := fun _ => ByteArray) acc
    (fun w prev =>
      let uw := USize.ofNat w
      let aw := readPlaneWordIota inp n srcPos uw rc
      let c1 := readWordAt cols (baseA + uw)
      let c2 := readWordAt cols (baseB + uw)
      pushU64LE prev (aw ^^^ c1 ^^^ c2))
    n.toNat

@[noinline, export lean_xmss_keccak_theta_rho_pi_iota_planes]
def keccakThetaRhoPiIotaPlanes (inp : ByteArray) (n : USize) (rc : UInt64) : ByteArray :=
  let cols := buildColumnParities inp n rc
  let cap := 1600 * n.toNat * 8
  Nat.rec (motive := fun _ => ByteArray) (ByteArray.emptyWithCapacity cap)
    (fun outPos prev => linearPositionWords inp cols n (USize.ofNat outPos) rc prev)
    1600

end LeanVmXmss.Native.Kernels.KeccakGkr
