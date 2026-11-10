import Tests.Keccak.Native
import Model.Keccak.Registers
import Spec.Transcript.Basic

namespace LeanVmXmss.Tests.Keccak.NativeRefinement

theorem lane00_refines : Native.lane00 = Model.Keccak.lane00 := rfl
theorem lane01_refines : Native.lane01 = Model.Keccak.lane01 := rfl
theorem lane02_refines : Native.lane02 = Model.Keccak.lane02 := rfl
theorem lane03_refines : Native.lane03 = Model.Keccak.lane03 := rfl
theorem lane04_refines : Native.lane04 = Model.Keccak.lane04 := rfl
theorem lane05_refines : Native.lane05 = Model.Keccak.lane05 := rfl
theorem lane06_refines : Native.lane06 = Model.Keccak.lane06 := rfl
theorem lane07_refines : Native.lane07 = Model.Keccak.lane07 := rfl
theorem lane08_refines : Native.lane08 = Model.Keccak.lane08 := rfl
theorem lane09_refines : Native.lane09 = Model.Keccak.lane09 := rfl
theorem lane10_refines : Native.lane10 = Model.Keccak.lane10 := rfl
theorem lane11_refines : Native.lane11 = Model.Keccak.lane11 := rfl
theorem lane12_refines : Native.lane12 = Model.Keccak.lane12 := rfl
theorem lane13_refines : Native.lane13 = Model.Keccak.lane13 := rfl
theorem lane14_refines : Native.lane14 = Model.Keccak.lane14 := rfl
theorem lane15_refines : Native.lane15 = Model.Keccak.lane15 := rfl
theorem lane16_refines : Native.lane16 = Model.Keccak.lane16 := rfl
theorem lane17_refines : Native.lane17 = Model.Keccak.lane17 := rfl
theorem lane18_refines : Native.lane18 = Model.Keccak.lane18 := rfl
theorem lane19_refines : Native.lane19 = Model.Keccak.lane19 := rfl
theorem lane20_refines : Native.lane20 = Model.Keccak.lane20 := rfl
theorem lane21_refines : Native.lane21 = Model.Keccak.lane21 := rfl
theorem lane22_refines : Native.lane22 = Model.Keccak.lane22 := rfl
theorem lane23_refines : Native.lane23 = Model.Keccak.lane23 := rfl
theorem lane24_refines : Native.lane24 = Model.Keccak.lane24 := rfl

theorem duplexRateWord_refines (pending slot lane : Nat) (v0 v1 v2 tag : UInt64)
    (hp : pending < 2 ^ 64) (hs : slot < 2 ^ 64) (hl : lane < 8) :
    Native.duplexRateWord pending.toUInt64 slot.toUInt64 lane.toUInt64 v0 v1 v2 tag =
      if slot < pending then
        if lane = 0 then v0 else if lane = 1 then v1
        else if lane = 2 then v2 else tag else 0 := by
  unfold Native.duplexRateWord
  have hlt : (slot.toUInt64 < pending.toUInt64) ↔ (slot < pending) := by
    change slot.toUInt64.toNat < pending.toUInt64.toNat ↔ slot < pending
    simp only [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hs]
  cases hc : decide (slot < pending) with
  | false =>
    have hnot : ¬ slot < pending := of_decide_eq_false hc
    have hnotU : ¬ slot.toUInt64 < pending.toUInt64 := fun h => hnot (hlt.mp h)
    rw [ite_eq_right hnotU, ite_eq_right hnot]
  | true =>
    have hyes : slot < pending := of_decide_eq_true hc
    have hyesU : slot.toUInt64 < pending.toUInt64 := hlt.mpr hyes
    rw [ite_eq_left hyesU, ite_eq_left hyes]
    match lane, hl with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl
    | n + 8, h => exact absurd h (Nat.not_lt_of_ge (Nat.le_add_left 8 n))

theorem powMask_refines (bits : Nat) (bound : bits < 2 ^ 64) :
    Native.powMask bits.toUInt64 = Spec.Transcript.mask bits := by
  unfold Native.powMask Spec.Transcript.mask
  have hlt : (bits.toUInt64 < 64) ↔ (bits < 64) := by
    change bits.toUInt64.toNat < 64 ↔ bits < 64
    simp only [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt bound]
  cases hc : decide (bits < 64) with
  | false =>
    have hnot : ¬ bits < 64 := of_decide_eq_false hc
    have hnotU : ¬ bits.toUInt64 < 64 := fun h => hnot (hlt.mp h)
    rw [ite_eq_right hnotU, ite_eq_right hnot]
  | true =>
    have hyes : bits < 64 := of_decide_eq_true hc
    have hyesU : bits.toUInt64 < 64 := hlt.mpr hyes
    rw [ite_eq_left hyesU, ite_eq_left hyes]

theorem powOk_refines (c0 : UInt64) (bits : Nat) (bound : bits < 2 ^ 64) :
    Native.powOk c0 bits.toUInt64 =
      if (c0 &&& Spec.Transcript.mask bits) = 0 then 1 else 0 := by
  unfold Native.powOk
  rw [powMask_refines bits bound]

theorem roundConstant_refines (r : Nat) (bound : r < 32) :
    Native.roundConstant r.toUInt64 = Model.Keccak.roundConstant r := by
  match r, bound with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _
  | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _
  | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _
  | 24, _ | 25, _ | 26, _ | 27, _ | 28, _ | 29, _ | 30, _ | 31, _ => rfl
  | n + 32, h => exact absurd h (Nat.not_lt_of_ge (Nat.le_add_left 32 n))


end LeanVmXmss.Tests.Keccak.NativeRefinement
