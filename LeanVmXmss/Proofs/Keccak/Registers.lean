import Model.Keccak.Registers

namespace LeanVmXmss.Proofs.Keccak

set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

theorem range_five : Array.range 5 = #[0, 1, 2, 3, 4] := by decide

theorem range_twenty_five : Array.range 25 =
    #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] := by decide

theorem registers_round_refines_spec (s : Model.Keccak.State25) (r : UInt64) :
    (Model.Keccak.round25 s r).toSpec = Spec.Keccak.round s.toSpec r := by
  apply Array.ext
  · simp [Model.Keccak.round25, Model.Keccak.State25.toSpec, Spec.Keccak.round,
      Spec.Keccak.iota, Spec.Keccak.chi, Spec.Keccak.rhoPi, Spec.Keccak.theta,
      -Array.getElem_range, range_five, range_twenty_five]
  · intro i h₁ h₂
    have hi : i < 25 := by simpa [Model.Keccak.round25, Model.Keccak.State25.toSpec] using h₁
    have cases_i : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
        i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨
        i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 := by omega
    rcases cases_i with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst i <;>
      simp [Model.Keccak.round25, Model.Keccak.State25.toSpec, Spec.Keccak.round,
        Spec.Keccak.iota, Spec.Keccak.chi, Spec.Keccak.rhoPi, Spec.Keccak.theta,
        Spec.Keccak.rho, -Array.getElem_range, range_five, range_twenty_five]

theorem round_constant_refines (i : Nat) (h : i < 24) :
    Model.Keccak.roundConstant i = Spec.Keccak.rc[i]! := by
  have cases_i : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
      i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨
      i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 := by omega
  rcases cases_i with h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h <;> subst i <;> decide +revert

theorem registers_rounds_refines (n i : Nat) (s : Model.Keccak.State25) (h : i + n ≤ 24) :
    (Model.Keccak.rounds25 n i s).toSpec = Spec.Keccak.rounds n i s.toSpec := by
  induction n generalizing i s with
  | zero => rfl
  | succ n ih =>
    change (Model.Keccak.rounds25 n (i + 1) (Model.Keccak.round25 s (Model.Keccak.roundConstant i))).toSpec =
      Spec.Keccak.rounds n (i + 1) (Spec.Keccak.round s.toSpec Spec.Keccak.rc[i]!)
    rw [ih (i + 1) _ (by omega), registers_round_refines_spec,
      round_constant_refines i (by omega)]

theorem registers_permutation_refines_spec (s : Model.Keccak.State25) :
    (Model.Keccak.keccakF1600 s).toSpec = Spec.Keccak.keccakF1600 s.toSpec := by
  exact registers_rounds_refines 24 0 s (by omega)

theorem spec_rounds_eq_permute (s : Spec.Keccak.State) :
    Spec.Keccak.keccakF1600 s = Spec.Keccak.permute s := by
  rfl

end LeanVmXmss.Proofs.Keccak
