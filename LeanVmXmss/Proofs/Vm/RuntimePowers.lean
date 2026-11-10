import Proofs.Vm.GPow
import Model.Vm.Interpreter
import Spec.Vm.Hints
import Model.Vm.PowerTable
import Proofs.Vm.Basic
import Model.Vm.Scheduled

namespace LeanVmXmss.Proofs.Vm

open Spec.Vm

set_option maxRecDepth 4096

theorem lookup_power_refinement (g : GPow) (i : Nat) :
    Model.Vm.lookupPower g.powers i = g.power i := by
  by_cases hi : i < g.powers.size
  · simp [Model.Vm.lookupPower, GPow.power, hi]
  · have bound : g.powers.size ≤ i := by omega
    simp [Model.Vm.lookupPower, GPow.power, hi]

theorem model_grown_lookup_count (g : GPow) (n i : Nat)
    (valid : PowersValid g) (covered : i ≤ n) :
    Model.Vm.lookupPower (g.grow n).powers i = .ok (Spec.Xmss.count i) := by
  rw [lookup_power_refinement]
  exact grow_covers g n i valid covered

theorem initial_with_powers_valid (frame : Nat) (inputs : Array Spec.Field.E)
    (g : GPow) (valid : PowersValid g) (s : State)
    (success : Model.Vm.initialWithPowers frame inputs g = .ok s) : PowersValid s.g := by
  cases hm : Model.Vm.initialMemory frame inputs with
  | error fault =>
    simp [Model.Vm.initialWithPowers, hm, bind, Except.bind] at success
  | ok memory =>
    simp [Model.Vm.initialWithPowers, hm, bind, Except.bind, pure, Except.pure] at success
    subst s
    exact valid

theorem initial_powers_valid (frame : Nat) (inputs : Array Spec.Field.E)
    (programSize : Nat) (s : State)
    (success : Model.Vm.initial frame inputs programSize = .ok s) : PowersValid s.g := by
  exact initial_with_powers_valid frame inputs _
    (grow_valid _ _ default_powers_valid) s success

theorem set_step_powers_valid (offset : Nat) (value : Spec.Field.E) (s t : State)
    (valid : PowersValid s.g) (success : Model.Vm.setStep offset value s = .ok t) :
    PowersValid t.g := by
  cases s with
  | mk memory pc fp nextFree g cycles counts =>
    cases hp : memory.put (fp+offset) value with
    | error fault => simp [Model.Vm.setStep, hp, bind, Except.bind] at success
    | ok next =>
      cases hb : next.bump (fp+offset) with
      | error fault => simp [Model.Vm.setStep, hp, hb, bind, Except.bind] at success
      | ok final =>
        simp [Model.Vm.setStep, hp, hb, bind, Except.bind, pure, Except.pure] at success
        subst t
        exact grow_valid g _ valid

theorem step_with_powers_valid (op : Op) (s t : State) (g : GPow)
    (valid : PowersValid g) (success : stepWithPowers op s g = .ok t) :
    PowersValid t.g := by
  cases hb : stepBody op s g with
  | error fault => simp [stepWithPowers, hb, bind, Except.bind] at success
  | ok result =>
    rcases result with ⟨memory, pc, fp, counts⟩
    simp [stepWithPowers, hb, bind, Except.bind, pure, Except.pure] at success
    subst t
    exact valid

theorem spec_step_powers_valid (op : Op) (s t : State)
    (valid : PowersValid s.g) (success : Spec.Vm.step op s = .ok t) :
    PowersValid t.g := by
  exact step_with_powers_valid op s t _ (grow_valid _ _ valid) success

theorem model_step_powers_valid (op : Op) (s t : State)
    (valid : PowersValid s.g) (success : Model.Vm.step op s = .ok t) :
    PowersValid t.g := by
  rw [step_refines_spec] at success
  exact spec_step_powers_valid op s t valid success

theorem run_powers_valid (fuel : Nat) (program : Array Op) (s t : State)
    (valid : PowersValid s.g) (success : Model.Vm.run fuel program s = .ok t) :
    PowersValid t.g := by
  induction fuel generalizing s with
  | zero => simp [Model.Vm.run] at success
  | succ fuel ih =>
    simp only [Model.Vm.run] at success
    split at success
    · cases success
      exact valid
    · cases hp : program[s.pc]? with
      | none => simp [hp] at success
      | some op =>
        cases hs : Model.Vm.step op s with
        | error fault => simp [hp, hs] at success
        | ok next =>
          simp only [hp, hs] at success
          exact ih next (model_step_powers_valid op s next valid hs) success

theorem reserve_powers_valid (s t : State) (ptr size : Nat)
    (valid : PowersValid s.g) (success : reserve s ptr size = .ok t) :
    PowersValid t.g := by
  simp only [reserve, bind, Except.bind, pure, Except.pure,
    throw] at success
  split at success
  · simp at success
    subst t
    exact valid
  · split at success
    · simp at success
    · cases hm : s.memory.ensure (s.nextFree+size) with
      | error fault => simp [hm] at success
      | ok m =>
        have hp := allocation_power_coverage s.g s.nextFree size valid
        cases hw : m.put (s.fp+ptr) (Spec.Xmss.count s.nextFree) with
        | error fault => simp [hm, hp, hw] at success
        | ok memory =>
          simp [hm, hp, hw] at success
          subst t
          exact grow_valid _ _ valid

theorem put_values_powers_valid (s t : State) (base : Nat) (values : Array Spec.Field.E)
    (valid : PowersValid s.g) (success : putValues s base values = .ok t) :
    PowersValid t.g := by
  simp only [putValues, bind, Except.bind, pure, Except.pure] at success
  split at success
  · cases success
  · simp only [Except.ok.injEq] at success
    subst t
    exact valid

theorem pop_witness_powers_valid (r t : Runtime) (name : String) (base len : Nat)
    (valid : PowersValid r.state.g) (success : popWitness r name base len = .ok t) :
    PowersValid t.state.g := by
  simp only [popWitness, bind, Except.bind, pure, Except.pure,
    throw] at success
  repeat first
    | split at success
    | contradiction
  all_goals
    try simp_all
  all_goals
    subst t
    apply put_values_powers_valid r.state _ base _ valid
    assumption

theorem apply_hint_powers_valid (hint : RHint) (r t : Runtime)
    (valid : PowersValid r.state.g) (success : applyHint hint r = .ok t) :
    PowersValid t.state.g := by
  cases hint <;>
    simp only [applyHint, bind, Except.bind, pure, Except.pure, throw] at success
  all_goals
    repeat first
      | split at success
      | contradiction
      | simp only [bind, Except.bind, pure, Except.pure, throw] at success
  all_goals
    try simp only [bind, Except.bind, pure, Except.pure, throw] at success
    repeat first
      | split at success
      | contradiction
  all_goals
    try simp only [Except.ok.injEq] at success
    first
    | exact pop_witness_powers_valid r t _ _ _ valid success
    | subst t
      first
      | exact valid
      | exact grow_valid _ _ valid
      | apply reserve_powers_valid r.state _ _ _ valid
        assumption
      | apply put_values_powers_valid r.state _ _ _ valid
        assumption

theorem fold_hints_powers_valid (hints : List RHint) (r t : Runtime)
    (valid : PowersValid r.state.g)
    (success : hints.foldlM (fun r hint => applyHint hint r) r = .ok t) :
    PowersValid t.state.g := by
  induction hints generalizing r with
  | nil => cases success; exact valid
  | cons hint rest ih =>
    simp only [List.foldlM_cons, bind, Except.bind] at success
    cases hs : applyHint hint r with
    | error fault => simp [hs] at success
    | ok next =>
      simp only [hs] at success
      exact ih next (apply_hint_powers_valid hint r next valid hs) success

theorem apply_hints_powers_valid (hints : Array RHint) (r t : Runtime)
    (valid : PowersValid r.state.g) (success : applyHints hints r = .ok t) :
    PowersValid t.state.g := by
  apply fold_hints_powers_valid hints.toList r t valid
  simpa only [Array.foldlM_toList, applyHints] using success

theorem scheduled_run_powers_valid (fuel : Nat) (program : Array Op)
    (hints : Array (Array RHint)) (r t : Runtime)
    (valid : PowersValid r.state.g)
    (success : Model.Vm.scheduledRun fuel program hints r = .ok t) :
    PowersValid t.state.g := by
  induction fuel generalizing r with
  | zero => simp [Model.Vm.scheduledRun] at success
  | succ fuel ih =>
    simp only [Model.Vm.scheduledRun] at success
    split at success
    · cases success; exact valid
    · cases hp : program[r.state.pc]? with
      | none => simp [hp] at success
      | some op =>
        cases hh : applyHints (hints[r.state.pc]?.getD #[]) r with
        | error fault => simp [hp, hh] at success
        | ok ready =>
          rcases ready with ⟨state, streams⟩
          cases hs : Model.Vm.step op state with
          | error fault => simp [hp, hh, hs] at success
          | ok next =>
            simp only [hp, hh, hs] at success
            exact ih ⟨next, streams⟩
              (model_step_powers_valid op state next
                (apply_hints_powers_valid _ r ⟨state, streams⟩ valid hh) hs) success

end LeanVmXmss.Proofs.Vm
