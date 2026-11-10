import Model.Vm.Interpreter
import Spec.Vm.Bytecode
import Spec.Vm.Hints

namespace LeanVmXmss.Proofs.Vm

open Spec.Vm

theorem step_refines_spec (op : Op) (s : State) :
    Model.Vm.step op s = Spec.Vm.step op s := by
  cases op with
  | set offset value =>
    cases s with
    | mk memory pc fp nextFree g cycles counts =>
      cases hp : memory.put (fp+offset) value with
      | error fault =>
        simp [Model.Vm.step, Model.Vm.setStep, Spec.Vm.step, Spec.Vm.stepWithPowers, Spec.Vm.stepBody, opcode,
          hp, bind, Except.bind, pure, Except.pure]
      | ok next =>
        cases hb : next.bump (fp+offset) <;>
          simp [Model.Vm.step, Model.Vm.setStep, Spec.Vm.step, Spec.Vm.stepWithPowers, Spec.Vm.stepBody, opcode,
            hp, hb, bind, Except.bind, pure, Except.pure]
  | xor a b c => rfl
  | mul a b c => rfl
  | deref a b c mode => rfl
  | jump a b c => rfl
  | keccak message tail b8 cap output inOdd outOdd => rfl

theorem store_conflict (m : Memory) (address : Nat) (value : Spec.Field.E)
    (hbound : address < maxCells) (hsize : address < m.cells.size)
    (hwritten : (m.get address).written = true) (hne : (m.get address).word ≠ value) :
    m.store address value = .error (.conflict address (m.get address).word value) := by
  have hw : m.cells[address].written = true := by simpa [Memory.get, hsize] using hwritten
  have hn : m.cells[address].word ≠ value := by simpa [Memory.get, hsize] using hne
  simp [Memory.store, Memory.ensure, Nat.not_le.mpr hbound, Memory.get, hsize, hw, hn]

theorem xor_kernel_refines_eadd (a b : Spec.Field.E) :
    (⟨Model.Vm.xorKernel a.c0 b.c0, Model.Vm.xorKernel a.c1 b.c1,
      Model.Vm.xorKernel a.c2 b.c2⟩ : Spec.Field.E) = Spec.Field.eadd a b := by
  cases a
  cases b
  simp [Model.Vm.xorKernel, Spec.Field.eadd, Spec.Field.add]

theorem store_out_of_memory (m : Memory) (address : Nat) (value : Spec.Field.E)
    (h : maxCells ≤ address) : m.store address value = .error .outOfMemory := by
  simp [Memory.store, Memory.ensure, h]

theorem even_first_lane : KeccakInternal.cellLanes false 0 = (some 0, some 1) := by decide

theorem odd_first_lane : KeccakInternal.cellLanes true 0 = (none, some 0) := by decide

theorem layout_parity_distinct : KeccakInternal.cellLanes false 0 ≠ KeccakInternal.cellLanes true 0 := by decide

theorem ensure_used_mono (m : Memory) (address : Nat) (next : Memory)
    (success : m.ensure address = .ok next) : m.used ≤ next.used := by
  simp only [Memory.ensure] at success
  split at success
  · simp at success
  · split at success
    · cases success
      exact Nat.le_max_left _ _
    · cases success
      exact Nat.le_max_left _ _

theorem store_used_mono (m : Memory) (address : Nat) (value : Spec.Field.E) (next : Memory)
    (success : m.store address value = .ok next) : m.used ≤ next.used := by
  simp only [Memory.store, bind, Except.bind] at success
  cases hm : m.ensure address with
  | error fault => simp [hm] at success
  | ok ensured =>
    have hused := ensure_used_mono m address ensured hm
    simp only [hm, pure, Except.pure] at success
    split at success
    · simp at success
    · cases success
      exact hused

theorem forIn_except_mono {α β : Type} {inv : β → β → Prop}
    (refl_inv : ∀ x, inv x x)
    (trans_inv : ∀ x y z, inv x y → inv y z → inv x z)
    (xs : List α) (init : β) (f : α → β → Except Fault (ForInStep β))
    (step_inv : ∀ a b c, (f a b = .ok (.yield c) ∨ f a b = .ok (.done c)) → inv b c)
    (out : β) (success : forIn xs init f = .ok out) : inv init out := by
  induction xs generalizing init with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure] at success
    cases success
    exact refl_inv _
  | cons a rest ih =>
    simp only [List.forIn_cons, bind, Except.bind, pure, Except.pure] at success
    cases hf : f a init with
    | error fault => simp [hf] at success
    | ok step =>
      cases step with
      | done final =>
        simp only [hf] at success
        injection success with hfinal
        subst hfinal
        exact step_inv a init final (Or.inr hf)
      | yield next =>
        simp only [hf] at success
        exact trans_inv _ _ _ (step_inv a init next (Or.inl hf)) (ih next success)

theorem wf_nat_fix_eq {α : Sort u} {motive : α → Sort v} (h : α → Nat)
    (F : (x : α) → ((y : α) → InvImage (fun x1 x2 => x1 < x2) h y x → motive y) → motive x)
    (x : α) :
    WellFounded.Nat.fix h F x = F x (fun y _ => WellFounded.Nat.fix h F y) := by
  have hgo : ∀ (f1 f2 : Nat) (y : α) (h1 : h y < f1) (h2 : h y < f2),
      WellFounded.Nat.fix.go h F f1 y h1 = WellFounded.Nat.fix.go h F f2 y h2 := by
    intro f1
    induction f1 with
    | zero =>
      intro _ y h1 _
      exact False.elim (Nat.not_lt_zero _ h1)
    | succ f1 ih =>
      intro f2 y h1 h2
      cases f2 with
      | zero => exact False.elim (Nat.not_lt_zero _ h2)
      | succ f2 =>
        unfold WellFounded.Nat.fix.go
        exact congrArg (F y) (funext fun z => funext fun hz => ih f2 z _ _)
  have h1 : WellFounded.Nat.fix h F x =
      WellFounded.Nat.fix.go h F (h x + 1) x (Nat.lt_succ_self (h x)) := by
    unfold WellFounded.Nat.fix
    exact hgo _ _ x _ _
  rw [h1]
  unfold WellFounded.Nat.fix.go
  dsimp only
  exact congrArg (F x) (funext fun y => funext fun hy => hgo _ _ y _ _)

def rangeLoop {β : Type} (r : Std.Legacy.Range)
    (f : (i : Nat) → i ∈ r → β → Except Fault (ForInStep β))
    (b : β) (i : Nat) (hs : (i - r.start) % r.step = 0) (hl : r.start ≤ i) :
    Except Fault β :=
  @WellFounded.Nat.fix
    ((_ : β) ×' (j : Nat) ×' (_ : (j - r.start) % r.step = 0) ×' (r.start ≤ j))
    (fun _ => Except Fault β)
    (fun x => PSigma.casesOn x fun _ j => PSigma.casesOn j fun j hs => PSigma.casesOn hs fun _ _ => r.stop - j)
    (fun _x rec =>
      match _x with
      | ⟨b, ⟨j, ⟨hs, hl⟩⟩⟩ =>
        if hlt : j < r.stop then do
          match ← f j ⟨hl, hlt, hs⟩ b with
          | .done b' => pure b'
          | .yield b' =>
            have hpos := r.step_pos
            have hs' : (j + r.step - r.start) % r.step = 0 := by
              have hsub : j + r.step - r.start = (j - r.start) + r.step := by omega
              rw [hsub, Nat.add_mod_right]
              exact hs
            have hl' : r.start ≤ j + r.step := Nat.le_trans hl (Nat.le_add_right _ _)
            rec ⟨b', ⟨j + r.step, ⟨hs', hl'⟩⟩⟩ (by
              change r.stop - (j + r.step) < r.stop - j
              omega)
        else pure b)
    ⟨b, ⟨i, ⟨hs, hl⟩⟩⟩

theorem forIn'_eq_rangeLoop {β : Type} (r : Std.Legacy.Range) (init : β)
    (f : (i : Nat) → i ∈ r → β → Except Fault (ForInStep β)) :
    Std.Legacy.Range.forIn' r init f =
      rangeLoop r f init r.start (by simp) (Nat.le_refl _) := by
  with_unfolding_all rfl

theorem rangeLoop_eq_range' {β : Type} (n : Nat) (f : Nat → β → Except Fault (ForInStep β)) :
    ∀ (k i : Nat) (b : β) (hs : (i - ([:n] : Std.Legacy.Range).start) % ([:n] : Std.Legacy.Range).step = 0)
      (hl : ([:n] : Std.Legacy.Range).start ≤ i) (_hk : n ≤ i + k),
      rangeLoop [:n] (fun j _ x => f j x) b i hs hl = forIn (List.range' i (n - i) 1) b f := by
  intro k
  induction k with
  | zero =>
    intro i b _ _ _hk
    have hge : ¬ i < n := by omega
    have hsub : n - i = 0 := by omega
    unfold rangeLoop
    rw [wf_nat_fix_eq]
    dsimp only
    simp [hge, hsub, pure, Except.pure]
  | succ k ih =>
    intro i b _ _ _hk
    by_cases hlt : i < n
    · have hsub : n - i = (n - (i + 1)) + 1 := by omega
      unfold rangeLoop
      rw [wf_nat_fix_eq]
      dsimp only
      rw [dite_cond_eq_true (eq_true hlt), hsub, List.range'_succ, List.forIn_cons]
      cases hf : f i b with
      | error e => rfl
      | ok step =>
        cases step with
        | done b' => rfl
        | yield b' =>
          dsimp only [bind, Except.bind]
          exact ih (i + 1) b' _ _ (by omega)
    · have hsub : n - i = 0 := by omega
      unfold rangeLoop
      rw [wf_nat_fix_eq]
      dsimp only
      simp [hlt, hsub, pure, Except.pure]

theorem range_forIn_eq_range' {β : Type} (n : Nat) (init : β)
    (f : Nat → β → Except Fault (ForInStep β)) :
    forIn [:n] init f = forIn (List.range' 0 n 1) init f := by
  change Std.Legacy.Range.forIn' [:n] init (fun j _ x => f j x) = forIn (List.range' 0 n 1) init f
  rw [forIn'_eq_rangeLoop]
  simpa only [Nat.sub_zero] using
    rangeLoop_eq_range' n f n 0 init (by simp) (Nat.le_refl _) (Nat.le_add_left n 0)

theorem spread_used_mono (fuel : Nat) (todo : List Nat) (m next : Memory) (value : Spec.Field.E)
    (success : spread fuel todo m value = .ok next) : m.used ≤ next.used := by
  unfold spread at success
  dsimp only at success
  rw [range_forIn_eq_range'] at success
  simp only [bind, Except.bind, pure, Except.pure, throw] at success
  split at success
  · contradiction
  · rename_i outer hs
    have houter := forIn_except_mono
      (inv := fun s1 s2 : Option Memory × Memory × List Nat =>
        s1.2.1.used ≤ s2.2.1.used ∧
        ∀ r, s2.1 = some r → (∃ r0, s1.1 = some r0 ∧ r0.used ≤ r.used) ∨ s1.2.1.used ≤ r.used)
      (fun x => ⟨Nat.le_refl _, fun r hr => Or.inl ⟨r, hr, Nat.le_refl _⟩⟩)
      (fun x y z hxy hyz => ⟨Nat.le_trans hxy.1 hyz.1, fun r hr => by
        cases hyz.2 r hr with
        | inl h0 =>
          rcases h0 with ⟨r1, hy1, hr1⟩
          cases hxy.2 r1 hy1 with
          | inl h00 =>
            rcases h00 with ⟨r0, hx0, hr0⟩
            exact Or.inl ⟨r0, hx0, Nat.le_trans hr0 hr1⟩
          | inr hx => exact Or.inr (Nat.le_trans hx hr1)
        | inr hy => exact Or.inr (Nat.le_trans hxy.1 hy)⟩)
      _ (none, m, todo) _
      (fun _ acc c hc => by
        rcases acc with ⟨rOpt, cur, pend⟩
        cases pend with
        | nil =>
          cases hc with
          | inl h => simp [pure, Except.pure] at h
          | inr h =>
            simp only [pure, Except.pure, Except.ok.injEq, ForInStep.done.injEq] at h
            subst c
            exact ⟨Nat.le_refl _, fun r hr => by
              simp only [Option.some.injEq] at hr
              subst r
              exact Or.inr (Nat.le_refl _)⟩
        | cons a rest =>
          have step_body : ∀ stepOut : Memory × List Nat,
              forIn (List.filterMap (fun (x, y) => if (x == a) = true then some y else none) cur.links.toList)
                ({cur with links := cur.links.filter fun (x, _) => x != a}, rest)
                (fun b inner =>
                  let jp := fun (_ : Unit) pending => do
                    let stored ← inner.1.store b value
                    pure (ForInStep.yield (stored, pending))
                  if (!(inner.1.get b).written) = true then jp () (b :: inner.2) else jp () inner.2) = .ok stepOut →
              cur.used ≤ stepOut.1.used := by
            intro stepOut hinner
            exact forIn_except_mono
              (inv := fun p1 p2 : Memory × List Nat => p1.1.used ≤ p2.1.used)
              (fun _ => Nat.le_refl _)
              (fun _ _ _ => Nat.le_trans)
              _ _ _
              (fun b p1 p2 hp => by
                cases hp with
                | inr hd =>
                  split at hd <;> simp only [bind, Except.bind, pure, Except.pure] at hd
                  all_goals
                    cases hst : p1.1.store b value with
                    | error _ => simp [hst] at hd
                    | ok st => simp [hst] at hd
                | inl hy =>
                  split at hy <;> simp only [bind, Except.bind, pure, Except.pure] at hy
                  all_goals
                    cases hst : p1.1.store b value with
                    | error _ => simp [hst] at hy
                    | ok st =>
                      have hmono := store_used_mono p1.1 b value st hst
                      simp only [hst, Except.ok.injEq, ForInStep.yield.injEq] at hy
                      subst p2
                      exact hmono)
              stepOut hinner
          cases hc with
          | inr hd =>
            simp only [bind, Except.bind, pure, Except.pure] at hd
            split at hd
            · contradiction
            · simp at hd
          | inl hy =>
            simp only [bind, Except.bind, pure, Except.pure] at hy
            split at hy
            · contradiction
            · rename_i stepOut hinner
              have hmono := step_body stepOut hinner
              simp only [Except.ok.injEq, ForInStep.yield.injEq] at hy
              subst c
              exact ⟨hmono, fun r hr => by simp at hr⟩)
      outer hs
    cases hopt : outer.1 with
    | some r =>
      simp only [hopt, Except.ok.injEq] at success
      subst next
      cases houter.2 _ hopt with
      | inl h0 => rcases h0 with ⟨_, hnone, _⟩; simp at hnone
      | inr hm => exact hm
    | none =>
      simp only [hopt] at success
      split at success
      · simp only [Except.ok.injEq] at success
        subst next
        exact houter.1
      · simp at success

theorem put_used_mono (m : Memory) (address : Nat) (value : Spec.Field.E) (next : Memory)
    (success : m.put address value = .ok next) : m.used ≤ next.used := by
  simp only [Memory.put, bind, Except.bind] at success
  cases hm : m.store address value with
  | error fault => simp [hm] at success
  | ok stored =>
    have hused := store_used_mono m address value stored hm
    simp only [hm] at success
    exact Nat.le_trans hused (spread_used_mono _ _ _ _ _ success)

theorem read_used_mono (m : Memory) (address : Nat) (value : Spec.Field.E) (next : Memory)
    (success : m.read address = .ok (value, next)) : m.used ≤ next.used := by
  simp only [Memory.read, bind, Except.bind, pure, Except.pure] at success
  cases hm : m.ensure address with
  | error fault => simp [hm] at success
  | ok ensured =>
    have hused := ensure_used_mono m address ensured hm
    simp only [hm, pure, Except.pure] at success
    split at success
    · cases success
      exact hused
    · cases success
      exact hused

theorem bump_used_mono (m : Memory) (address : Nat) (next : Memory)
    (success : m.bump address = .ok next) : m.used ≤ next.used := by
  simp only [Memory.bump, bind, Except.bind, pure, Except.pure] at success
  cases hm : m.ensure address with
  | error fault => simp [hm] at success
  | ok ensured =>
    have hused := ensure_used_mono m address ensured hm
    simp only [hm] at success
    cases success
    exact hused

theorem link_used_mono (m : Memory) (a b : Nat) (next : Memory)
    (success : m.link a b = .ok next) : m.used ≤ next.used := by
  simp only [Memory.link, bind, Except.bind, pure, Except.pure] at success
  cases ha : m.ensure a with
  | error fault => simp [ha] at success
  | ok first =>
    have hfirst := ensure_used_mono m a first ha
    simp only [ha] at success
    cases hb : first.ensure b with
    | error fault => simp [hb] at success
    | ok second =>
      have hsecond := ensure_used_mono first b second hb
      simp only [hb] at success
      cases success
      exact Nat.le_trans hfirst hsecond

theorem put_values_used_mono (s t : State) (base : Nat) (values : Array Spec.Field.E)
    (success : putValues s base values = .ok t) : s.memory.used ≤ t.memory.used := by
  unfold putValues at success
  dsimp only at success
  rw [range_forIn_eq_range'] at success
  simp only [bind, Except.bind, pure, Except.pure] at success
  split at success
  · contradiction
  · rename_i finalMem hloop
    simp only [Except.ok.injEq] at success
    subst t
    exact forIn_except_mono
      (inv := fun m1 m2 : Memory => m1.used ≤ m2.used)
      (fun _ => Nat.le_refl _)
      (fun _ _ _ => Nat.le_trans)
      _ s.memory _
      (fun i m1 m2 hm => by
        cases hm with
        | inr hd =>
          cases hp : m1.put (base + i) (values[i]?.getD Spec.Field.zero) with
          | error _ => simp [hp, bind, Except.bind] at hd
          | ok pm => simp [hp, bind, Except.bind, pure, Except.pure] at hd
        | inl hy =>
          cases hp : m1.put (base + i) (values[i]?.getD Spec.Field.zero) with
          | error _ => simp [hp, bind, Except.bind] at hy
          | ok pm =>
            have hmono := put_used_mono m1 (base + i) _ pm hp
            simp only [hp, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
              ForInStep.yield.injEq] at hy
            subst m2
            exact hmono)
      finalMem hloop

end LeanVmXmss.Proofs.Vm
