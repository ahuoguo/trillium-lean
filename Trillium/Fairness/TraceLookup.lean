/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.Fairness.NatOmega
import Trillium.Fairness.TraceLen
import Trillium.Fairness.Inftraces
import Trillium.Fairness.TraceUtils

/-!
# Lookups in possibly infinite traces
Port of `fairness/trace_lookup.v`.

* `traceLookup tr i` (Rocq `tr !! i`, scoped notation `tr !! i`) is the `i`-th position of
  `tr`: its state together with the label and target state of the next step, if any
  (`Option (St × Option (L × St))`).
* `stateLookup tr i` (Rocq/Lean scoped notation `tr S!! i`) is the `i`-th state.
* `labelLookup tr i` (Rocq/Lean scoped notation `tr L!! i`) is the `i`-th label.

All three are characterised by the lemmas `traceLookup_eq`, `stateLookup_eq` and
`labelLookup_eq` in terms of `after i tr` (not `simp` globally; use
`attribute [local simp] traceLookup_eq stateLookup_eq labelLookup_eq` to reduce lookups to
`after`). The lookups at `0` and at successors of `cons` are `simp` lemmas.

Rocq's stdpp `Lookup` instances `state_lookup_Lookup`/`label_lookup_Lookup` are not ported (see
the `#rocq_ignore`s); Rocq's `trace_lookup` instance is the definition `traceLookup`.
Rocq's `lia_NO` tactic is replaced by `cases len` followed by `simp`/`omega`.
-/

namespace Trillium.Fairness

open Trace NatOmega

namespace Trace

variable {St L : Type _}

/-- The state of a trace together with its first step (label and target state), if any. -/
def headStep (t : Trace St L) : St × Option (L × St) :=
  (t.first, match t.dest with
    | .inl _ => none
    | .inr (_, ℓ, r) => some (ℓ, r.first))

@[simp] theorem headStep_singl (s : St) : (singl s : Trace St L).headStep = (s, none) := by
  simp [headStep]

@[simp] theorem headStep_cons (s : St) (ℓ : L) (r : Trace St L) :
    (s -[ℓ]-> r).headStep = (s, some (ℓ, r.first)) := by
  simp [headStep]

end Trace

section TraceLookup

variable {St L : Type _}

/-- The `i`-th position of a trace: the state and, if any, the label and the target of the next
step (Rocq's `Lookup` instance `trace_lookup`, notation `tr !! i`). -/
@[rocq_alias trillium.fairness.trace_lookup]
def traceLookup (tr : Trace St L) (i : Nat) : Option (St × Option (L × St)) :=
  match after i tr with
  | none => none
  | some t => some t.headStep

/-- The `i`-th state of a trace (notation `tr S!! i`). -/
@[rocq_alias trillium.fairness.state_lookup]
def stateLookup (tr : Trace St L) (i : Nat) : Option St :=
  match traceLookup tr i with
  | some (st, _) => some st
  | none => none

/-- The `i`-th label of a trace (notation `tr L!! i`). -/
@[rocq_alias trillium.fairness.label_lookup]
def labelLookup (tr : Trace St L) (i : Nat) : Option L :=
  match traceLookup tr i with
  | some (_, some (ℓ, _)) => some ℓ
  | _ => none

#rocq_ignore trillium.fairness.state_lookup_Lookup
  "stdpp `Lookup` instance; Lean's `GetElem?` has the element type as an `outParam`, so the \
  three lookups cannot all be instances on `Trace`. Use `stateLookup` / scoped notation `tr S!! i`"
#rocq_ignore trillium.fairness.label_lookup_Lookup
  "stdpp `Lookup` instance; Lean's `GetElem?` has the element type as an `outParam`, so the \
  three lookups cannot all be instances on `Trace`. Use `labelLookup` / scoped notation `tr L!! i`"

@[inherit_doc] scoped notation:70 tr:70 " !! " i:71 => traceLookup tr i
@[inherit_doc] scoped notation:70 tr:70 " S!! " i:71 => stateLookup tr i
@[inherit_doc] scoped notation:70 tr:70 " L!! " i:71 => labelLookup tr i

theorem traceLookup_eq (tr : Trace St L) (i : Nat) :
    tr !! i = (after i tr).map headStep := by
  unfold traceLookup; cases after i tr <;> rfl

theorem stateLookup_eq (tr : Trace St L) (i : Nat) :
    tr S!! i = (after i tr).map Trace.first := by
  unfold stateLookup traceLookup; cases after i tr <;> rfl

theorem labelLookup_eq (tr : Trace St L) (i : Nat) :
    tr L!! i = (after i tr).bind Trace.label? := by
  unfold labelLookup traceLookup
  cases after i tr with
  | none => rfl
  | some t => cases t <;> simp

attribute [local simp] traceLookup_eq stateLookup_eq labelLookup_eq

/-- `after (i + 1)` in terms of `after i`. -/
theorem after_succ (tr : Trace St L) (i : Nat) :
    after (i + 1) tr = (after i tr).bind (after 1) := by
  rw [after_sum' 1 i tr]; cases after i tr <;> rfl

@[simp] theorem after_one_singl (s : St) : after 1 (singl s : Trace St L) = none := rfl

@[simp] theorem after_one_cons (s : St) (ℓ : L) (r : Trace St L) :
    after 1 (s -[ℓ]-> r) = some r := by
  simp [after]

@[rocq_alias trillium.fairness.trace_lookup_trichotomy]
theorem trace_lookup_trichotomy (tr : Trace St L) (len : NatOmega) (LEN : traceLenIs tr len) :
    ∀ i, (∃ st ℓ st', tr !! i = some (st, some (ℓ, st')) ∧ ltNatL (i + 1) len) ∨
      (∃ st, tr !! i = some (st, none) ∧ len = .num (i + 1)) ∨
      (tr !! i = none ∧ NatOmega.le len (.num i)) := by
  intro i
  have Ai := LEN i
  have Ai' := LEN (i + 1)
  have Ni := trace_len_neg tr len LEN i
  have Ni' := trace_len_neg tr len LEN (i + 1)
  rw [after_succ] at Ai' Ni'
  cases h : after i tr with
  | none =>
    exact .inr (.inr ⟨by simp [h], Ni.1 h⟩)
  | some t =>
    rw [h] at Ai Ai' Ni'
    have Hlt := Ai.1 rfl
    cases t with
    | singl s =>
      have Hle := Ni'.1 rfl
      refine .inr (.inl ⟨s, by simp [h], ?_⟩)
      cases len with
      | infinity => exact Hle.elim
      | num n => simp only [ltNatL, NatOmega.le] at Hlt Hle; congr 1; omega
    | cons s ℓ r =>
      exact .inl ⟨s, ℓ, r.first, by simp [h], Ai'.1 (by simp)⟩

@[rocq_alias trillium.fairness.trace_lookup_dom]
theorem trace_lookup_dom (tr : Trace St L) (len : NatOmega) (LEN : traceLenIs tr len) :
    ∀ i, (tr !! i).isSome ↔ ltNatL i len := by
  intro i
  rw [← LEN i, traceLookup_eq, Option.isSome_map]

@[rocq_alias trillium.fairness.trace_lookup_dom_neg]
theorem trace_lookup_dom_neg (tr : Trace St L) (len : NatOmega) (LEN : traceLenIs tr len) :
    ∀ i, tr !! i = none ↔ NatOmega.le len (.num i) := by
  intro i
  rw [← trace_len_neg tr len LEN i, traceLookup_eq, Option.map_eq_none_iff]

@[rocq_alias trillium.fairness.trace_lookup_dom_strong]
theorem trace_lookup_dom_strong (tr : Trace St L) (len : NatOmega) (LEN : traceLenIs tr len) :
    ∀ i, (∃ st ℓ st', tr !! i = some (st, some (ℓ, st'))) ↔ ltNatL (i + 1) len := by
  intro i
  rcases trace_lookup_trichotomy tr len LEN i with ⟨st, ℓ, st', H, LT⟩ | ⟨st, H, rfl⟩ | ⟨H, LE⟩
  · exact ⟨fun _ => LT, fun _ => ⟨st, ℓ, st', H⟩⟩
  · rw [H]; simp [ltNatL]
  · rw [H]
    simp only [reduceCtorEq, exists_false, false_iff]
    cases len with
    | infinity => exact LE.elim
    | num n => simp only [ltNatL, NatOmega.le] at LE ⊢; omega

@[rocq_alias trillium.fairness.trace_lookup_dom_eq]
theorem trace_lookup_dom_eq (tr : Trace St L) (len : NatOmega) (LEN : traceLenIs tr len) :
    ∀ i, (∃ st, tr !! i = some (st, none)) ↔ len = .num (i + 1) := by
  intro i
  rcases trace_lookup_trichotomy tr len LEN i with ⟨st, ℓ, st', H, LT⟩ | ⟨st, H, rfl⟩ | ⟨H, LE⟩
  · rw [H]
    simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq, and_false, exists_false,
      false_iff]
    rintro rfl; simp [ltNatL] at LT
  · exact ⟨fun _ => rfl, fun _ => ⟨st, H⟩⟩
  · rw [H]
    simp only [reduceCtorEq, exists_false, false_iff]
    rintro rfl; simp [NatOmega.le] at LE

@[rocq_alias trillium.fairness.state_label_lookup]
theorem state_label_lookup (tr : Trace St L) :
    ∀ i st st' ℓ, tr !! i = some (st, some (ℓ, st')) ↔
      (tr S!! i = some st ∧ tr S!! (i + 1) = some st' ∧ tr L!! i = some ℓ) := by
  intro i st st' ℓ
  simp only [traceLookup_eq, stateLookup_eq, labelLookup_eq]
  rw [after_succ]
  cases after i tr with
  | none => simp
  | some t =>
    cases t with
    | singl s => simp
    | cons s ℓ' r => simp; tauto

@[rocq_alias trillium.fairness.state_lookup_dom]
theorem state_lookup_dom (tr : Trace St L) (len : NatOmega) (LEN : traceLenIs tr len) :
    ∀ i, (tr S!! i).isSome ↔ ltNatL i len := by
  intro i
  rw [← LEN i, stateLookup_eq, Option.isSome_map]

@[rocq_alias trillium.fairness.state_lookup_dom_neg]
theorem state_lookup_dom_neg (tr : Trace St L) (len : NatOmega) (LEN : traceLenIs tr len) :
    ∀ i, tr S!! i = none ↔ NatOmega.le len (.num i) := by
  intro i
  rw [← trace_len_neg tr len LEN i, stateLookup_eq, Option.map_eq_none_iff]

@[rocq_alias trillium.fairness.label_lookup_dom]
theorem label_lookup_dom (tr : Trace St L) (len : NatOmega) (LEN : traceLenIs tr len) :
    ∀ i, (tr L!! i).isSome ↔ ltNatL (i + 1) len := by
  intro i
  rw [← LEN (i + 1), labelLookup_eq, after_succ]
  cases after i tr with
  | none => simp
  | some t => cases t <;> simp

@[rocq_alias trillium.fairness.state_lookup_prev]
theorem state_lookup_prev (tr : Trace St L) (i : Nat) (DOM : (tr S!! i).isSome) :
    ∀ j, j ≤ i → (tr S!! j).isSome := by
  intro j LE
  rw [stateLookup_eq, Option.isSome_map] at DOM ⊢
  exact after_is_Some_le tr i j LE DOM

@[rocq_alias trillium.fairness.label_lookup_prev]
theorem label_lookup_prev (tr : Trace St L) (i : Nat) (DOM : (tr L!! i).isSome) :
    ∀ j, j ≤ i → (tr L!! j).isSome := by
  intro j LE
  obtain ⟨len, LEN⟩ := trace_has_len tr
  rw [label_lookup_dom tr len LEN] at DOM ⊢
  exact NatOmega.le_lt_nat _ _ _ (by omega) DOM

@[rocq_alias trillium.fairness.label_lookup_states]
theorem label_lookup_states (tr : Trace St L) :
    ∀ i, (tr L!! i).isSome ↔ (tr S!! i).isSome ∧ (tr S!! (i + 1)).isSome := by
  obtain ⟨len, LEN⟩ := trace_has_len tr
  intro i
  rw [label_lookup_dom tr len LEN, state_lookup_dom tr len LEN, state_lookup_dom tr len LEN]
  exact ⟨fun h => ⟨NatOmega.lt_lt_nat _ _ _ (by omega) h, h⟩, fun h => h.2⟩

@[rocq_alias trillium.fairness.label_lookup_states']
theorem label_lookup_states' (tr : Trace St L) :
    ∀ i, (tr L!! i).isSome ↔ (tr S!! (i + 1)).isSome := by
  intro i
  rw [label_lookup_states]
  exact ⟨And.right, fun h => ⟨state_lookup_prev tr (i + 1) h i (by omega), h⟩⟩

@[rocq_alias trillium.fairness.next_state_lookup]
theorem next_state_lookup (tr : Trace St L) :
    ∀ i, (tr S!! (i + 1)).isSome ↔ (tr S!! i).isSome ∧ (tr L!! i).isSome := by
  intro i
  rw [label_lookup_states]
  exact ⟨fun h => ⟨state_lookup_prev tr (i + 1) h i (by omega),
    state_lookup_prev tr (i + 1) h i (by omega), h⟩, fun h => h.2.2⟩

@[rocq_alias trillium.fairness.pred_at_trace_lookup]
theorem pred_at_trace_lookup (tr : Trace St L) (i : Nat) (P : St → Option L → Prop) :
    predAt tr i P ↔ ∃ st, tr S!! i = some st ∧ P st (tr L!! i) := by
  simp only [stateLookup_eq, labelLookup_eq]
  unfold predAt
  cases after i tr <;> simp

@[rocq_alias trillium.fairness.pred_at_trace_lookup']
theorem pred_at_trace_lookup' (tr : Trace St L) (i : Nat) (P : St → Option L → Prop) :
    predAt tr i P ↔ ∃ s step, tr !! i = some (s, step) ∧ P s (step.map Prod.fst) := by
  simp only [traceLookup_eq]
  unfold predAt
  cases after i tr with
  | none => simp
  | some t => cases t <;> simp

@[rocq_alias trillium.fairness.inf_trace_lookup]
theorem inf_trace_lookup (tr : Trace St L) (INF : traceLenIs tr .infinity) :
    ∀ i, ∃ c1 ℓ c2, tr !! i = some (c1, some (ℓ, c2)) :=
  fun i => (trace_lookup_dom_strong tr _ INF i).2 trivial

@[rocq_alias trillium.fairness.trace_lookup_cons, simp]
theorem trace_lookup_cons (s : St) (l : L) (tr : Trace St L) (i : Nat) :
    (s -[l]-> tr) !! (i + 1) = tr !! i := by
  simp

@[rocq_alias trillium.fairness.trace_state_lookup_simpl]
theorem trace_state_lookup_simpl (tr : Trace St L) (i : Nat) (s' : St)
    (step : Option (L × St)) (s : St) (TLi : tr !! i = some (s', step))
    (SLi : tr S!! i = some s) : s' = s := by
  simp only [traceLookup_eq, stateLookup_eq] at TLi SLi
  cases h : after i tr with
  | none => simp [h] at TLi
  | some t =>
    rw [h] at TLi SLi
    simp only [Option.map_some, Option.some.injEq] at TLi SLi
    rw [← SLi]
    exact (congrArg Prod.fst TLi).symm

@[rocq_alias trillium.fairness.trace_lookup_0_cons, simp]
theorem trace_lookup_0_cons (s : St) (ℓ : L) (tr : Trace St L) :
    (s -[ℓ]-> tr) !! 0 = some (s, some (ℓ, tr.first)) := by
  simp

/-- As in Rocq, this lemma is stated about `S!!` (the label variant is
`labelLookup_succ_cons`). -/
@[rocq_alias trillium.fairness.state_lookup_cons, simp]
theorem state_lookup_cons (s : St) (l : L) (tr : Trace St L) (i : Nat) :
    (s -[l]-> tr) S!! (i + 1) = tr S!! i := by
  simp

/-- Rocq's `label_lookup_cons` is (by a typo) the same statement as `state_lookup_cons`, about
`S!!`; we port it as stated. See `labelLookup_succ_cons` for the `L!!` version. -/
@[rocq_alias trillium.fairness.label_lookup_cons]
theorem label_lookup_cons (s : St) (l : L) (tr : Trace St L) (i : Nat) :
    (s -[l]-> tr) S!! (i + 1) = tr S!! i := by
  simp

@[simp] theorem labelLookup_succ_cons (s : St) (l : L) (tr : Trace St L) (i : Nat) :
    (s -[l]-> tr) L!! (i + 1) = tr L!! i := by
  simp

@[rocq_alias trillium.fairness.trace_label_lookup_simpl]
theorem trace_label_lookup_simpl (tr : Trace St L) (i : Nat) (step : St × Option (L × St))
    (ℓ : L) (TLi : tr !! i = some step) (SLi : tr L!! i = some ℓ) :
    ∃ s1 s2, step = (s1, some (ℓ, s2)) := by
  simp only [traceLookup_eq, labelLookup_eq] at TLi SLi
  cases h : after i tr with
  | none => simp [h] at TLi
  | some t =>
    rw [h] at TLi SLi
    simp only [Option.map_some, Option.some.injEq, Option.bind_some] at TLi SLi
    subst TLi
    cases t with
    | singl s => simp at SLi
    | cons s ℓ' r =>
      simp only [label?_cons, Option.some.injEq] at SLi
      subst SLi
      exact ⟨s, r.first, by simp⟩

@[rocq_alias trillium.fairness.state_lookup_0, simp]
theorem state_lookup_0 (tr : Trace St L) : tr S!! 0 = some tr.first := by
  simp

@[rocq_alias trillium.fairness.label_lookup_0, simp]
theorem label_lookup_0 (st : St) (ℓ : L) (tr : Trace St L) : (st -[ℓ]-> tr) L!! 0 = some ℓ := by
  simp

@[rocq_alias trillium.fairness.trace_state_lookup_simpl']
theorem trace_state_lookup_simpl' (tr : Trace St L) (i : Nat) (st : St) :
    (∃ step, tr !! i = some step ∧ step.1 = st) ↔ tr S!! i = some st := by
  simp only [traceLookup_eq, stateLookup_eq]
  cases after i tr with
  | none => simp
  | some t => simp [headStep]

@[rocq_alias trillium.fairness.trace_state_lookup]
theorem trace_state_lookup (tr : Trace St L) (i : Nat) (st : St) (ostep : Option (L × St))
    (ITH : tr !! i = some (st, ostep)) : tr S!! i = some st :=
  (trace_state_lookup_simpl' tr i st).1 ⟨_, ITH, rfl⟩

@[rocq_alias trillium.fairness.trace_label_lookup_simpl']
theorem trace_label_lookup_simpl' (tr : Trace St L) (i : Nat) (ℓ : L) :
    (∃ s1 s2, tr !! i = some (s1, some (ℓ, s2))) ↔ tr L!! i = some ℓ := by
  constructor
  · rintro ⟨_, _, H⟩
    exact ((state_label_lookup tr i _ _ _).1 H).2.2
  · simp only [traceLookup_eq, labelLookup_eq]
    cases after i tr with
    | none => simp
    | some t =>
      cases t with
      | singl s => simp
      | cons s ℓ' r => simp only [Option.bind_some, label?_cons, Option.some.injEq]; rintro rfl; simp

@[rocq_alias trillium.fairness.trace_lookup_0_singleton, simp]
theorem trace_lookup_0_singleton (s : St) : (singl s : Trace St L) !! 0 = some (s, none) := by
  simp

@[rocq_alias trillium.fairness.trace_lookup_0]
theorem trace_lookup_0 (tr : Trace St L) : ∃ ostep, tr !! 0 = some (tr.first, ostep) :=
  ⟨tr.headStep.2, by simp [headStep]⟩

@[rocq_alias trillium.fairness.trace_lookup_0_Some]
theorem trace_lookup_0_Some (tr : Trace St L) : (tr !! 0).isSome := by
  simp

end TraceLookup

section After

variable {St L : Type _}

attribute [local simp] traceLookup_eq stateLookup_eq labelLookup_eq

@[rocq_alias trillium.fairness.trace_lookup_after]
theorem trace_lookup_after (tr atr : Trace St L) (a : Nat) (AFTER : after a tr = some atr) :
    ∀ k, atr !! k = tr !! (a + k) := by
  intro k
  simp [after_sum', AFTER]

@[rocq_alias trillium.fairness.state_lookup_after]
theorem state_lookup_after (tr atr : Trace St L) (a : Nat) (AFTER : after a tr = some atr) :
    ∀ k, atr S!! k = tr S!! (a + k) := by
  intro k
  simp [after_sum', AFTER]

@[rocq_alias trillium.fairness.label_lookup_after]
theorem label_lookup_after (tr atr : Trace St L) (a : Nat) (AFTER : after a tr = some atr) :
    ∀ k, atr L!! k = tr L!! (a + k) := by
  intro k
  simp [after_sum', AFTER]

@[rocq_alias trillium.fairness.state_lookup_after_0]
theorem state_lookup_after_0 (tr atr : Trace St L) (n : Nat) (AFTER : after n tr = some atr) :
    tr S!! n = some atr.first := by
  simp [AFTER]

@[rocq_alias trillium.fairness.state_lookup_after']
theorem state_lookup_after' (tr : Trace St L) (n : Nat) (st : St) :
    (∃ atr, after n tr = some atr ∧ atr.first = st) ↔ tr S!! n = some st := by
  simp

@[rocq_alias trillium.fairness.trace_lookup_after_strong]
theorem trace_lookup_after_strong (tr : Trace St L) (s1 : St) (ℓ : L) (s2 : St) (n : Nat) :
    (∃ atr', after n tr = some (s1 -[ℓ]-> atr') ∧ atr'.first = s2) ↔
      tr !! n = some (s1, some (ℓ, s2)) := by
  simp only [traceLookup_eq]
  cases after n tr with
  | none => simp
  | some t =>
    cases t with
    | singl s => simp
    | cons s ℓ' r =>
      simp only [Option.some.injEq, cons_inj, Option.map_some, headStep_cons, Prod.mk.injEq]
      constructor
      · rintro ⟨_, ⟨rfl, rfl, rfl⟩, rfl⟩; exact ⟨rfl, rfl, rfl⟩
      · rintro ⟨rfl, rfl, rfl⟩; exact ⟨r, ⟨rfl, rfl, rfl⟩, rfl⟩

@[rocq_alias trillium.fairness.trace_lookup_after_weak]
theorem trace_lookup_after_weak (tr : Trace St L) (s : St) (n : Nat) :
    (∃ atr, after n tr = some atr ∧ atr.first = s) ↔ ∃ ostep, tr !! n = some (s, ostep) := by
  simp only [traceLookup_eq]
  cases after n tr with
  | none => simp
  | some t =>
    simp only [Option.some.injEq, exists_eq_left', Option.map_some, headStep, Prod.mk.injEq]
    exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩

@[rocq_alias trillium.fairness.trace_lookup_prev]
theorem trace_lookup_prev (tr : Trace St L) (i : Nat) (st2 : St) (ostep : Option (L × St))
    (ITH' : tr !! (i + 1) = some (st2, ostep)) :
    ∃ st1 l, tr !! i = some (st1, some (l, st2)) := by
  simp only [traceLookup_eq] at ITH' ⊢
  rw [after_succ] at ITH'
  cases h : after i tr with
  | none => simp [h] at ITH'
  | some t =>
    rw [h] at ITH'
    cases t with
    | singl s => simp at ITH'
    | cons s l r =>
      simp only [Option.bind_some, after_one_cons, Option.map_some, Option.some.injEq,
        headStep] at ITH'
      exact ⟨s, l, by simpa using congrArg Prod.fst ITH'⟩

end After

section TracesMatch

attribute [local simp] traceLookup_eq stateLookup_eq labelLookup_eq

variable {L1 L2 S1 S2 : Type _}
variable {Rℓ : L1 → L2 → Prop} {Rs : S1 → S2 → Prop}
variable {trans1 : S1 → L1 → S1 → Prop} {trans2 : S2 → L2 → S2 → Prop}

@[rocq_alias trillium.fairness.traces_match_trace_lookup_general]
theorem traces_match_trace_lookup_general (tr1 : Trace S1 L1) (tr2 : Trace S2 L2) (n : Nat)
    (MATCH : TracesMatch Rℓ Rs trans1 trans2 tr1 tr2) :
    match tr1 !! n, tr2 !! n with
    | some step1, some step2 =>
        Rs step1.1 step2.1 ∧
          match step1.2, step2.2 with
          | some (ℓ1, s1'), some (ℓ2, s2') => Rℓ ℓ1 ℓ2 ∧ Rs s1' s2'
          | none, none => True
          | _, _ => False
    | none, none => True
    | _, _ => False := by
  simp only [traceLookup_eq]
  cases h2 : after n tr2 with
  | none =>
    rw [traces_match_after_None Rℓ Rs trans1 trans2 tr1 tr2 n MATCH h2]
    trivial
  | some t2 =>
    obtain ⟨t1, h1, Hm⟩ := traces_match_after tr1 tr2 n t2 MATCH h2
    rw [h1]
    rcases Hm.inv with ⟨s1, s2, H, rfl, rfl⟩ | ⟨s1, ℓ1, r1, s2, ℓ2, r2, H1, H2, -, -, H5, rfl, rfl⟩
    · exact ⟨H, trivial⟩
    · exact ⟨H2, H1, traces_match_first r1 r2 H5⟩

@[rocq_alias trillium.fairness.traces_match_state_lookup_1]
theorem traces_match_state_lookup_1 (tr1 : Trace S1 L1) (tr2 : Trace S2 L2) (n : Nat) (st1 : S1)
    (MATCH : TracesMatch Rℓ Rs trans1 trans2 tr1 tr2) (ST1 : tr1 S!! n = some st1) :
    ∃ st2, tr2 S!! n = some st2 ∧ Rs st1 st2 := by
  obtain ⟨⟨s1, ostep1⟩, NTH1, rfl⟩ := (trace_state_lookup_simpl' tr1 n st1).2 ST1
  have STEPS := traces_match_trace_lookup_general tr1 tr2 n MATCH
  rw [NTH1] at STEPS
  cases NTH2 : tr2 !! n with
  | none => rw [NTH2] at STEPS; exact STEPS.elim
  | some step2 =>
    rw [NTH2] at STEPS
    exact ⟨step2.1, (trace_state_lookup_simpl' tr2 n _).1 ⟨_, NTH2, rfl⟩, STEPS.1⟩

@[rocq_alias trillium.fairness.traces_match_state_lookup_2]
theorem traces_match_state_lookup_2 (tr1 : Trace S1 L1) (tr2 : Trace S2 L2) (n : Nat) (st2 : S2)
    (MATCH : TracesMatch Rℓ Rs trans1 trans2 tr1 tr2) (ST2 : tr2 S!! n = some st2) :
    ∃ st1, tr1 S!! n = some st1 ∧ Rs st1 st2 := by
  obtain ⟨⟨s2, ostep2⟩, NTH2, rfl⟩ := (trace_state_lookup_simpl' tr2 n st2).2 ST2
  have STEPS := traces_match_trace_lookup_general tr1 tr2 n MATCH
  rw [NTH2] at STEPS
  cases NTH1 : tr1 !! n with
  | none => rw [NTH1] at STEPS; exact STEPS.elim
  | some step1 =>
    rw [NTH1] at STEPS
    exact ⟨step1.1, (trace_state_lookup_simpl' tr1 n _).1 ⟨_, NTH1, rfl⟩, STEPS.1⟩

@[rocq_alias trillium.fairness.traces_match_label_lookup_1]
theorem traces_match_label_lookup_1 (tr1 : Trace S1 L1) (tr2 : Trace S2 L2) (n : Nat) (ℓ1 : L1)
    (MATCH : TracesMatch Rℓ Rs trans1 trans2 tr1 tr2) (LBL1 : tr1 L!! n = some ℓ1) :
    ∃ ℓ2, tr2 L!! n = some ℓ2 ∧ Rℓ ℓ1 ℓ2 := by
  obtain ⟨s, s', NTH1⟩ := (trace_label_lookup_simpl' tr1 n ℓ1).2 LBL1
  have STEPS := traces_match_trace_lookup_general tr1 tr2 n MATCH
  rw [NTH1] at STEPS
  cases NTH2 : tr2 !! n with
  | none => rw [NTH2] at STEPS; exact STEPS.elim
  | some step2 =>
    rw [NTH2] at STEPS
    obtain ⟨s2, ostep2⟩ := step2
    cases ostep2 with
    | none => exact STEPS.2.elim
    | some p =>
      obtain ⟨ℓ2, s2'⟩ := p
      exact ⟨ℓ2, (trace_label_lookup_simpl' tr2 n ℓ2).1 ⟨_, _, NTH2⟩, STEPS.2.1⟩

@[rocq_alias trillium.fairness.traces_match_label_lookup_2]
theorem traces_match_label_lookup_2 (tr1 : Trace S1 L1) (tr2 : Trace S2 L2) (n : Nat) (ℓ2 : L2)
    (MATCH : TracesMatch Rℓ Rs trans1 trans2 tr1 tr2) (LBL2 : tr2 L!! n = some ℓ2) :
    ∃ ℓ1, tr1 L!! n = some ℓ1 ∧ Rℓ ℓ1 ℓ2 := by
  obtain ⟨s, s', NTH2⟩ := (trace_label_lookup_simpl' tr2 n ℓ2).2 LBL2
  have STEPS := traces_match_trace_lookup_general tr1 tr2 n MATCH
  rw [NTH2] at STEPS
  cases NTH1 : tr1 !! n with
  | none => rw [NTH1] at STEPS; exact STEPS.elim
  | some step1 =>
    rw [NTH1] at STEPS
    obtain ⟨s1, ostep1⟩ := step1
    cases ostep1 with
    | none => exact STEPS.2.elim
    | some p =>
      obtain ⟨ℓ1, s1'⟩ := p
      exact ⟨ℓ1, (trace_label_lookup_simpl' tr1 n ℓ1).1 ⟨_, _, NTH1⟩, STEPS.2.1⟩

end TracesMatch

section ValidTracesProperties

attribute [local simp] traceLookup_eq stateLookup_eq labelLookup_eq

variable {St L : Type _} (trans : St → L → St → Prop)

@[rocq_alias trillium.fairness.trace_valid_steps']
theorem trace_valid_steps' (tr : Trace St L) (VALID : TraceValid trans tr) (i : Nat) (st : St)
    (ℓ : L) (st' : St) (ITH : tr !! i = some (st, some (ℓ, st'))) : trans st ℓ st' := by
  induction i generalizing tr with
  | zero =>
    cases tr with
    | singl s => simp at ITH
    | cons s ℓ' r =>
      simp only [traceLookup_eq, after_0_id, Option.map_some, headStep_cons, Option.some.injEq,
        Prod.mk.injEq] at ITH
      obtain ⟨rfl, rfl, rfl⟩ := ITH
      exact (trace_valid_cons_inv r _ _ VALID).2
  | succ i IHi =>
    cases tr with
    | singl s => simp at ITH
    | cons s ℓ' r =>
      rw [trace_lookup_cons] at ITH
      exact IHi r (trace_valid_tail s ℓ' r VALID) ITH

@[rocq_alias trillium.fairness.trace_valid_steps'']
theorem trace_valid_steps'' (tr : Trace St L) (VALID : TraceValid trans tr) (i : Nat) (st : St)
    (ℓ : L) (st' : St) (ST1 : tr S!! i = some st) (ST2 : tr S!! (i + 1) = some st')
    (LBL : tr L!! i = some ℓ) : trans st ℓ st' :=
  trace_valid_steps' trans tr VALID i st ℓ st' ((state_label_lookup tr i st st' ℓ).2 ⟨ST1, ST2, LBL⟩)

end ValidTracesProperties

end Trillium.Fairness
