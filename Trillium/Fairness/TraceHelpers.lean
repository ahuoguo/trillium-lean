/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.Fairness.TraceLen
import Trillium.Fairness.TraceLookup
import Trillium.Fairness.Inftraces
import Trillium.Fairness.Fairness
import Trillium.Fairness.TraceUtils
import Trillium.Fairness.NatOmega

/-!
# Helpers on fair model traces
Port of `fairness/trace_helpers.v`.

Alternative (minimal-step) characterisations of `fairModelTrace`, and lemmas about properties of
model states preserved along valid model traces. Rocq's `ClassicalFacts.Minimal P m` is
`IsLeast {x | P x} m`.
-/

namespace Trillium.Fairness

open Trace

section FMTraceHelpers

variable {M : FairModel}

/-- `tr` is fair for all roles satisfying `T`. -/
@[rocq_alias trillium.fairness.set_fair_model_trace]
def setFairModelTrace (T : M.fmrole → Prop) (tr : Mtrace M) : Prop :=
  ∀ ρ, T ρ → fairModelTrace ρ tr

/-- Fairness of `tr` for `ρ`, with the first position where `ρ` is disabled or steps. -/
@[rocq_alias trillium.fairness.strong_fair_model_trace]
def strongFairModelTrace (tr : Mtrace M) (ρ : M.fmrole) : Prop :=
  ∀ n, predAt tr n (fun δ _ => roleEnabledModel ρ δ) →
    ∃ m, IsLeast {x | predAt tr (n + x)
      (fun δ ℓ => ¬ roleEnabledModel ρ δ ∨ ℓ = some (some ρ))} m

private theorem fairnessSat_role_iff (ρ : M.fmrole) (δ : M.fmstate) (ℓ : Option (Option M.fmrole)) :
    fairnessSat roleEnabledModel roleMatch ρ δ ℓ ↔
      (¬ roleEnabledModel ρ δ ∨ ℓ = some (some ρ)) := by
  unfold fairnessSat roleMatch
  constructor
  · rintro (h | ⟨_, rfl, rfl⟩)
    · exact .inl h
    · exact .inr rfl
  · rintro (h | rfl)
    · exact .inl h
    · exact .inr ⟨_, rfl, rfl⟩

@[rocq_alias trillium.fairness.fair_model_trace_defs_equiv]
theorem fair_model_trace_defs_equiv (tr : Mtrace M) (ρ : M.fmrole) :
    fairModelTrace ρ tr ↔ strongFairModelTrace tr ρ := by
  unfold fairModelTrace fairBy strongFairModelTrace
  have E : ∀ k, predAt tr k (fairnessSat roleEnabledModel roleMatch ρ) ↔
      predAt tr k (fun δ ℓ => ¬ roleEnabledModel ρ δ ∨ ℓ = some (some ρ)) :=
    pred_at_iff _ _ (fairnessSat_role_iff ρ) tr
  simp only [E]
  refine forall_congr' fun n => imp_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨x, H⟩
    classical
    exact min_prop_dec (fun x => predAt tr (n + x)
      (fun δ ℓ => ¬ roleEnabledModel ρ δ ∨ ℓ = some (some ρ))) x H
  · rintro ⟨m, H, -⟩
    exact ⟨m, H⟩

/-- `strongFairModelTrace` stated with lookups. -/
@[rocq_alias trillium.fairness.strong_fair_model_trace_alt]
def strongFairModelTraceAlt (tr : Mtrace M) (ρ : M.fmrole) : Prop :=
  ∀ n st, tr S!! n = some st → roleEnabledModel ρ st →
    ∃ m, IsLeast {x | (∃ st', tr S!! (n + x) = some st' ∧ ¬ roleEnabledModel ρ st') ∨
      tr L!! (n + x) = some (some ρ)} m

private theorem pred_disabled_or_step_iff (tr : Mtrace M) (ρ : M.fmrole) (k : Nat) :
    predAt tr k (fun δ ℓ => ¬ roleEnabledModel ρ δ ∨ ℓ = some (some ρ)) ↔
      ((∃ st', tr S!! k = some st' ∧ ¬ roleEnabledModel ρ st') ∨
        tr L!! k = some (some ρ)) := by
  rw [pred_at_trace_lookup]
  constructor
  · rintro ⟨st, ST, DIS | STEP⟩
    · exact .inl ⟨st, ST, DIS⟩
    · exact .inr STEP
  · rintro (⟨st, ST, DIS⟩ | STEP)
    · exact ⟨st, ST, .inl DIS⟩
    · have := ((label_lookup_states tr k).1 (by rw [STEP]; rfl)).1
      obtain ⟨st, ST⟩ := Option.isSome_iff_exists.1 this
      exact ⟨st, ST, .inr STEP⟩

@[rocq_alias trillium.fairness.strong_fair_model_trace_alt_defs_equiv]
theorem strong_fair_model_trace_alt_defs_equiv (tr : Mtrace M) (ρ : M.fmrole) :
    strongFairModelTrace tr ρ ↔ strongFairModelTraceAlt tr ρ := by
  unfold strongFairModelTrace strongFairModelTraceAlt
  simp only [pred_disabled_or_step_iff]
  constructor
  · intro H n st NTH EN
    exact H n ((pred_at_trace_lookup tr n _).2 ⟨st, NTH, EN⟩)
  · intro H n EN
    obtain ⟨st, NTH, EN⟩ := (pred_at_trace_lookup tr n _).1 EN
    exact H n st NTH EN

section ValidTracesProperties

/-- `Ps` is preserved by the model steps satisfying `Pstep`. -/
@[rocq_alias trillium.fairness.label_kept_state_gen]
def labelKeptStateGen (Ps : M.fmstate → Prop)
    (Pstep : M.fmstate → Option M.fmrole → M.fmstate → Prop) : Prop :=
  ∀ st oℓ' st', Ps st → Pstep st oℓ' st' → M.fmtrans st oℓ' st' → Ps st'

@[rocq_alias trillium.fairness.steps_keep_state_gen]
theorem steps_keep_state_gen {tr : Mtrace M} (VALID : MtraceValid tr) (i : Nat)
    (P : M.fmstate → Prop) (Pstep : M.fmstate → Option M.fmrole → M.fmstate → Prop) (j : Nat)
    (Pi : ∃ st, tr S!! i = some st ∧ P st) (P_KEPT : labelKeptStateGen P Pstep)
    (NOρ : ∀ (k : Nat) st1 oℓ' st2, i ≤ k ∧ k < j →
      tr !! k = some (st1, some (oℓ', st2)) → Pstep st1 oℓ' st2) :
    ∀ k st', i ≤ k ∧ k ≤ j → tr S!! k = some st' → P st' := by
  rintro k st' ⟨IK, KJ⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le IK
  induction d generalizing st' with
  | zero =>
    obtain ⟨st, ST, Pst⟩ := Pi
    intro KTH
    rw [Nat.add_zero, ST, Option.some.injEq] at KTH
    exact KTH ▸ Pst
  | succ d IHd =>
    intro KTH
    rw [← Nat.add_assoc] at KTH
    obtain ⟨PREV, LBL⟩ := (next_state_lookup tr (i + d)).1 (by rw [KTH]; rfl)
    obtain ⟨st, ST⟩ := Option.isSome_iff_exists.1 PREV
    obtain ⟨oℓ', LB⟩ := Option.isSome_iff_exists.1 LBL
    have CUR : tr !! (i + d) = some (st, some (oℓ', st')) :=
      (state_label_lookup tr (i + d) st st' oℓ').2 ⟨ST, KTH, LB⟩
    exact P_KEPT st oℓ' st' (IHd st (by omega) (by omega) ST)
      (NOρ (i + d) st oℓ' st' ⟨by omega, by omega⟩ CUR)
      (trace_valid_steps' _ tr VALID (i + d) st oℓ' st' CUR)

/-- `Ps` is preserved by the model steps whose label satisfies `Pl`. -/
@[rocq_alias trillium.fairness.label_kept_state]
def labelKeptState (Ps : M.fmstate → Prop) (Pl : Option M.fmrole → Prop) : Prop :=
  ∀ st oℓ' st', Ps st → Pl oℓ' → M.fmtrans st oℓ' st' → Ps st'

/-- The step is not taken by `ρ`. -/
@[rocq_alias trillium.fairness.other_step]
def otherStep (ρ : M.fmrole) : Option M.fmrole → Prop := fun oρ' => oρ' ≠ some ρ

@[rocq_alias trillium.fairness.steps_keep_state]
theorem steps_keep_state {tr : Mtrace M} (VALID : MtraceValid tr) (i : Nat)
    (P : M.fmstate → Prop) (Pl : Option M.fmrole → Prop) (j : Nat)
    (Pi : ∃ st, tr S!! i = some st ∧ P st) (P_KEPT : labelKeptState P Pl)
    (NOρ : ∀ (k : Nat) oℓ', i ≤ k ∧ k < j → tr L!! k = some oℓ' → Pl oℓ') :
    ∀ k st', i ≤ k ∧ k ≤ j → tr S!! k = some st' → P st' :=
  steps_keep_state_gen VALID i P (fun _ oℓ' _ => Pl oℓ') j Pi
    (fun st oℓ' st' Pst Pl' STEP => P_KEPT st oℓ' st' Pst Pl' STEP)
    (fun k _ oℓ' _ IKJ KTH => NOρ k oℓ' IKJ ((state_label_lookup tr k _ _ _).1 KTH).2.2)

@[rocq_alias trillium.fairness.steps_keep_state_inf]
theorem steps_keep_state_inf {tr : Mtrace M} (VALID : MtraceValid tr) (i : Nat)
    (P : M.fmstate → Prop) (Pl : Option M.fmrole → Prop)
    (Pi : ∃ st, tr S!! i = some st ∧ P st) (P_KEPT : labelKeptState P Pl)
    (NOρ : ∀ (k : Nat) oℓ', i ≤ k → tr L!! k = some oℓ' → Pl oℓ') :
    ∀ k st', i ≤ k → tr S!! k = some st' → P st' :=
  fun k st' IK KTH => steps_keep_state VALID i P Pl k Pi P_KEPT
    (fun p oℓ' IPK LBL => NOρ p oℓ' IPK.1 LBL) k st' ⟨IK, le_rfl⟩ KTH

@[rocq_alias trillium.fairness.kept_state_fair_step]
theorem kept_state_fair_step {tr : Mtrace M} (VALID : MtraceValid tr) (ρ : M.fmrole)
    (P : M.fmstate → Prop) (KEPT : labelKeptState P (otherStep ρ))
    (P_EN : ∀ st, P st → roleEnabledModel ρ st) (FAIRρ : fairModelTrace ρ tr) :
    ∀ i st, tr S!! i = some st → P st →
      ∃ j st', IsLeast {j | i ≤ j ∧ tr L!! j = some (some ρ)} j ∧ tr S!! j = some st' ∧
        P st' := by
  intro i st ITH Pst
  have FAIR := (strong_fair_model_trace_alt_defs_equiv tr ρ).1
    ((fair_model_trace_defs_equiv tr ρ).1 FAIRρ)
  obtain ⟨d, STEP, MIN⟩ := FAIR i st ITH (P_EN st Pst)
  have DOM : (tr S!! (i + d)).isSome := by
    rcases STEP with ⟨st', ST', -⟩ | STEP
    · rw [ST']; rfl
    · exact ((label_lookup_states tr (i + d)).1 (by rw [STEP]; rfl)).1
  obtain ⟨st', IDTH⟩ := Option.isSome_iff_exists.1 DOM
  have NEXT_EN := steps_keep_state VALID i P (otherStep ρ) (i + d) ⟨st, ITH, Pst⟩ KEPT
    (by
      rintro k oℓ' ⟨IK, KJ⟩ LBL rfl
      obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le IK
      have := MIN (show v ∈ _ from .inr LBL)
      omega)
    (i + d) st' ⟨by omega, le_rfl⟩ IDTH
  rcases STEP with ⟨st'_, ST', DIS'⟩ | STEP
  · rw [IDTH, Option.some.injEq] at ST'
    subst ST'
    exact (DIS' (P_EN _ NEXT_EN)).elim
  · refine ⟨i + d, st', ⟨⟨by omega, STEP⟩, ?_⟩, IDTH, NEXT_EN⟩
    rintro k ⟨LE', STEP'⟩
    obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le LE'
    have := MIN (show d' ∈ _ from .inr STEP')
    omega

end ValidTracesProperties

end FMTraceHelpers

end Trillium.Fairness
