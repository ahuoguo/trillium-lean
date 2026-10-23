/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.Fairness.Inftraces
import Trillium.Traces.Trace

/-!
# Utilities on possibly infinite traces
Port of `fairness/trace_utils.v`.

* `traceImplies P Q tr` (Rocq `trace_implies`): whenever `P` holds, `Q` holds later.
* `traceTake n tr` (Rocq `trace_take`), `traceFilter f ft` (Rocq `trace_filter`),
  `countLabels ft` (Rocq `count_labels`) and `finiteTraceToTrace ft`
  (Rocq `finite_trace_to_trace`) convert between possibly infinite traces and the finite
  traces of `Trillium.Traces.Trace`. As in Rocq, `traceTake` and `finiteTraceToTrace` reverse
  the order of the states (the finite trace is extended at its end).
* `traceNow`, `traceAlways`, `traceEventually`, `traceUntil`: temporal predicates.

Rocq's `is_Some (after n tr)` is `(after n tr).isSome`.
-/

namespace Trillium.Fairness

open Trace
open Trillium (FiniteTrace)

section trace_utils

variable {S L : Type _}

/-- Whenever `P` holds on `tr`, `Q` holds at the same or a later position. -/
@[rocq_alias trillium.fairness.trace_implies]
def traceImplies (P Q : S → Option L → Prop) (tr : Trace S L) : Prop :=
  ∀ n, predAt tr n P → ∃ m, predAt tr (n + m) Q

@[rocq_alias trillium.fairness.trace_implies_after]
theorem trace_implies_after (P Q : S → Option L → Prop) (tr tr' : Trace S L) (k : Nat)
    (Haf : after k tr = some tr') : traceImplies P Q tr → traceImplies P Q tr' := by
  intro Hf n Hp
  have Hp' : predAt tr (k + n) P := by rw [pred_at_sum, Haf]; exact Hp
  obtain ⟨m, Hm⟩ := Hf (k + n) Hp'
  refine ⟨m, ?_⟩
  rw [Nat.add_assoc, pred_at_sum, Haf] at Hm
  exact Hm

@[rocq_alias trillium.fairness.trace_implies_cons]
theorem trace_implies_cons (P Q : S → Option L → Prop) (s : S) (l : L) (tr : Trace S L) :
    traceImplies P Q (s -[l]-> tr) → traceImplies P Q tr :=
  trace_implies_after P Q (s -[l]-> tr) tr 1 (by simp)

end trace_utils

section traces_match

variable {S1 S2 L1 L2 : Type _}

@[rocq_alias trillium.fairness.traces_match_impl]
theorem traces_match_impl (Rℓ1 : L1 → L2 → Prop) (Rs1 : S1 → S2 → Prop)
    (Rℓ2 : L1 → L2 → Prop) (Rs2 : S1 → S2 → Prop)
    (trans1 : S1 → L1 → S1 → Prop) (trans2 : S2 → L2 → S2 → Prop)
    (tr1 : Trace S1 L1) (tr2 : Trace S2 L2)
    (HRℓ : ∀ ℓ1 ℓ2, Rℓ1 ℓ1 ℓ2 → Rℓ2 ℓ1 ℓ2) (HRs : ∀ s1 s2, Rs1 s1 s2 → Rs2 s1 s2) :
    TracesMatch Rℓ1 Rs1 trans1 trans2 tr1 tr2 → TracesMatch Rℓ2 Rs2 trans1 trans2 tr1 tr2 := by
  intro Hmatch
  refine TracesMatch.coinduct Rℓ2 Rs2 trans1 trans2 (TracesMatch Rℓ1 Rs1 trans1 trans2) ?_
    tr1 tr2 Hmatch
  intro tr1 tr2 Hm
  rcases Hm.inv with ⟨s1, s2, h, rfl, rfl⟩ | ⟨s1, ℓ1, r1, s2, ℓ2, r2, h1, h2, h3, h4, h5, rfl, rfl⟩
  · exact .inl ⟨s1, s2, HRs _ _ h, rfl, rfl⟩
  · exact .inr ⟨s1, ℓ1, r1, s2, ℓ2, r2, HRℓ _ _ h1, HRs _ _ h2, h3, h4, h5, rfl, rfl⟩

@[rocq_alias trillium.fairness.traces_match_infinite_trace]
theorem traces_match_infinite_trace (Rℓ : L1 → L2 → Prop) (Rs : S1 → S2 → Prop)
    (trans1 : S1 → L1 → S1 → Prop) (trans2 : S2 → L2 → S2 → Prop)
    (tr1 : Trace S1 L1) (tr2 : Trace S2 L2) :
    TracesMatch Rℓ Rs trans1 trans2 tr1 tr2 → infiniteTrace tr1 → infiniteTrace tr2 := by
  intro Hmatch Hinf n
  obtain ⟨tr', Hafter⟩ := Option.isSome_iff_exists.1 (Hinf n)
  obtain ⟨tr'', Hafter', -⟩ := traces_match_after' tr1 tr2 n tr' Hmatch Hafter
  simp [Hafter']

/-- The relation between the optional labels of two matching positions (the `match` in the
statement of Rocq's `traces_match_traces_implies`). -/
def optLabelRel (Rℓ : L1 → L2 → Prop) : Option L1 → Option L2 → Prop
  | some ℓ1, some ℓ2 => Rℓ ℓ1 ℓ2
  | none, none => True
  | _, _ => False

/-- Matching traces have related first states and related first labels. -/
theorem TracesMatch.first_label_rel {Rℓ : L1 → L2 → Prop} {Rs : S1 → S2 → Prop}
    {trans1 : S1 → L1 → S1 → Prop} {trans2 : S2 → L2 → S2 → Prop}
    {tr1 : Trace S1 L1} {tr2 : Trace S2 L2} (h : TracesMatch Rℓ Rs trans1 trans2 tr1 tr2) :
    Rs tr1.first tr2.first ∧ optLabelRel Rℓ tr1.label? tr2.label? := by
  rcases h.inv with ⟨s1, s2, h0, rfl, rfl⟩ | ⟨s1, ℓ1, r1, s2, ℓ2, r2, h1, h2, -, -, -, rfl, rfl⟩
  · exact ⟨h0, by simp [optLabelRel]⟩
  · exact ⟨h2, by simpa [optLabelRel] using h1⟩

@[rocq_alias trillium.fairness.traces_match_traces_implies]
theorem traces_match_traces_implies (Rℓ : L1 → L2 → Prop) (Rs : S1 → S2 → Prop)
    (trans1 : S1 → L1 → S1 → Prop) (trans2 : S2 → L2 → S2 → Prop)
    (P1 Q1 : S1 → Option L1 → Prop) (P2 Q2 : S2 → Option L2 → Prop)
    (tr1 : Trace S1 L1) (tr2 : Trace S2 L2) :
    TracesMatch Rℓ Rs trans1 trans2 tr1 tr2 →
    (∀ s1 s2 oℓ1 oℓ2, Rs s1 s2 →
      (match oℓ1, oℓ2 with
        | some ℓ1, some ℓ2 => Rℓ ℓ1 ℓ2
        | none, none => True
        | _, _ => False) →
      P2 s2 oℓ2 → P1 s1 oℓ1) →
    (∀ s1 s2 oℓ1 oℓ2, Rs s1 s2 →
      (match oℓ1, oℓ2 with
        | some ℓ1, some ℓ2 => Rℓ ℓ1 ℓ2
        | none, none => True
        | _, _ => False) →
      Q1 s1 oℓ1 → Q2 s2 oℓ2) →
    traceImplies P1 Q1 tr1 → traceImplies P2 Q2 tr2 := by
  intro Hmatch HP HQ Htr1 n Hpred
  cases Ha2 : after n tr2 with
  | none => exact absurd Hpred (predAt_none Ha2 _)
  | some t2 =>
    obtain ⟨t1, Ha1, Hm⟩ := traces_match_after tr1 tr2 n t2 Hmatch Ha2
    obtain ⟨Hs, Hl⟩ := Hm.first_label_rel
    have HP1 : predAt tr1 n P1 := by
      rw [predAt_some Ha1]
      rw [predAt_some Ha2] at Hpred
      exact HP _ _ _ _ Hs (by revert Hl; cases t1.label? <;> cases t2.label? <;> simp [optLabelRel])
        Hpred
    obtain ⟨m, Hm1⟩ := Htr1 n HP1
    refine ⟨m, ?_⟩
    cases Hb1 : after (n + m) tr1 with
    | none => exact absurd Hm1 (predAt_none Hb1 _)
    | some u1 =>
      obtain ⟨u2, Hb2, Hm'⟩ := traces_match_after' tr1 tr2 (n + m) u1 Hmatch Hb1
      obtain ⟨Hs', Hl'⟩ := Hm'.first_label_rel
      rw [predAt_some Hb1] at Hm1
      rw [predAt_some Hb2]
      exact HQ _ _ _ _ Hs' (by revert Hl'; cases u1.label? <;> cases u2.label? <;> simp [optLabelRel])
        Hm1

@[rocq_alias trillium.fairness.traces_match_after_None]
theorem traces_match_after_None (Rℓ : L1 → L2 → Prop) (Rs : S1 → S2 → Prop)
    (trans1 : S1 → L1 → S1 → Prop) (trans2 : S2 → L2 → S2 → Prop)
    (tr1 : Trace S1 L1) (tr2 : Trace S2 L2) (n : Nat) :
    TracesMatch Rℓ Rs trans1 trans2 tr1 tr2 → after n tr2 = none → after n tr1 = none := by
  induction n generalizing tr1 tr2 with
  | zero => intro _ h; simp at h
  | succ n IHn =>
    intro Hm Ha
    cases tr1 with
    | singl s => simp
    | cons s ℓ r1 =>
      cases tr2 with
      | singl s2 => exact Hm.cons_singl_false.elim
      | cons s2 ℓ2 r2 =>
        rw [after_succ_cons] at Ha ⊢
        exact IHn r1 r2 Hm.cons_inv.2.2.2.2 Ha

end traces_match

section finite

variable {S L : Type _}

/-- The first `n` steps of a trace as a finite trace (Rocq `trace_take`). As in Rocq, the
states are stored in reverse order: the first state of `tr` is the last of the result. -/
@[rocq_alias trillium.fairness.trace_take]
def traceTake : Nat → Trace S L → FiniteTrace S L
  | 0, tr => .singleton tr.first
  | n + 1, tr =>
    match tr.dest with
    | .inl s => .singleton s
    | .inr (s, ℓ, r) => .extend (traceTake n r) ℓ s

@[simp] theorem traceTake_zero (tr : Trace S L) : traceTake 0 tr = .singleton tr.first := rfl

@[simp] theorem traceTake_singl (n : Nat) (s : S) :
    traceTake n (singl s : Trace S L) = .singleton s := by
  cases n <;> simp [traceTake]

@[simp] theorem traceTake_succ_cons (n : Nat) (s : S) (ℓ : L) (r : Trace S L) :
    traceTake (n + 1) (s -[ℓ]-> r) = .extend (traceTake n r) ℓ s := by
  simp [traceTake]

/-- Keep the steps `(s, ℓ)` of a finite trace satisfying `f` (Rocq `trace_filter`). -/
@[rocq_alias trillium.fairness.trace_filter]
def traceFilter (f : S → L → Prop) [∀ s l, Decidable (f s l)] :
    FiniteTrace S L → FiniteTrace S L
  | .singleton s => .singleton s
  | .extend tr ℓ s => if f s ℓ then .extend (traceFilter f tr) ℓ s else traceFilter f tr

/-- The number of labels (steps) of a finite trace (Rocq `count_labels`). -/
@[rocq_alias trillium.fairness.count_labels]
def countLabels : FiniteTrace S L → Nat
  | .singleton _ => 0
  | .extend ft' _ _ => countLabels ft' + 1

@[rocq_alias trillium.fairness.count_labels_sum]
theorem count_labels_sum (P : S → L → Prop) [∀ s l, Decidable (P s l)] (n m : Nat)
    (mtr mtr' : Trace S L) (Hafter : after n mtr = some mtr') :
    countLabels (traceFilter P (traceTake (n + m) mtr)) =
      countLabels (traceFilter P (traceTake n mtr)) +
        countLabels (traceFilter P (traceTake m mtr')) := by
  induction n generalizing mtr mtr' with
  | zero =>
    simp only [after_0_id, Option.some.injEq] at Hafter
    subst Hafter
    simp [traceFilter, countLabels]
  | succ n IHn =>
    cases mtr with
    | singl s => simp at Hafter
    | cons s ℓ r =>
      rw [after_succ_cons] at Hafter
      rw [show n + 1 + m = (n + m) + 1 by omega, traceTake_succ_cons, traceTake_succ_cons]
      simp only [traceFilter]
      split
      · simp only [countLabels]; rw [IHn r mtr' Hafter]; omega
      · exact IHn r mtr' Hafter

@[rocq_alias trillium.fairness.pred_at_neg]
theorem pred_at_neg (tr : Trace S L) (n : Nat) (P : S → Option L → Prop)
    (Hafter : (after n tr).isSome) :
    ¬ predAt tr n P ↔ predAt tr n (fun s l => ¬ P s l) := by
  obtain ⟨t, Ht⟩ := Option.isSome_iff_exists.1 Hafter
  rw [predAt_some Ht, predAt_some Ht]

@[rocq_alias trillium.fairness.infinite_trace_after']
theorem infinite_trace_after' (n : Nat) (tr : Trace S L) :
    infiniteTrace tr → ∃ tr', after n tr = some tr' ∧ infiniteTrace tr' := by
  intro Hinf
  have H := infinite_trace_after n tr Hinf
  revert H
  cases after n tr with
  | none => intro H; exact H.elim
  | some tr' => intro H; exact ⟨tr', rfl, H⟩

@[rocq_alias trillium.fairness.infinite_trace_after'']
theorem infinite_trace_after'' (n : Nat) (tr tr' : Trace S L) :
    after n tr = some tr' → infiniteTrace tr → infiniteTrace tr' := by
  intro Hafter Hinf m
  have := Hinf (n + m)
  rwa [after_sum', Hafter] at this

/-- Convert a finite trace to a trace (Rocq `finite_trace_to_trace`). As in Rocq, the order of
the states is reversed: the last state of `ft` becomes the first state of the result. -/
@[rocq_alias trillium.fairness.finite_trace_to_trace]
def finiteTraceToTrace : FiniteTrace S L → Trace S L
  | .singleton s => singl s
  | .extend tr ℓ s => s -[ℓ]-> finiteTraceToTrace tr

end finite

section temporal

variable {S T : Type _}

@[rocq_alias trillium.fairness.trace_now]
def traceNow (tr : Trace S T) (P : S → Option T → Prop) : Prop := predAt tr 0 P

@[rocq_alias trillium.fairness.trace_always]
def traceAlways (tr : Trace S T) (P : S → Option T → Prop) : Prop := ∀ n, predAt tr n P

@[rocq_alias trillium.fairness.trace_eventually]
def traceEventually (tr : Trace S T) (P : S → Option T → Prop) : Prop := ∃ n, predAt tr n P

@[rocq_alias trillium.fairness.trace_until]
def traceUntil (tr : Trace S T) (P Q : S → Option T → Prop) : Prop :=
  ∃ n, predAt tr n Q ∧ ∀ m, m < n → predAt tr m P

@[rocq_alias trillium.fairness.pred_at_after_is_Some]
theorem pred_at_after_is_Some (tr : Trace S T) (n : Nat) (P : S → Option T → Prop) :
    predAt tr n P → (after n tr).isSome := by
  unfold predAt
  split <;> simp_all

@[rocq_alias trillium.fairness.after_is_Some_le]
theorem after_is_Some_le (tr : Trace S T) (n m : Nat) :
    m ≤ n → (after n tr).isSome → (after m tr).isSome := by
  intro Hle H
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le Hle
  rw [after_sum'] at H
  revert H
  cases after m tr <;> simp

@[rocq_alias trillium.fairness.trace_eventually_until]
theorem trace_eventually_until (tr : Trace S T) (P : S → Option T → Prop) :
    traceEventually tr P → traceUntil tr (fun s l => ¬ P s l) P := by
  rintro ⟨n, Hn⟩
  induction n using Nat.strong_induction_on with
  | _ n IHn =>
    by_cases HP : ∀ m, m < n → predAt tr m (fun s l => ¬ P s l)
    · exact ⟨n, Hn, HP⟩
    · obtain ⟨n', HP⟩ := Classical.not_forall.mp HP
      obtain ⟨Hlt, HP⟩ := Classical.not_imp.mp HP
      have Hsome : (after n' tr).isSome :=
        after_is_Some_le tr n n' (Nat.le_of_lt Hlt) (pred_at_after_is_Some tr n P Hn)
      rw [pred_at_neg tr n' _ Hsome] at HP
      exact IHn n' Hlt (pred_at_impl _ _ (fun _ _ h => Classical.not_not.mp h) tr n' HP)

@[rocq_alias trillium.fairness.trace_eventually_cons]
theorem trace_eventually_cons (s : S) (l : T) (tr : Trace S T) (P : S → Option T → Prop) :
    traceEventually tr P → traceEventually (s -[l]-> tr) P :=
  fun ⟨n, HP⟩ => ⟨n + 1, by simpa using HP⟩

end temporal

@[rocq_alias trillium.fairness.to_trace_trfirst]
theorem to_trace_trfirst {S L : Type _} (s : S) (il : Stream'.Seq (L × S)) :
    (toTrace s il).first = s := rfl

end Trillium.Fairness
