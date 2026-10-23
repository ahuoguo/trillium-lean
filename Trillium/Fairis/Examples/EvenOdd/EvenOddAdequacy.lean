/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.Fairis.Examples.EvenOdd.EvenOdd
import Trillium.Fairis.Adequacy
import Trillium.Fairness.TraceUtils

/-!
# Adequacy of the even/odd example
Port of `fairis/examples/even_odd/even_odd_adequacy.v`.

Every fair model trace of the even/odd model starting in `0` visits every natural number and is
monotone (`evenodd_mdl_progresses`, `evenodd_mdl_is_mono`). These properties are transported to
the auxiliary trace (through destuttering) and to the execution trace (through the simulation
relation `ξ_evenodd` obtained from the Fairis adequacy theorem): in every maximal fair
execution of `start #l` the counter at `l` takes every value and never decreases
(`evenodd_ex_liveness`).

## Representation

* Rocq's paco proofs (`punfold`, `pinversion`, `pfold`) use the inversion lemmas of
  `TraceValid`, `TracesMatch` and `UptoStutter` (`TraceValid.inv`, `UptoStutter.unfold`, …).
* `l ≫= Ul` is `l.bind liveUl`; `ls_under ∘ ls_data` is `fun δ => δ.lsUnder`.
* stdpp's `Forall P l` is `∀ e ∈ l, P e`.
* `extrace_maximal` is the coinductive predicate `ExtraceMaximal`.
-/

set_option linter.unusedSectionVars false

namespace Trillium.Fairis.EvenOdd

open Iris Iris.BI Iris.Std Iris.ProofMode
open Trillium Trillium.HeapLang Trillium.Fairness Trillium.Language Trillium.Fairis Trace
open Iris.HeapLang (Loc HeapF)

/-! ## Helper lemmas for working with even and odd -/

attribute [rocq_alias trillium.fairis.even_odd_False] Trillium.Fairness.even_odd_False
attribute [rocq_alias trillium.fairis.even_not_odd] Trillium.Fairness.even_not_odd
attribute [rocq_alias trillium.fairis.odd_not_even] Trillium.Fairness.odd_not_even

/-! ## The model is finitely branching -/

/-- The candidate steps from `n` (Rocq `steppable`). -/
@[rocq_alias trillium.fairis.even_odd_adequacy.steppable]
def steppable (n : Nat) : List (Nat × Option EO) := do
  let n' ← [n + 1, n]
  let ℓ ← [some EO.ρEven, some EO.ρOdd]
  pure (n', ℓ)

#rocq_ignore trillium.fairis.even_odd_adequacy.proof_irrel_trans
  "`ProofIrrel` instance for the transition relation; Lean's `Prop` is proof-irrelevant"

@[rocq_alias trillium.fairis.even_odd_adequacy.model_finitary]
theorem model_finitary (s : theFairModel.fmstate) :
    Finite {p : theFairModel.fmstate × Option theFairModel.fmrole //
      theFairModel.fmtrans s p.2 p.1} := by
  refine in_list_finite (steppable s) ?_
  rintro ⟨n, w⟩ Htrans
  cases Htrans <;> simp [steppable]

/-! ## Any fair execution of the model visits all natural numbers -/

/-- Rocq `evenodd_mtrace`. -/
@[rocq_alias trillium.fairis.evenodd_mtrace]
abbrev EvenoddMtrace : Type := Mtrace theFairModel

/-- Rocq `evenodd_mdl_progress`. -/
@[rocq_alias trillium.fairis.evenodd_mdl_progress]
def evenoddMdlProgress (tr : EvenoddMtrace) : Prop :=
  ∀ i : Nat, ∃ n, predAt tr n (fun s _ => s = i)

/-- Rocq `evenodd_mdl_mono`. -/
@[rocq_alias trillium.fairis.evenodd_mdl_mono]
def evenoddMdlMono (tr : EvenoddMtrace) : Prop :=
  ∀ n, ∃ i : Nat, predAt tr n (fun s _ => s = i) ∧
    predAt tr (n + 1) (fun s _ => ∃ j : Nat, s = j ∧ i ≤ j)

/-- In an infinite trace, every position is followed by a step. -/
private theorem infiniteTrace_after_cons {S L : Type _} {tr : Trace S L} (Hinf : infiniteTrace tr)
    (n : Nat) : ∃ s ℓ r, after n tr = some (s -[ℓ]-> r) ∧ after (n + 1) tr = some r := by
  obtain ⟨t, Ht⟩ := Option.isSome_iff_exists.1 (Hinf n)
  have H1 := Hinf (n + 1)
  rw [after_sum', Ht] at H1
  cases t with
  | singl s => simp at H1
  | cons s ℓ r => exact ⟨s, ℓ, r, Ht, after_S_tr_cons _ _ _ _ _ Ht⟩

@[rocq_alias trillium.fairis.evenodd_mdl_always_live]
theorem evenodd_mdl_always_live (ρ : EO) (n : Nat) (mtr : EvenoddMtrace) :
    infiniteTrace mtr →
    predAt mtr n (fun (δ : theFairModel.fmstate) _ => roleEnabledModel ρ δ) := by
  intro Hinf
  obtain ⟨mtr', Hafter⟩ := Option.isSome_iff_exists.1 (Hinf n)
  rw [predAt_some Hafter]
  exact mem_eoLiveRoles ρ

@[rocq_alias trillium.fairis.evenodd_mdl_always_eventually_scheduled]
theorem evenodd_mdl_always_eventually_scheduled (ρ : EO) (mtr : EvenoddMtrace) :
    infiniteTrace mtr → fairModelTrace ρ mtr →
    ∀ n, ∃ m, predAt mtr (n + m) (fun _ ℓ => ℓ = some (some ρ)) := by
  intro Hinf Hfair n
  obtain ⟨m, Hm⟩ := Hfair n (evenodd_mdl_always_live ρ n mtr Hinf)
  refine ⟨m, pred_at_impl _ _ ?_ _ _ Hm⟩
  rintro s ol (Hne | ⟨ℓ, rfl, rfl⟩)
  · exact absurd (mem_eoLiveRoles ρ) Hne
  · rfl

/-- Common part of `evenodd_mdl_noprogress_Even` and `evenodd_mdl_noprogress_Odd`. -/
private theorem evenodd_mdl_noprogress (ρ : EO) (i n : Nat) (mtr : EvenoddMtrace)
    (Hstay : ∀ ℓ s', ℓ ≠ some ρ → EOTrans i ℓ s' → s' = i) :
    infiniteTrace mtr → MtraceValid mtr → mtr.first = i →
    (∀ m, m < n → predAt mtr m (fun _ l => l ≠ some (some ρ))) →
    predAt mtr n (fun s _ => s = i) := by
  intro Hinf Hvalid Hfirst Hne
  induction n with
  | zero => rw [predAt_some (after_0_id mtr)]; exact Hfirst
  | succ n IHn =>
    have IH := IHn (fun m Hm => Hne m (Nat.lt_succ_of_lt Hm))
    obtain ⟨s, ℓ, r, Hafter, Hafter'⟩ := infiniteTrace_after_cons Hinf n
    rw [predAt_some Hafter] at IH
    simp only [first_cons] at IH
    subst IH
    have Hneq : ℓ ≠ some ρ := by
      have := Hne n (Nat.lt_succ_self n)
      rw [predAt_some Hafter] at this
      simpa using this
    have Htrans := (trace_valid_cons_inv _ _ _ (trace_valid_after _ _ n Hafter Hvalid)).2
    rw [predAt_some Hafter']
    exact Hstay ℓ _ Hneq Htrans

@[rocq_alias trillium.fairis.evenodd_mdl_noprogress_Even]
theorem evenodd_mdl_noprogress_Even (i n : Nat) (mtr : EvenoddMtrace) :
    infiniteTrace mtr → MtraceValid mtr → mtr.first = i → Even i →
    (∀ m, m < n → predAt mtr m (fun _ l => l ≠ some (some EO.ρEven))) →
    predAt mtr n (fun s _ => s = i) := by
  intro Hinf Hvalid Hfirst Heven
  refine evenodd_mdl_noprogress EO.ρEven i n mtr ?_ Hinf Hvalid Hfirst
  intro ℓ s' Hne Htrans
  cases Htrans with
  | even_trans => exact absurd rfl Hne
  | even_fail Hodd => exact absurd Hodd (even_not_odd _ Heven)
  | odd_trans Hodd => exact absurd Hodd (even_not_odd _ Heven)
  | odd_fail => rfl

@[rocq_alias trillium.fairis.evenodd_mdl_noprogress_Odd]
theorem evenodd_mdl_noprogress_Odd (i n : Nat) (mtr : EvenoddMtrace) :
    infiniteTrace mtr → MtraceValid mtr → mtr.first = i → Odd i →
    (∀ m, m < n → predAt mtr m (fun _ l => l ≠ some (some EO.ρOdd))) →
    predAt mtr n (fun s _ => s = i) := by
  intro Hinf Hvalid Hfirst Hodd
  refine evenodd_mdl_noprogress EO.ρOdd i n mtr ?_ Hinf Hvalid Hfirst
  intro ℓ s' Hne Htrans
  cases Htrans with
  | even_trans Heven => exact absurd Hodd (even_not_odd _ Heven)
  | even_fail => rfl
  | odd_trans => exact absurd rfl Hne
  | odd_fail Heven => exact absurd Hodd (even_not_odd _ Heven)

/-- Common part of `evenodd_mdl_progresses_Even` and `evenodd_mdl_progresses_Odd`. -/
private theorem evenodd_mdl_progresses_role (ρ : EO) (i : Nat) (mtr : EvenoddMtrace)
    (Hnoprog : ∀ n, (∀ m, m < n → predAt mtr m (fun _ l => l ≠ some (some ρ))) →
      predAt mtr n (fun s _ => s = i))
    (Hstep : ∀ s', EOTrans i (some ρ) s' → s' = i + 1) :
    infiniteTrace mtr → MtraceValid mtr → (∀ ρ, fairModelTrace ρ mtr) →
    ∃ m, predAt mtr m (fun s _ => s = i + 1) := by
  intro Hinf Hvalid Hfair
  have Hsched := evenodd_mdl_always_eventually_scheduled ρ mtr Hinf (Hfair ρ) 0
  obtain ⟨m0, Hm0⟩ := Hsched
  rw [Nat.zero_add] at Hm0
  obtain ⟨m, Hsched, Hschedne⟩ := trace_eventually_until mtr _ ⟨m0, Hm0⟩
  obtain ⟨s, ℓ, r, Hafter, Hafter'⟩ := infiniteTrace_after_cons Hinf m
  rw [predAt_some Hafter] at Hsched
  simp only [label?_cons, Option.some.injEq] at Hsched
  subst Hsched
  have Hs := Hnoprog m Hschedne
  rw [predAt_some Hafter] at Hs
  simp only [first_cons] at Hs
  subst Hs
  have Htrans := (trace_valid_cons_inv _ _ _ (trace_valid_after _ _ m Hafter Hvalid)).2
  refine ⟨m + 1, ?_⟩
  rw [predAt_some Hafter']
  exact Hstep _ Htrans

@[rocq_alias trillium.fairis.evenodd_mdl_progresses_Even]
theorem evenodd_mdl_progresses_Even (i : Nat) (mtr : EvenoddMtrace) :
    infiniteTrace mtr → MtraceValid mtr → (∀ ρ, fairModelTrace ρ mtr) →
    mtr.first = i → Even i →
    ∃ m, predAt mtr m (fun s _ => s = i + 1) := by
  intro Hinf Hvalid Hfair Hfirst Heven
  refine evenodd_mdl_progresses_role EO.ρEven i mtr
    (fun n => evenodd_mdl_noprogress_Even i n mtr Hinf Hvalid Hfirst Heven) ?_ Hinf Hvalid Hfair
  intro s' Htrans
  cases Htrans with
  | even_trans => rfl
  | even_fail Hodd => exact absurd Hodd (even_not_odd _ Heven)

@[rocq_alias trillium.fairis.evenodd_mdl_progresses_Odd]
theorem evenodd_mdl_progresses_Odd (i : Nat) (mtr : EvenoddMtrace) :
    infiniteTrace mtr → MtraceValid mtr → (∀ ρ, fairModelTrace ρ mtr) →
    mtr.first = i → Odd i →
    ∃ m, predAt mtr m (fun s _ => s = i + 1) := by
  intro Hinf Hvalid Hfair Hfirst Hodd
  refine evenodd_mdl_progresses_role EO.ρOdd i mtr
    (fun n => evenodd_mdl_noprogress_Odd i n mtr Hinf Hvalid Hfirst Hodd) ?_ Hinf Hvalid Hfair
  intro s' Htrans
  cases Htrans with
  | odd_trans => rfl
  | odd_fail Heven => exact absurd Hodd (even_not_odd _ Heven)

@[rocq_alias trillium.fairis.evenodd_mdl_progresses]
theorem evenodd_mdl_progresses (mtr : EvenoddMtrace) :
    infiniteTrace mtr → MtraceValid mtr → (∀ ρ, fairModelTrace ρ mtr) →
    mtr.first = 0 → evenoddMdlProgress mtr := by
  intro Hinf Hvalid Hfair Hfirst i
  induction i with
  | zero => exact ⟨0, by rw [predAt_some (after_0_id mtr)]; exact Hfirst⟩
  | succ i IHi =>
    obtain ⟨n, Hpred⟩ := IHi
    cases Hafter : after n mtr with
    | none => exact absurd Hpred (predAt_none Hafter _)
    | some mtr' =>
      rw [predAt_some Hafter] at Hpred
      have Hinf' := infinite_trace_after'' n mtr mtr' Hafter Hinf
      have Hvalid' := trace_valid_after _ _ n Hafter Hvalid
      have Hfair' : ∀ ρ, fairModelTrace ρ mtr' :=
        fun ρ => fair_by_after _ _ ρ mtr mtr' n Hafter (Hfair ρ)
      obtain ⟨m, Hpred'⟩ : ∃ m, predAt mtr' m (fun s _ => s = i + 1) := by
        rcases Nat.even_or_odd i with Heven | Hodd
        · exact evenodd_mdl_progresses_Even i mtr' Hinf' Hvalid' Hfair' Hpred Heven
        · exact evenodd_mdl_progresses_Odd i mtr' Hinf' Hvalid' Hfair' Hpred Hodd
      refine ⟨n + m, ?_⟩
      rw [pred_at_sum, Hafter]
      exact Hpred'

@[rocq_alias trillium.fairis.evenodd_mdl_is_mono]
theorem evenodd_mdl_is_mono (mtr : EvenoddMtrace) :
    infiniteTrace mtr → MtraceValid mtr → (∀ ρ, fairModelTrace ρ mtr) →
    mtr.first = 0 → evenoddMdlMono mtr := by
  intro Hinf Hvalid _Hfair _Hfirst n
  obtain ⟨s, ℓ, r, Hafter, Hafter'⟩ := infiniteTrace_after_cons Hinf n
  refine ⟨s, by rw [predAt_some Hafter]; rfl, ?_⟩
  rw [predAt_some Hafter']
  have Htrans := (trace_valid_cons_inv _ _ _ (trace_valid_after _ _ n Hafter Hvalid)).2
  generalize r.first = s' at Htrans ⊢
  cases Htrans with
  | even_trans => exact ⟨s + 1, rfl, Nat.le_succ s⟩
  | even_fail => exact ⟨s, rfl, Nat.le_refl s⟩
  | odd_trans => exact ⟨s + 1, rfl, Nat.le_succ s⟩
  | odd_fail => exact ⟨s, rfl, Nat.le_refl s⟩

/-! ## Fair progress is preserved through the auxiliary trace -/

/-- Rocq `evenodd_aux_progress`. -/
@[rocq_alias trillium.fairis.evenodd_aux_progress]
def evenoddAuxProgress (auxtr : Auxtrace theModel) : Prop :=
  ∀ i : Nat, ∃ n, predAt auxtr n (fun s l =>
    (fun (s' : theFairModel.fmstate) (_ : Option (Option EO)) => s' = i) s.lsUnder (l.bind liveUl))

@[rocq_alias trillium.fairis.trace_eventually_stutter_preserves]
theorem trace_eventually_stutter_preserves {St S' L L' : Type _} (Us : St → S')
    (Ul : L → Option L') (tr1 : Trace St L) (tr2 : Trace S' L') (P : S' → Option L' → Prop) :
    UptoStutter Us Ul tr1 tr2 → traceEventually tr2 P →
    traceEventually tr1 (fun s l => P (Us s) (l.bind Ul)) := by
  rintro Hstutter ⟨n, Heventually⟩
  induction n generalizing tr1 tr2 with
  | zero =>
    have Hind := Hstutter.unfold
    clear Hstutter
    induction Hind with
    | singleton s =>
      refine ⟨0, ?_⟩
      simpa using Heventually
    | stutter btr str s ℓ _ _ _ _ IH =>
      obtain ⟨n, Hn⟩ := IH Heventually
      exact ⟨n + 1, by simpa only [pred_at_S] using Hn⟩
    | step btr str s ℓ s' ℓ' Hs HUl _ =>
      refine ⟨0, ?_⟩
      rw [pred_at_0] at Heventually ⊢
      rw [Option.bind_some, HUl, Hs]
      exact Heventually
  | succ n IHn =>
    have Hind := Hstutter.unfold
    clear Hstutter
    induction Hind with
    | singleton s => simp [predAt] at Heventually
    | stutter btr str s ℓ _ _ _ _ IH =>
      obtain ⟨n', Hn⟩ := IH Heventually
      exact ⟨n' + 1, by simpa only [pred_at_S] using Hn⟩
    | step btr str s ℓ s' ℓ' Hs HUl Hrest =>
      rw [pred_at_S] at Heventually
      exact trace_eventually_cons _ _ _ _ (IHn btr str Hrest Heventually)

@[rocq_alias trillium.fairis.evenodd_mtr_aux_progress_preserved]
theorem evenodd_mtr_aux_progress_preserved (mtr : Mtrace theFairModel)
    (auxtr : Auxtrace theModel) :
    UptoStutterAuxtr theModel auxtr mtr → evenoddMdlProgress mtr → evenoddAuxProgress auxtr := by
  intro Hstutter Hmtr n
  exact trace_eventually_stutter_preserves _ _ auxtr mtr (fun s' _ => s' = n) Hstutter (Hmtr n)

/-- Rocq `evenodd_aux_mono`. -/
@[rocq_alias trillium.fairis.evenodd_aux_mono]
def evenoddAuxMono (auxtr : Auxtrace theModel) : Prop :=
  ∀ n, ∃ i : Nat,
    predAt auxtr n (fun s l =>
      (fun (s' : theFairModel.fmstate) (_ : Option (Option EO)) => s' = i)
        s.lsUnder (l.bind liveUl)) ∧
    predAt auxtr (n + 1) (fun s l =>
      (fun (s' : theFairModel.fmstate) (_ : Option (Option EO)) => ∃ j : Nat, s' = j ∧ i ≤ j)
        s.lsUnder (l.bind liveUl))

@[rocq_alias trillium.fairis.evenodd_mtr_aux_mono_preserved]
theorem evenodd_mtr_aux_mono_preserved (mtr : Mtrace theFairModel) (auxtr : Auxtrace theModel) :
    UptoStutterAuxtr theModel auxtr mtr → evenoddMdlMono mtr → evenoddAuxMono auxtr := by
  intro Hstutter Hmtr n
  induction n generalizing auxtr mtr with
  | zero =>
    have Hind := Hstutter.unfold
    clear Hstutter
    induction Hind with
    | singleton s =>
      obtain ⟨_, _, H⟩ := Hmtr 0
      simp [predAt] at H
    | stutter btr str s ℓ _ Hfirst _ _ IH =>
      obtain ⟨i, Hpred, -⟩ := IH Hmtr
      rw [predAt_some (after_0_id btr)] at Hpred
      refine ⟨i, ?_, ?_⟩
      · rw [pred_at_0]; exact Hfirst.trans Hpred
      · rw [pred_at_S, predAt_some (after_0_id btr)]; exact ⟨i, Hpred, Nat.le_refl i⟩
    | step btr str s ℓ s' ℓ' Hs _ Hrest =>
      obtain ⟨i, Hpred1, Hpred2⟩ := Hmtr 0
      rw [pred_at_0] at Hpred1
      rw [pred_at_S, predAt_some (after_0_id str)] at Hpred2
      refine ⟨i, ?_, ?_⟩
      · rw [pred_at_0]; exact Hs.trans Hpred1
      · rw [pred_at_S, predAt_some (after_0_id btr)]
        rw [UptoStutterInd.first Hrest.unfold] at Hpred2
        exact Hpred2
  | succ n IHn =>
    cases auxtr using Trace.casesOn' with
    | singl s =>
      obtain ⟨_, _, H⟩ := Hmtr 0
      rw [Hstutter.unfold.singl_inv] at H
      simp [predAt] at H
    | cons s ℓ btr =>
      rcases Hstutter.unfold.cons_inv with ⟨_, _, _, Hind⟩ | ⟨ℓ', str', rfl, _, Hrest⟩
      · obtain ⟨i, H1, H2⟩ := IHn mtr btr (UptoStutter.fold Hind) Hmtr
        exact ⟨i, by rw [pred_at_S]; exact H1, by rw [pred_at_S]; exact H2⟩
      · have Hmtr' : evenoddMdlMono str' := by
          intro m
          obtain ⟨i, H1, H2⟩ := Hmtr (m + 1)
          rw [pred_at_S] at H1 H2
          exact ⟨i, H1, H2⟩
        obtain ⟨i, H1, H2⟩ := IHn str' btr Hrest Hmtr'
        exact ⟨i, by rw [pred_at_S]; exact H1, by rw [pred_at_S]; exact H2⟩

/-! ## Progress is preserved between the auxiliary and the execution trace -/

/-- Rocq `evenodd_ex_progress`. -/
@[rocq_alias trillium.fairis.evenodd_ex_progress]
def evenoddExProgress (l : Loc) (extr : HeapLangExtrace) : Prop :=
  ∀ i : Nat, ∃ n, predAt extr n (fun s _ => s.2.heap[l]? = some (.lit (.int i)))

/-- Rocq `evenodd_ex_mono`. -/
@[rocq_alias trillium.fairis.evenodd_ex_mono]
def evenoddExMono (l : Loc) (extr : HeapLangExtrace) : Prop :=
  ∀ n, ∃ i : Nat,
    predAt extr n (fun s _ => s.2.heap[l]? = some (.lit (.int i))) ∧
    predAt extr (n + 1) (fun s _ => ∃ j : Nat, s.2.heap[l]? = some (.lit (.int j)) ∧ i ≤ j)

/-- Rocq `ξ_evenodd_model_match`. -/
@[rocq_alias trillium.fairis.ξ_evenodd_model_match]
def ξEvenoddModelMatch (l : Loc) (c : List Expr × State) (δ : theFairModel.fmstate) : Prop :=
  ∃ N : Nat, c.2.heap[l]? = some (.lit (.int N)) ∧ δ = N

/-- Rocq `ξ_evenodd_no_val_steps`. -/
@[rocq_alias trillium.fairis.ξ_evenodd_no_val_steps]
def ξEvenoddNoValSteps (c : List Expr × State) : Prop :=
  ((∀ e ∈ c.1, (toVal e).isSome) → False) ∧ ∀ e ∈ c.1, NotStuck e c.2

/-- Rocq `ξ_evenodd`. -/
@[rocq_alias trillium.fairis.ξ_evenodd]
def ξEvenodd (l : Loc) (c : List Expr × State) (δ : theFairModel.fmstate) : Prop :=
  ξEvenoddNoValSteps c ∧ ξEvenoddModelMatch l c δ

/-- Rocq `ξ_evenodd_trace`. -/
@[rocq_alias trillium.fairis.ξ_evenodd_trace]
def ξEvenoddTrace (l : Loc) (extr : ExecutionTrace Expr)
    (auxtr : FiniteTrace theFairModel.fmstate (Option EO)) : Prop :=
  ξEvenodd l extr.last auxtr.last

@[rocq_alias trillium.fairis.evenodd_aux_ex_progress_preserved]
theorem evenodd_aux_ex_progress_preserved (l : Loc) (extr : HeapLangExtrace)
    (auxtr : Auxtrace theModel) :
    TracesMatch labelsMatch (fun c (δ : LiveState BaseLocale theFairModel) => ξEvenodd l c δ.lsUnder)
      (LocaleStep (Expr := Expr)) theModel.lmLsTrans extr auxtr →
    evenoddAuxProgress auxtr → evenoddExProgress l extr := by
  intro Hξ Hauxtr n
  obtain ⟨m, Hauxtr⟩ := Hauxtr n
  cases Heqn : after m auxtr with
  | none => exact absurd Hauxtr (predAt_none Heqn _)
  | some auxtr' =>
    obtain ⟨extr', Hafter', Hextr'⟩ := traces_match_after extr auxtr m auxtr' Hξ Heqn
    refine ⟨m, ?_⟩
    rw [predAt_some Hafter']
    rw [predAt_some Heqn] at Hauxtr
    obtain ⟨-, N, HN, Hδ⟩ := traces_match_first _ _ Hextr'
    have : N = n := Hδ.symm.trans Hauxtr
    subst this
    exact HN

@[rocq_alias trillium.fairis.evenodd_aux_ex_mono_preserved]
theorem evenodd_aux_ex_mono_preserved (l : Loc) (extr : HeapLangExtrace)
    (auxtr : Auxtrace theModel) :
    TracesMatch labelsMatch (fun c (δ : LiveState BaseLocale theFairModel) => ξEvenodd l c δ.lsUnder)
      (LocaleStep (Expr := Expr)) theModel.lmLsTrans extr auxtr →
    evenoddAuxMono auxtr → evenoddExMono l extr := by
  intro Hξ Hauxtr n
  obtain ⟨i, Hauxtr1, Hauxtr2⟩ := Hauxtr n
  refine ⟨i, ?_, ?_⟩
  · cases Heqn : after n auxtr with
    | none => exact absurd Hauxtr1 (predAt_none Heqn _)
    | some auxtr' =>
      obtain ⟨extr', Hafter', Hextr'⟩ := traces_match_after extr auxtr n auxtr' Hξ Heqn
      rw [predAt_some Hafter']
      rw [predAt_some Heqn] at Hauxtr1
      obtain ⟨-, N, HN, Hδ⟩ := traces_match_first _ _ Hextr'
      have : N = i := Hδ.symm.trans Hauxtr1
      subst this
      exact HN
  · cases Heqn : after (n + 1) auxtr with
    | none => exact absurd Hauxtr2 (predAt_none Heqn _)
    | some auxtr' =>
      obtain ⟨extr', Hafter', Hextr'⟩ := traces_match_after extr auxtr (n + 1) auxtr' Hξ Heqn
      rw [predAt_some Hafter']
      rw [predAt_some Heqn] at Hauxtr2
      obtain ⟨j, Hj, Hle⟩ := Hauxtr2
      obtain ⟨-, N, HN, Hδ⟩ := traces_match_first _ _ Hextr'
      refine ⟨N, HN, ?_⟩
      have : N = j := Hδ.symm.trans Hj
      exact this ▸ Hle

/-- Rocq `the_model_mstate_countable` (an `EqDecision` instance, classical in Lean). -/
@[rocq_alias trillium.fairis.the_model_mstate_countable]
noncomputable instance the_model_mstate_countable : DecidableEq theModel.toModel.mstate :=
  Classical.decEq _

/-- Rocq `the_model_mlabel_countable` (an `EqDecision` instance). -/
@[rocq_alias trillium.fairis.the_model_mlabel_countable]
instance the_model_mlabel_countable : DecidableEq theModel.toModel.mlabel :=
  inferInstanceAs (DecidableEq (FairLabel EO BaseLocale))

/-! ## The program refines the model up to `ξ_evenodd` -/

/-- The initial state of the program: the counter at `l` is `0`. -/
abbrev initState (l : Loc) : State := ⟨GMap.singleton l (.lit (.int 0)), ∅⟩

/-- The program `start #l`. -/
abbrev startExpr (l : Loc) : Expr := tl(v(&start) #(.loc l))

private theorem mapUnderlyingTrace_last (aux : AuxiliaryTrace theModel.toModel) :
    (mapUnderlyingTrace aux).last = aux.last.lsUnder := by
  cases aux <;> rfl

theorem toGMap_eoLiveRoles :
    GSet.toGMap (theModel.lmFl 0) (theFairModel.liveRoles 0) =
      (GMap.singleton (K := theFairModel.fmrole) EO.ρOdd 61).insert EO.ρEven 61 := by
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  cases k <;> simp [GMap.getElem?_insert_ite, GMap.getElem?_singleton, mem_eoLiveRoles]

/-- Rocq `evenodd_sim`. Rocq instantiates the ghost state with the concrete `evenoddΣ`; here (as
for iris-lean's `heap_adequacy`) the statement is for any `GF` with
`[HeapGpreS theModel GF] [EvenoddPreG GF]`. -/
@[rocq_alias trillium.fairis.evenodd_sim]
theorem evenodd_sim (GF : BundledGFunctors) [HeapGpreS theModel GF] [EvenoddPreG GF] (l : Loc) :
    ContinuedSimulation (simRelWithUser theModel (ξEvenoddTrace l))
      ({tr[([startExpr l], initState l)]} : ExecutionTrace Expr)
      ({tr[initialLs theModel 0 0]} : AuxiliaryTrace theModel.toModel) := by
  refine strong_simulation_adequacy GF theModel .NotStuck _ _ 0 ∅ (ξEvenoddTrace l) ?_ ?_ ?_
  · apply rel_finitary_sim_rel_with_user_sim_rel
    exact valid_state_evolution_finitary_fairness_simple model_finitary (liveRel theModel)
  · intro h
    have : EO.ρEven ∈ theFairModel.liveRoles 0 := mem_eoLiveRoles _
    rw [h] at this
    exact LawfulSet.mem_empty this
  · intro _
    iintro !> Hσ Hs Hr Hf
    imod iOwn_alloc (F := constOF EOAuthR)
      ((ExclAuth.auth (⟨0⟩ : DiscreteO Nat)) • ExclAuth.frag (⟨0⟩ : DiscreteO Nat)) ExclAuth.valid
      with ⟨%γe, He⟩
    icases iOwn_op.1 $$ He with ⟨Hea, Hef⟩
    imod iOwn_alloc (F := constOF EOAuthR)
      ((ExclAuth.auth (⟨1⟩ : DiscreteO Nat)) • ExclAuth.frag (⟨1⟩ : DiscreteO Nat)) ExclAuth.valid
      with ⟨%γo, Ho⟩
    icases iOwn_op.1 $$ Ho with ⟨Hoa, Hof⟩
    let _ : EvenoddG GF := ⟨γe, γo, inferInstance⟩
    have Hfr : (∅ : GSet EO) \ theFairModel.liveRoles 0 = ∅ := by
      apply LawfulSet.ext
      intro x
      simp only [LawfulSet.mem_diff]
      exact ⟨fun h => absurd h.1 LawfulSet.mem_empty, fun h => absurd h LawfulSet.mem_empty⟩
    have HrEq : fragFreeRolesAre (GF := GF) (∅ \ theFairModel.liveRoles 0) ⊢
        fragFreeRolesAre (GF := GF) ∅ := by rw [Hfr]
    ihave Hr := HrEq $$ Hr
    imod inv_alloc Ns ⊤ (evenoddInvInner (GF := GF) l) $$ [Hea Hoa Hσ Hs Hr] with #Hinv
    · inext
      iunfold evenoddInvInner
      iexists 0
      have Hsing := BigSepM.bigSepM_singleton (M := HeapF) (PROP := IProp GF)
        (Φ := fun l v => iprop(l ↦ v)) (i := l) (x := Val.lit (.int 0))
      have Heq : (PartialMap.singleton l (Val.lit (.int 0)) : HeapF Val) =
          GMap.singleton l (Val.lit (.int 0)) := rfl
      rw [Heq] at Hsing
      ihave Hl := Hsing.1 $$ Hσ
      have Hev : Even 0 := ⟨0, rfl⟩
      isimp only [Hev, ite_true, authEvenAt, authOddAt, Nat.cast_zero, Nat.zero_add]
      iframe
    imodintro
    isplitl [Hf Hef Hof]
    · ihave Hf : hasFuels (GF := GF) 0
          ((GMap.singleton (K := theFairModel.fmrole) EO.ρOdd 61).insert EO.ρEven 61) $$ [Hf]
      · rw [← toGMap_eoLiveRoles]
        iexact Hf
      have Hspec := start_spec (GF := GF) 0 l 0 1 61 (by omega)
      isimp only [localeOf_eq, List.length_nil]
      iapply Hspec $$ [Hf Hef Hof]
      · isimp only [evenoddInv, evenAt, oddAt]
        iframe
        iexact Hinv
      · inext
        iintro H
        iexact H
    · iunfold relAlwaysHolds
      iintro %ex %atr %c %Hvalid %Hex %Hatr %Hends %Hξ %Hstuck %Hequiv Hσ Hposts
      obtain rfl : c = ex.last := (FiniteTrace.endsIn_iff.1 Hends).symm
      imod inv_acc (E := ⊤) (N := Ns) (P := evenoddInvInner (GF := GF) l)
        CoPset.subseteq_top $$ Hinv with ⟨HI, -⟩
      iunfold evenoddInvInner at HI
      icases HI with ⟨%M, >HFR, >Hmod, >Hn, -⟩
      rw [heapG_stateInterp_eq]
      icases Hσ with ⟨%Hvse, Hh, Hm⟩
      ihave %Hlookup : ⌜ex.last.2.heap[l]? = some (Val.lit (.int M))⌝ $$ [Hh Hn]
      · ihave >%H := genHeap_valid' ex.last.2 l _ _ $$ [$Hh $Hn]
        ipureintro
        exact H
      ihave %Hlast := model_agree' (GF := GF) atr.last (M : theFairModel.fmstate) ex.last.1 $$
        Hm Hmod
      ihave %Hnv : ⌜(∀ e ∈ ex.last.1, (toVal e).isSome) → False⌝ $$ [Hm Hposts]
      · by_cases hP : ∀ e ∈ ex.last.1, (toVal e).isSome
        · iunfold modelStateInterp at Hm
          icases Hm with ⟨%fm, -, %Hfmdead, %Hfmtp, -, Hfm⟩
          obtain ⟨ζ, fs, Hζ, Hρ⟩ := Hfmdead EO.ρEven (mem_eoLiveRoles _)
          have hζ : ζ ∈ localesOfList ex.last.1 := by
            by_contra h
            rw [Hfmtp ζ h] at Hζ
            cases Hζ
          rw [localesOfList_eq_indexes] at hζ
          have hlt : ζ < ex.last.1.length := by
            simp only [indexes, List.mem_mapIdx] at hζ
            obtain ⟨i, hi, rfl⟩ := hζ
            exact hi
          have He : ex.last.1[ζ]? = some ex.last.1[ζ] := List.getElem?_eq_getElem hlt
          obtain ⟨v, Hv⟩ := Option.isSome_iff_exists.1 (hP _ (List.getElem_mem hlt))
          ihave Hem : hasFuels (GF := GF) ζ ∅ $$ [Hposts]
          · iclear Hinv
            exact posts_of_empty_mapping (M := theModel.toModel) (GF := GF) (startExpr l) _ v ζ
              ex.last.1 He (by simpa [toVal_eq] using Hv)
          ihave %Hagree := has_fuels_agree $$ Hfm Hem
          ipureintro
          intro _
          rw [Hagree] at Hζ
          cases Hζ
          simp [GMap.mem_dom] at Hρ
        · ipureintro
          exact fun h => hP h
      iapply fupd_mask_intro_discard LawfulSet.empty_subset
      ipureintro
      refine ⟨⟨Hnv, fun e he => Hstuck e rfl he⟩, M, Hlookup, ?_⟩
      rw [mapUnderlyingTrace_last, Hlast]

/-! ## Maximal execution traces -/

section maximal

variable {Expr' Val' Ectx' State' Locale' : Type _} [Language Expr' Val' Ectx' State' Locale']

/-- An execution trace is maximal: every step is a `LocaleStep`, and it only ends in a
configuration that cannot step (Rocq `extrace_maximal`). -/
@[rocq_alias trillium.fairis.extrace_maximal]
coinductive ExtraceMaximal : Extrace Expr' → Prop where
  | singleton (c : List Expr' × State') :
      (∀ oζ c', ¬ LocaleStep c oζ c') → ExtraceMaximal (Trace.singl c)
  | cons (c : List Expr' × State') (oζ : Option Locale') (tr : Extrace Expr') :
      LocaleStep c oζ tr.first → ExtraceMaximal tr → ExtraceMaximal (Trace.cons c oζ tr)

/-- Inversion for `ExtraceMaximal`. -/
theorem ExtraceMaximal.inv {tr : Extrace Expr'} (h : ExtraceMaximal tr) :
    (∃ c, (∀ oζ c', ¬ LocaleStep c oζ c') ∧ tr = Trace.singl c) ∨
      ∃ c oζ r, LocaleStep c oζ r.first ∧ ExtraceMaximal r ∧ tr = Trace.cons c oζ r := by
  cases h with
  | singleton c h => exact .inl ⟨c, h, rfl⟩
  | cons c oζ r h1 h2 => exact .inr ⟨c, oζ, r, h1, h2, rfl⟩

@[rocq_alias trillium.fairis.extrace_maximal_valid]
theorem extrace_maximal_valid (extr : Extrace Expr') :
    ExtraceMaximal extr → ExtraceValid extr := by
  intro Hmaximal
  refine ExtraceValid.coinduct ExtraceMaximal ?_ extr Hmaximal
  intro tr h
  rcases h.inv with ⟨c, -, rfl⟩ | ⟨c, oζ, r, h1, h2, rfl⟩
  · exact .inl ⟨c, rfl⟩
  · exact .inr ⟨c, oζ, r, h1, h2, rfl⟩

@[rocq_alias trillium.fairis.extrace_maximal_after]
theorem extrace_maximal_after (n : Nat) (extr extr' : Extrace Expr') :
    ExtraceMaximal extr → after n extr = some extr' → ExtraceMaximal extr' := by
  induction n generalizing extr with
  | zero =>
    intro Hmax Hafter
    simp only [after_0_id, Option.some.injEq] at Hafter
    exact Hafter ▸ Hmax
  | succ n IHn =>
    intro Hmax Hafter
    rcases Hmax.inv with ⟨c, -, rfl⟩ | ⟨c, oζ, r, -, Hr, rfl⟩
    · simp at Hafter
    · rw [after_succ_cons] at Hafter
      exact IHn r Hr Hafter

end maximal

@[rocq_alias trillium.fairis.infinite_trace_no_val_steps]
theorem infinite_trace_no_val_steps (extr : HeapLangExtrace) (auxtr : Auxtrace theModel) :
    ExtraceMaximal extr →
    TracesMatch labelsMatch (fun c (_ : LiveState BaseLocale theFairModel) => ξEvenoddNoValSteps c)
      (LocaleStep (Expr := Expr)) theModel.lmLsTrans extr auxtr →
    infiniteTrace extr := by
  intro Hmaximal Hmatch n
  induction n with
  | zero => rfl
  | succ n IHn =>
    obtain ⟨extr', Hafter⟩ := Option.isSome_iff_exists.1 IHn
    obtain ⟨auxtr', -, Hmatch'⟩ := traces_match_after' extr auxtr n extr' Hmatch Hafter
    obtain ⟨Hξ1, Hξ2⟩ := traces_match_first _ _ Hmatch'
    have Hmax' := extrace_maximal_after n extr extr' Hmaximal Hafter
    rcases Hmax'.inv with ⟨c, Hnstep, rfl⟩ | ⟨c, oζ, r, -, -, rfl⟩
    · exfalso
      simp only [first_singl] at Hξ1 Hξ2
      obtain ⟨e, He, Hval⟩ : ∃ e ∈ c.1, toVal e = none := by
        by_contra H
        exact Hξ1 fun e he => Option.isSome_iff_ne_none.2 fun h => H ⟨e, he, h⟩
      rcases Hξ2 e He with Hsome | ⟨e', σ', efs, Hred⟩
      · rw [Hval] at Hsome; cases Hsome
      · obtain ⟨es1, es2, Hes⟩ := List.mem_iff_append.1 He
        obtain ⟨tp, σ⟩ := c
        simp only at Hes
        subst Hes
        exact Hnstep _ _ (LocaleStep.atomic es1 es2 Hred)
    · rw [after_S_tr_cons _ _ _ _ _ Hafter]
      rfl

/-! ## The execution trace satisfies the liveness properties -/

@[rocq_alias trillium.fairis.evenodd_ex_liveness]
theorem evenodd_ex_liveness (GF : BundledGFunctors) [HeapGpreS theModel GF] [EvenoddPreG GF]
    (l : Loc) (extr : HeapLangExtrace) :
    ExtraceMaximal extr → (∀ tid, fairEx tid extr) →
    extr.first = ([startExpr l], initState l) →
    evenoddExProgress l extr ∧ evenoddExMono l extr := by
  intro Hmaximal Hfair Hfirst
  have Hvalid := extrace_maximal_valid extr Hmaximal
  have Hsim := evenodd_sim GF l
  rw [← Hfirst] at Hsim
  have Hiatr := produced_inf_aux_trace_valid_inf (Hst := ValidSystemTrace.singleton _ _)
    (Hcsm := Hsim) (iex := fromTrace extr)
    (Hvex := from_trace_preserves_validity_singleton extr Hvalid)
  set auxtr : Auxtrace theModel := toTrace (initialLs theModel 0 0)
    (produceInfAuxTrace _ _ _ Hsim (fromTrace extr)
      (from_trace_preserves_validity_singleton extr Hvalid)) with Hauxtr
  have Hmatch_strong : TracesMatch labelsMatch
      (fun σ (δ : LiveState BaseLocale theFairModel) => liveTids σ δ ∧ ξEvenodd l σ δ.lsUnder)
      (LocaleStep (Expr := Expr)) theModel.lmLsTrans extr auxtr := by
    refine valid_inf_system_trace_implies_traces_match_strong theModel _
      (fun σ (δ : LiveState BaseLocale theFairModel) => ξEvenodd l σ δ.lsUnder) _ _ _ _ extr auxtr
      (fun _ _ h => h.rel.1.2) (fun _ _ h => h.rel.1.1) ?_ (from_trace_spec _ extr rfl)
      (to_trace_spec _ _) Hiatr
    intro ex atr h
    have := h.rel.2
    unfold ξEvenoddTrace at this
    rw [mapUnderlyingTrace_last] at this
    exact this
  have Hmatch : ExauxTracesMatch Expr theModel extr auxtr :=
    traces_match_impl _ _ _ _ _ _ _ _ (fun _ _ h => h) (fun _ _ h => h.1) Hmatch_strong
  obtain ⟨mtr, Hupto⟩ := can_destutter_auxtr auxtr (exaux_preserves_validity extr auxtr Hmatch)
  have Hinf : infiniteTrace extr :=
    infinite_trace_no_val_steps extr auxtr Hmaximal
      (traces_match_impl _ _ _ _ _ _ _ _ (fun _ _ h => h) (fun _ _ h => h.2.1) Hmatch_strong)
  have Hfairaux := fairness_preserved extr auxtr Hinf Hmatch Hfair
  have Hfair'' := upto_stutter_fairness auxtr mtr Hupto Hfairaux
  have Hinf'' : infiniteTrace mtr :=
    upto_stutter_infinite_trace auxtr mtr Hupto
      (traces_match_infinite_trace _ _ _ _ _ _ Hmatch Hinf)
  have Hvalid'' : MtraceValid mtr :=
    upto_preserves_validity auxtr mtr Hupto (exaux_preserves_validity extr auxtr Hmatch)
  have Hfirst'' : mtr.first = 0 := by
    rw [upto_stutter_trfirst _ _ Hupto]
    rfl
  have HmatchU : TracesMatch labelsMatch
      (fun c (δ : LiveState BaseLocale theFairModel) => ξEvenodd l c δ.lsUnder)
      (LocaleStep (Expr := Expr)) theModel.lmLsTrans extr auxtr :=
    traces_match_impl _ _ _ _ _ _ _ _ (fun _ _ h => h) (fun _ _ h => h.2) Hmatch_strong
  refine ⟨?_, ?_⟩
  · exact evenodd_aux_ex_progress_preserved l extr auxtr HmatchU
      (evenodd_mtr_aux_progress_preserved mtr auxtr Hupto
        (evenodd_mdl_progresses mtr Hinf'' Hvalid'' Hfair'' Hfirst''))
  · exact evenodd_aux_ex_mono_preserved l extr auxtr HmatchU
      (evenodd_mtr_aux_mono_preserved mtr auxtr Hupto
        (evenodd_mdl_is_mono mtr Hinf'' Hvalid'' Hfair'' Hfirst''))

end Trillium.Fairis.EvenOdd
