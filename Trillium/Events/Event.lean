/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.ProgramLogic.Traces
import Trillium.ProgramLogic.EctxLanguage

/-!
# Events
Port of `trillium/events/event.v`.

An `Event` is a predicate on head steps `e1, σ1 ⇝ e2, σ2`; an `EventObservation` records one
such step. `TraceHasEvents EV ex eobs` relates an execution trace to the list of `EV`-events
observed along it; it is functional on valid executions (`traceHasEvents_functional`), so
`eventsOfTrace EV ex` is defined with the axiom of choice (Rocq `epsilon` ↦ `Classical.choose`).

Representation: the Rocq record `EventObservation Λ` only depends on the expression and state
types of `Λ`, so it is `EventObservation Expr State`; `event_obs Λ` is `EventObs Expr`
(a `List`). stdpp's `Forall P l` is `∀ x ∈ l, P x`, `ectx_fill`/`ectx_emp`/`ectx_comp` are
`fill`/`EvContextOps.empty`/`EvContextOps.comp`, `is_Some (to_val e)` is `(toVal e).isSome`, and
the thread-pool `tp1 ++ fill K e :: tp2 ++ efs` is written `tp1 ++ fill K e :: (tp2 ++ efs)`
(as in `Language.LocaleStep`).
-/

namespace Trillium

open FiniteTrace Language
open Iris.ProgramLogic (ToVal EvContext EvContextOps)

/-- An event: a predicate on steps, only triggered by head steps. The predicate is the coercion
to a function (Rocq `is_triggered :>`). -/
@[rocq_alias trillium.Event]
structure Event (Expr : Type _) {Val Ectx State Locale : Type _}
    [Language Expr Val Ectx State Locale] where
  isTriggered : Expr → State → Expr → State → Prop
  /-- Events are only triggered on non-values. -/
  isTriggered_not_val : ∀ e1 σ1 e2 σ2, isTriggered e1 σ1 e2 σ2 → toVal e1 = none
  /-- Events are only triggered on head steps. -/
  isTriggered_ectx_free : ∀ e1 σ1 e2 σ2, isTriggered e1 σ1 e2 σ2 →
    ∀ (K : Ectx) e1', e1 = fill K e1' → (toVal e1').isSome ∨ K = EvContextOps.empty
  /-- Events are not triggered by stuttering steps. -/
  isTriggered_not_stuttering : ∀ e1 σ1 e2 σ2, isTriggered e1 σ1 e2 σ2 → e1 ≠ e2

variable {Expr Val Ectx State Locale : Type _}

instance [Language Expr Val Ectx State Locale] :
    CoeFun (Event Expr) (fun _ => Expr → State → Expr → State → Prop) :=
  ⟨Event.isTriggered⟩

/-- An observed event: the step `preExpr, preState ⇝ postExpr, postState`. -/
@[rocq_alias trillium.EventObservation]
structure EventObservation (Expr State : Type _) where
  preExpr : Expr
  preState : State
  postExpr : Expr
  postState : State

section

variable [Language Expr Val Ectx State Locale]

@[rocq_alias trillium.validEventObservation]
def ValidEventObservation (EV : Event Expr) (eo : EventObservation Expr State) : Prop :=
  EV eo.preExpr eo.preState eo.postExpr eo.postState

/-- Lists of observed events (Rocq `event_obs Λ`). -/
@[rocq_alias trillium.event_obs]
abbrev EventObs (Expr : Type _) {Val Ectx State Locale : Type _}
    [Language Expr Val Ectx State Locale] : Type _ :=
  List (EventObservation Expr State)

@[rocq_alias trillium.valid_event_obs]
def ValidEventObs (EV : Event Expr) (eo : EventObs Expr) : Prop :=
  ∀ o ∈ eo, ValidEventObservation EV o

/-- `TraceHasEvents EV ex eobs`: `eobs` are the `EV`-events observed along `ex`. -/
@[rocq_alias trillium.trace_has_events]
inductive TraceHasEvents (EV : Event Expr) : ExecutionTrace Expr → EventObs Expr → Prop where
  | singleton (c : List Expr × State) : TraceHasEvents EV {tr[c]} []
  | extendObserved (ex : ExecutionTrace Expr) (c c' : List Expr × State) (tp1 tp2 efs : List Expr)
      (K : Ectx) (eo : EventObservation Expr State) (eobs : EventObs Expr) (oζ : Option Locale) :
      ex.EndsIn c →
      c.2 = eo.preState →
      c.1 = tp1 ++ fill K eo.preExpr :: tp2 →
      c'.2 = eo.postState →
      c'.1 = tp1 ++ fill K eo.postExpr :: (tp2 ++ efs) →
      ValidEventObservation EV eo →
      TraceHasEvents EV ex eobs →
      TraceHasEvents EV (ex :tr[oζ]: c') (eobs ++ [eo])
  | extendNotObserved (ex : ExecutionTrace Expr) (c c' : List Expr × State) (eobs : EventObs Expr)
      (oζ : Option Locale) :
      ex.EndsIn c →
      (∀ tp1 tp2 efs (K : Ectx) e1 e2,
        c.1 = tp1 ++ fill K e1 :: tp2 →
        c'.1 = tp1 ++ fill K e2 :: (tp2 ++ efs) →
        ¬ EV e1 c.2 e2 c'.2) →
      TraceHasEvents EV ex eobs →
      TraceHasEvents EV (ex :tr[oζ]: c') eobs

/-! ## Properties -/

variable (EV : Event Expr)

@[rocq_alias trillium.validEventObservation_exprs_neq]
theorem ValidEventObservation.exprs_ne {obs : EventObservation Expr State} :
    ValidEventObservation EV obs → obs.preExpr ≠ obs.postExpr :=
  EV.isTriggered_not_stuttering _ _ _ _

@[rocq_alias trillium.validEventObservation_not_val]
theorem ValidEventObservation.not_val {obs : EventObservation Expr State} :
    ValidEventObservation EV obs → toVal obs.preExpr = none :=
  EV.isTriggered_not_val _ _ _ _

@[rocq_alias trillium.trace_has_events_valid, rocq_alias trillium.trace_has_valid_events]
theorem TraceHasEvents.valid {ex : ExecutionTrace Expr} {eobs : EventObs Expr} :
    TraceHasEvents EV ex eobs → ValidEventObs EV eobs := by
  intro h
  induction h with
  | singleton => simp [ValidEventObs]
  | extendObserved _ _ _ _ _ _ _ eo _ _ _ _ _ _ _ hv _ ih =>
    intro o ho
    rcases List.mem_append.mp ho with ho | ho
    · exact ih o ho
    · rw [List.mem_singleton.mp ho]; exact hv
  | extendNotObserved _ _ _ _ _ _ _ _ ih => exact ih

/-- Extract the element at position `tp1.length` of two decompositions of a thread pool. -/
private theorem getElem?_middle {A : Type _} (tp1 tp2 : List A) (a : A) :
    (tp1 ++ a :: tp2)[tp1.length]? = some a := by
  simp

@[rocq_alias trillium.event_in_the_middle]
theorem event_in_the_middle {tp1 tp2 : List Expr} {K : Ectx} {e1 e2 : Expr} {efs tp1' tp2' : List Expr}
    {K' : Ectx} {eo : EventObservation Expr State} {efs' : List Expr} :
    ValidEventObservation EV eo →
    toVal e1 = none →
    (∀ e1' (K'' : Ectx), e1 = fill K'' e1' → (toVal e1').isSome ∨ K'' = EvContextOps.empty) →
    tp1 ++ fill K e1 :: tp2 = tp1' ++ fill K' eo.preExpr :: tp2' →
    tp1 ++ fill K e2 :: (tp2 ++ efs) = tp1' ++ fill K' eo.postExpr :: (tp2' ++ efs') →
    eo.preExpr = e1 ∧ eo.postExpr = e2 := by
  intro HEV He1 Hnectx Heq1 Heq2
  have hneq := ValidEventObservation.exprs_ne EV HEV
  have hlen := congrArg List.length Heq1
  simp only [List.length_append, List.length_cons] at hlen
  rcases lt_trichotomy tp1'.length tp1.length with hlt | heq | hgt
  · -- The event happened in a thread in front of `e1`: impossible.
    exfalso
    have h1 := congrArg (·[tp1'.length]?) Heq1
    have h2 := congrArg (·[tp1'.length]?) Heq2
    simp only [List.getElem?_append_left hlt, getElem?_middle] at h1 h2
    rw [h1, Option.some.injEq] at h2
    exact hneq (ectx_fill_inj K' h2)
  · -- The event happened in the thread `e1`.
    obtain ⟨-, h1⟩ := List.append_inj Heq1 heq.symm
    obtain ⟨-, h2⟩ := List.append_inj Heq2 heq.symm
    obtain ⟨Hf1, -⟩ := List.cons.inj h1
    obtain ⟨Hf2, -⟩ := List.cons.inj h2
    have Hpre := ValidEventObservation.not_val EV HEV
    rcases ectx_fill_positive K K' e1 eo.preExpr He1 Hpre Hf1 with ⟨K'', rfl⟩ | ⟨K'', rfl⟩
    · rw [ectx_comp_comp] at Hf1 Hf2
      have Hf1 := ectx_fill_inj K Hf1
      have Hf2 := ectx_fill_inj K Hf2
      rcases Hnectx _ _ Hf1 with Hv | rfl
      · simp [Hpre] at Hv
      · rw [EvContext.fill_empty] at Hf1 Hf2
        exact ⟨Hf1.symm, Hf2.symm⟩
    · rw [ectx_comp_comp] at Hf1 Hf2
      have Hf1 := ectx_fill_inj K' Hf1
      have Hf2 := ectx_fill_inj K' Hf2
      rcases EV.isTriggered_ectx_free _ _ _ _ HEV K'' e1 Hf1.symm with Hv | rfl
      · simp [He1] at Hv
      · rw [EvContext.fill_empty] at Hf1 Hf2
        exact ⟨Hf1.symm, Hf2.symm⟩
  · -- The event happened in a thread after `e1`: impossible.
    exfalso
    obtain ⟨j, hj⟩ : ∃ j, tp1'.length - tp1.length = j + 1 := ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
    have hj2 : j < tp2.length := by omega
    have h1 := congrArg (·[tp1'.length]?) Heq1
    have h2 := congrArg (·[tp1'.length]?) Heq2
    simp only [List.getElem?_append_right hgt.le, hj, List.getElem?_cons_succ, getElem?_middle,
      List.getElem?_append_left hj2] at h1 h2
    rw [h1, Option.some.injEq] at h2
    exact hneq (ectx_fill_inj K' h2)

/-- This lemma, proven completely constructively, is an evidence why we are justified in using
classical logic in constructing observations of a valid execution trace. -/
@[rocq_alias trillium.trace_has_events_functional]
theorem traceHasEvents_functional {ex : ExecutionTrace Expr} {eobs eobs' : EventObs Expr} :
    ValidExec ex → TraceHasEvents EV ex eobs → TraceHasEvents EV ex eobs' → eobs = eobs' := by
  intro Hex
  induction Hex generalizing eobs eobs' with
  | singleton c =>
    rintro (_ | _ | _) (_ | _ | _)
    rfl
  | step ex c oζ c' Hendsin Hstep Hex IHex =>
    intro h1 h2
    cases h1 with
    | extendObserved _ c3 _ tp1 tp2 efs K obs3 eobs3 _ Hendsin' Hs1 Ht1 Hs2 Ht2 Hv3 Hh3 =>
      cases Hendsin.inj Hendsin'
      cases h2 with
      | extendObserved _ c4 _ tp1' tp2' efs' K' obs4 eobs4 _ Hendsin'' Hs1' Ht1' Hs2' Ht2' Hv4
          Hh4 =>
        cases Hendsin.inj Hendsin''
        rw [IHex Hh3 Hh4]
        obtain ⟨Hpre, Hpost⟩ := event_in_the_middle EV Hv4 (ValidEventObservation.not_val EV Hv3)
          (fun e1' K'' h => EV.isTriggered_ectx_free _ _ _ _ Hv3 K'' e1' h)
          (Ht1.symm.trans Ht1') (Ht2.symm.trans Ht2')
        obtain ⟨a, b, c, d⟩ := obs3
        obtain ⟨a', b', c', d'⟩ := obs4
        simp only at Hpre Hpost Hs1 Hs1' Hs2 Hs2'
        subst Hpre Hpost
        rw [← Hs1, ← Hs1', ← Hs2, ← Hs2']
      | extendNotObserved _ c4 _ _ _ Hendsin'' Hnobs Hh4 =>
        cases Hendsin.inj Hendsin''
        exfalso
        refine Hnobs tp1 tp2 efs K obs3.preExpr obs3.postExpr Ht1 Ht2 ?_
        rw [Hs1, Hs2]; exact Hv3
    | extendNotObserved _ c3 _ _ _ Hendsin' Hnobs Hh3 =>
      cases Hendsin.inj Hendsin'
      cases h2 with
      | extendObserved _ c4 _ tp1 tp2 efs K obs4 eobs4 _ Hendsin'' Hs1 Ht1 Hs2 Ht2 Hv4 Hh4 =>
        cases Hendsin.inj Hendsin''
        exfalso
        refine Hnobs tp1 tp2 efs K obs4.preExpr obs4.postExpr Ht1 Ht2 ?_
        rw [Hs1, Hs2]; exact Hv4
      | extendNotObserved _ c4 _ _ _ Hendsin'' _ Hh4 => exact IHex Hh3 Hh4

@[rocq_alias trillium.events_for_trace]
theorem events_for_trace (ex : ExecutionTrace Expr) : ∃ eobs, TraceHasEvents EV ex eobs := by
  induction ex with
  | singleton c => exact ⟨[], .singleton c⟩
  | extend ex oζ c IH =>
    obtain ⟨eobs, Hthe⟩ := IH
    by_cases Hex : ∃ tp1 tp2 efs, ∃ K : Ectx, ∃ e1 e2,
        ex.last.1 = tp1 ++ fill K e1 :: tp2 ∧ c.1 = tp1 ++ fill K e2 :: (tp2 ++ efs) ∧
        EV e1 ex.last.2 e2 c.2
    · obtain ⟨tp1, tp2, efs, K, e1, e2, Heq1, Heq2, HEV⟩ := Hex
      exact ⟨eobs ++ [⟨e1, ex.last.2, e2, c.2⟩],
        .extendObserved _ _ _ tp1 tp2 efs K ⟨e1, ex.last.2, e2, c.2⟩ _ _ ex.endsIn_last rfl Heq1 rfl
          Heq2 HEV Hthe⟩
    · refine ⟨eobs, .extendNotObserved _ _ _ _ _ ex.endsIn_last ?_ Hthe⟩
      intro tp1 tp2 efs K e1 e2 h1 h2 h3
      exact Hex ⟨tp1, tp2, efs, K, e1, e2, h1, h2, h3⟩

/-- The events observed along an execution trace. -/
@[rocq_alias trillium.events_of_trace]
noncomputable def eventsOfTrace (ex : ExecutionTrace Expr) : EventObs Expr :=
  Classical.choose (events_for_trace EV ex)

@[rocq_alias trillium.trace_has_events_of_trace]
theorem traceHasEvents_eventsOfTrace (ex : ExecutionTrace Expr) :
    TraceHasEvents EV ex (eventsOfTrace EV ex) :=
  Classical.choose_spec (events_for_trace EV ex)

@[rocq_alias trillium.events_of_trace_valid]
theorem eventsOfTrace_valid (ex : ExecutionTrace Expr) : ValidEventObs EV (eventsOfTrace EV ex) :=
  (traceHasEvents_eventsOfTrace EV ex).valid EV

@[rocq_alias trillium.events_of_trace_extend_same_tp]
theorem eventsOfTrace_extend_same_tp {ex : ExecutionTrace Expr} {c c' : List Expr × State}
    {oζ : Option Locale} :
    ValidExec (ex :tr[oζ]: c') → c.1 = c'.1 → ex.EndsIn c →
    eventsOfTrace EV (ex :tr[oζ]: c') = eventsOfTrace EV ex := by
  intro Hex Htps Hc
  suffices Help : ∀ eobs, TraceHasEvents EV (ex :tr[oζ]: c') eobs → eventsOfTrace EV ex = eobs from
    (Help _ (traceHasEvents_eventsOfTrace EV _)).symm
  intro eobs Heobs
  cases Heobs with
  | extendObserved _ c0 _ tp1 tp2 efs K eo _ _ Hei _ Ht1 _ Ht2 HEV _ =>
    cases Hc.inj Hei
    exfalso
    rw [← Htps, Ht1] at Ht2
    have := (List.cons.inj (List.append_cancel_left Ht2)).1
    exact ValidEventObservation.exprs_ne EV HEV (ectx_fill_inj K this)
  | extendNotObserved _ _ _ _ _ _ _ Hh =>
    exact traceHasEvents_functional EV Hex.extend_inv.1 (traceHasEvents_eventsOfTrace EV ex) Hh

@[rocq_alias trillium.events_of_singleton_trace]
theorem eventsOfTrace_singleton (c : List Expr × State) :
    eventsOfTrace EV ({tr[c]} : ExecutionTrace Expr) = [] :=
  traceHasEvents_functional EV (.singleton c) (traceHasEvents_eventsOfTrace EV _) (.singleton c)

@[rocq_alias trillium.events_of_trace_extend_pure]
theorem eventsOfTrace_extend_pure {ex : ExecutionTrace Expr} {c c' : List Expr × State}
    {oζ : Option Locale} :
    (∀ eo, ValidEventObservation EV eo → eo.preState ≠ eo.postState) →
    ValidExec (ex :tr[oζ]: c') → c.2 = c'.2 → ex.EndsIn c →
    eventsOfTrace EV (ex :tr[oζ]: c') = eventsOfTrace EV ex := by
  intro Himpure Hex Hst Hc
  suffices Help : ∀ eobs, TraceHasEvents EV (ex :tr[oζ]: c') eobs → eventsOfTrace EV ex = eobs from
    (Help _ (traceHasEvents_eventsOfTrace EV _)).symm
  intro eobs Heobs
  cases Heobs with
  | extendObserved _ c0 _ tp1 tp2 efs K eo _ _ Hei Hs1 _ Hs2 _ HEV _ =>
    cases Hc.inj Hei
    exact absurd (Hs1.symm.trans (Hst.trans Hs2)) (Himpure eo HEV)
  | extendNotObserved _ _ _ _ _ _ _ Hh =>
    exact traceHasEvents_functional EV Hex.extend_inv.1 (traceHasEvents_eventsOfTrace EV ex) Hh

/-- The step from `c` to `c'` triggers the observed event `ob`. -/
@[rocq_alias trillium.event_is_triggered]
def EventIsTriggered (ob : EventObservation Expr State) (c c' : List Expr × State) : Prop :=
  ∃ K : Ectx, ∃ tp1 tp2 efs,
    c.2 = ob.preState ∧
    c.1 = tp1 ++ fill K ob.preExpr :: tp2 ∧
    c'.2 = ob.postState ∧
    c'.1 = tp1 ++ fill K ob.postExpr :: (tp2 ++ efs)

@[rocq_alias trillium.events_of_trace_extend_app]
theorem eventsOfTrace_extend_app {ex : ExecutionTrace Expr} {c : List Expr × State}
    {oζ : Option Locale} :
    ValidExec (ex :tr[oζ]: c) →
    ∃ evs : EventObs Expr,
      evs.length ≤ 1 ∧
      eventsOfTrace EV (ex :tr[oζ]: c) = eventsOfTrace EV ex ++ evs ∧
      ∀ ev ∈ evs, EventIsTriggered ev ex.last c := by
  intro Hvl
  have Hthe := traceHasEvents_eventsOfTrace EV (ex :tr[oζ]: c)
  generalize eventsOfTrace EV (ex :tr[oζ]: c) = E at Hthe ⊢
  cases Hthe with
  | extendObserved _ c0 _ tp1 tp2 efs K eo eobs _ Hend Hs1 Ht1 Hs2 Ht2 _ Hh =>
    refine ⟨[eo], by simp, ?_, ?_⟩
    · rw [traceHasEvents_functional EV Hvl.extend_inv.1 Hh (traceHasEvents_eventsOfTrace EV ex)]
    · intro ev hev
      rw [List.mem_singleton.mp hev]
      cases Hend
      exact ⟨K, tp1, tp2, efs, Hs1, Ht1, Hs2, Ht2⟩
  | extendNotObserved _ c0 _ eobs _ Hend Hnobs Hh =>
    refine ⟨[], by simp, ?_, by simp⟩
    rw [List.append_nil]
    exact traceHasEvents_functional EV Hvl (.extendNotObserved _ _ _ _ _ Hend Hnobs Hh)
      (.extendNotObserved _ _ _ _ _ Hend Hnobs (traceHasEvents_eventsOfTrace EV ex))

@[rocq_alias trillium.events_of_trace_app]
theorem eventsOfTrace_app (ex : ExecutionTrace Expr) (l : List (Option Locale × (List Expr × State))) :
    ValidExec (ex +trl+ l) →
    ∃ evs : EventObs Expr,
      evs.length ≤ l.length ∧
      eventsOfTrace EV (ex +trl+ l) = eventsOfTrace EV ex ++ evs ∧
      ∀ ev oζ1 oζ2, ev ∈ evs →
        ∃ i c1 c2 oζ1' oζ2',
          ((oζ1, ex.last) :: l)[i]? = some (oζ1', c1) ∧
          ((oζ2, ex.last) :: l)[i + 1]? = some (oζ2', c2) ∧
          EventIsTriggered ev c1 c2 := by
  induction l using List.reverseRecOn with
  | nil => intro _; exact ⟨[], by simp, by simp, by simp⟩
  | append_singleton l p IHl =>
    obtain ⟨ζ, c⟩ := p
    rw [appendList_concat]
    intro Hvl
    obtain ⟨evs, Hevs1, Hevs2, Hevs3⟩ := IHl Hvl.extend_inv.1
    obtain ⟨evs', Hevs'1, Hevs'2, Hevs'3⟩ := eventsOfTrace_extend_app EV Hvl
    refine ⟨evs ++ evs', by simp; omega, by rw [Hevs'2, Hevs2, List.append_assoc], ?_⟩
    intro ev oζ1 oζ2 Hev
    rcases List.mem_append.mp Hev with Hev | Hev
    · obtain ⟨i, c1, c2, oζ1', oζ2', Hc1, Hc2, Htrg⟩ := Hevs3 ev oζ1 oζ2 Hev
      refine ⟨i, c1, c2, oζ1', oζ2', ?_, ?_, Htrg⟩
      · rw [← List.cons_append, List.getElem?_append_left (List.getElem?_eq_some_iff.mp Hc1).1]
        exact Hc1
      · rw [← List.cons_append, List.getElem?_append_left (List.getElem?_eq_some_iff.mp Hc2).1]
        exact Hc2
    · obtain ⟨oζ, Heq⟩ := last_appendList_eq_getElem? ex l oζ1
      refine ⟨l.length, _, c, oζ, ζ, ?_, ?_, Hevs'3 ev Hev⟩
      · rw [← List.cons_append, List.getElem?_append_left (by simp)]
        exact Heq
      · simp

@[rocq_alias trillium.events_of_trace_app_map]
theorem eventsOfTrace_app_map (ex : ExecutionTrace Expr)
    (l : List (Option Locale × (List Expr × State))) :
    ValidExec (ex +trl+ l) →
    ∃ evs : EventObs Expr,
      evs.length ≤ l.length ∧
      eventsOfTrace EV (ex +trl+ l) = eventsOfTrace EV ex ++ evs ∧
      ∀ ev, ev ∈ evs →
        ∃ i c1 c2,
          (ex.last :: l.map Prod.snd)[i]? = some c1 ∧
          (ex.last :: l.map Prod.snd)[i + 1]? = some c2 ∧
          EventIsTriggered ev c1 c2 := by
  intro Hval
  obtain ⟨evs, Hlen, Hevs, H⟩ := eventsOfTrace_app EV ex l Hval
  refine ⟨evs, Hlen, Hevs, fun ev Hin => ?_⟩
  obtain ⟨i, c1, c2, oζ1, oζ2, Hi, HSi, Htrig⟩ := H ev none none Hin
  refine ⟨i, c1, c2, ?_, ?_, Htrig⟩
  · rw [show ex.last :: l.map Prod.snd = ((none, ex.last) :: l).map Prod.snd from rfl,
      List.getElem?_map, Hi]
    rfl
  · rw [show ex.last :: l.map Prod.snd = ((none, ex.last) :: l).map Prod.snd from rfl,
      List.getElem?_map, HSi]
    rfl

end

/-! ## Properties for evaluation-context languages -/

section ectx

variable [EctxLanguage Expr Val Ectx State Locale] (EV : Event Expr)

@[rocq_alias trillium.events_of_trace_extend_triggered]
theorem eventsOfTrace_extend_triggered {ex : ExecutionTrace Expr} {tp1 tp2 : List Expr} {K : Ectx}
    {e1 e2 : Expr} {efs : List Expr} {σ1 σ2 : State} {oζ : Option Locale} :
    ValidExec ex →
    ex.EndsIn (tp1 ++ fill K e1 :: tp2, σ1) →
    headStep e1 σ1 e2 σ2 efs →
    EV e1 σ1 e2 σ2 →
    eventsOfTrace EV (ex :tr[oζ]: (tp1 ++ fill K e2 :: (tp2 ++ efs), σ2)) =
      eventsOfTrace EV ex ++ [⟨e1, σ1, e2, σ2⟩] := by
  intro HexV Hex Hhstep HEV
  have Hhasevs := traceHasEvents_eventsOfTrace EV (ex :tr[oζ]: (tp1 ++ fill K e2 :: (tp2 ++ efs), σ2))
  generalize eventsOfTrace EV (ex :tr[oζ]: (tp1 ++ fill K e2 :: (tp2 ++ efs), σ2)) = E at Hhasevs ⊢
  cases Hhasevs with
  | extendObserved _ c0 _ tp1' tp2' efs' K' eo eobs _ Hei Hs1 Ht1 Hs2 Ht2 HEV' Hh =>
    cases Hex.inj Hei
    rw [traceHasEvents_functional EV HexV Hh (traceHasEvents_eventsOfTrace EV ex)]
    obtain ⟨Hpre, Hpost⟩ := event_in_the_middle EV HEV' (EctxLanguage.val_head_stuck Hhstep)
      (fun e1' K'' h => EctxLanguage.head_ctx_step_val (h ▸ Hhstep)) Ht1 Ht2
    obtain ⟨a, b, c, d⟩ := eo
    simp only at Hpre Hpost Hs1 Hs2
    subst Hpre Hpost Hs1 Hs2
    rfl
  | extendNotObserved _ c0 _ eobs _ Hei HnEV _ =>
    cases Hex.inj Hei
    exact absurd HEV (HnEV tp1 tp2 efs K e1 e2 rfl rfl)

@[rocq_alias trillium.events_of_trace_extend_not_triggered]
theorem eventsOfTrace_extend_not_triggered {ex : ExecutionTrace Expr} {tp1 tp2 : List Expr}
    {K : Ectx} {e1 e2 : Expr} {efs : List Expr} {σ1 σ2 : State} {oζ : Option Locale} :
    ValidExec ex →
    ex.EndsIn (tp1 ++ fill K e1 :: tp2, σ1) →
    headStep e1 σ1 e2 σ2 efs →
    ¬ EV e1 σ1 e2 σ2 →
    eventsOfTrace EV (ex :tr[oζ]: (tp1 ++ fill K e2 :: (tp2 ++ efs), σ2)) =
      eventsOfTrace EV ex := by
  intro HexV Hex Hhstep HEV
  have Hhasevs := traceHasEvents_eventsOfTrace EV (ex :tr[oζ]: (tp1 ++ fill K e2 :: (tp2 ++ efs), σ2))
  generalize eventsOfTrace EV (ex :tr[oζ]: (tp1 ++ fill K e2 :: (tp2 ++ efs), σ2)) = E at Hhasevs ⊢
  cases Hhasevs with
  | extendObserved _ c0 _ tp1' tp2' efs' K' eo eobs _ Hei Hs1 Ht1 Hs2 Ht2 HEV' Hh =>
    cases Hex.inj Hei
    exfalso
    obtain ⟨Hpre, Hpost⟩ := event_in_the_middle EV HEV' (EctxLanguage.val_head_stuck Hhstep)
      (fun e1' K'' h => EctxLanguage.head_ctx_step_val (h ▸ Hhstep)) Ht1 Ht2
    obtain ⟨a, b, c, d⟩ := eo
    simp only at Hpre Hpost Hs1 Hs2
    subst Hpre Hpost Hs1 Hs2
    exact HEV HEV'
  | extendNotObserved _ c0 _ eobs _ Hei HnEV Hh =>
    cases Hex.inj Hei
    exact traceHasEvents_functional EV HexV Hh (traceHasEvents_eventsOfTrace EV ex)

end ectx

end Trillium
