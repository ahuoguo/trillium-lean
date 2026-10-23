/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.Fairis.Fuel
import Trillium.Fairis.FairTermination

/-!
# Fair termination via live models
Port of `fairis/fuel_termination.v`.

If an execution is related, by a continued simulation, to a live model over a fair terminating
model, then the execution is fairly terminating: a fair infinite execution would yield a fair
auxiliary trace, which destutters into a fair infinite model trace, contradicting fair
termination of the model.
-/

namespace Trillium.Fairis

open Trillium Trillium.Fairness Trace

/-- A valid auxiliary trace which is fair for every role terminates (Rocq
`auxtrace_fairly_terminating`). -/
@[rocq_alias trillium.fairis.auxtrace_fairly_terminating]
def AuxtraceFairlyTerminating {Locale : Type _} [Ord Locale] [Std.TransOrd Locale]
    [Std.LawfulEqOrd Locale] {Mdl : FairModel} {LM : LiveModel Locale Mdl}
    (auxtr : Auxtrace LM) : Prop :=
  AuxtraceValid LM auxtr → (∀ ρ, fairAux ρ auxtr) → terminatingTrace auxtr

/-- Rocq `continued_simulation_fair_termination`. As in Rocq, the hypothesis that the language
has no configuration steps is not used by the proof. -/
@[rocq_alias trillium.fairis.continued_simulation_fair_termination]
theorem continued_simulation_fair_termination {FM : FairModel} [FairTerminatingModel FM]
    {Locale : Type _} [Ord Locale] [Std.TransOrd Locale] [Std.LawfulEqOrd Locale]
    [DecidableEq Locale] {Expr Val Ectx State : Type _} [Language Expr Val Ectx State Locale]
    (LM : LiveModel Locale FM) (ξ : ExecutionTrace Expr → AuxiliaryTrace LM.toModel → Prop)
    (a1 : FM.fmstate) (r1 : Locale) (extr : Extrace Expr) :
    (∀ c c', Language.LocaleStep (Expr := Expr) c none c' → False) →
    (∀ (ex : ExecutionTrace Expr) (atr : AuxiliaryTrace LM.toModel), ξ ex atr →
      liveTids (M := FM) ex.last atr.last) →
    (∀ (ex : ExecutionTrace Expr) (atr : AuxiliaryTrace LM.toModel), ξ ex atr →
      validStateEvolutionFairness LM ex atr) →
    ContinuedSimulation ξ ({tr[extr.first]} : ExecutionTrace Expr)
      ({tr[initialLs LM a1 r1]} : AuxiliaryTrace LM.toModel) →
    ExtraceFairlyTerminating extr := by
  intro _Hstep Hlive Hvalid Hsim Hvex
  rcases infinite_or_finite extr with Hinf | Hfin
  swap
  · exact fun _ => Hfin
  have Hvalinf : ValidInfExec ({tr[extr.first]} : ExecutionTrace Expr) (fromTrace extr) :=
    from_trace_preserves_validity_singleton extr Hvex
  have Hiatr := produced_inf_aux_trace_valid_inf ξ _ _
    (ValidSystemTrace.singleton extr.first (initialLs LM a1 r1)) Hsim (fromTrace extr) Hvalinf
  have Hmatch : ExauxTracesMatch Expr LM extr
      (toTrace (initialLs LM a1 r1) (produceInfAuxTrace ξ _ _ Hsim (fromTrace extr) Hvalinf)) :=
    valid_inf_system_trace_implies_traces_match LM (ContinuedSimulation ξ) _ _ _ _ extr _
      (fun ex atr h => Hlive ex atr h.rel) (fun ex atr h => Hvalid ex atr h.rel)
      (from_trace_spec _ extr rfl) (to_trace_spec _ _) Hiatr
  intro Hfair
  have Hvalaux := exaux_preserves_validity extr _ Hmatch
  obtain ⟨mtr, Hupto⟩ := can_destutter_auxtr _ Hvalaux
  have Hfairaux := fairness_preserved extr _ Hinf Hmatch Hfair
  have Hfairm := upto_stutter_fairness _ mtr Hupto Hfairaux
  have Hmtrvalid := upto_preserves_validity _ mtr Hupto Hvalaux
  exact exaux_preserves_termination extr _ Hmatch
    (upto_stutter_finiteness _ mtr Hupto (fair_terminating_traces_terminate mtr Hmtrvalid Hfairm))

end Trillium.Fairis
