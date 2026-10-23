/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.ProgramLogic.Language
import Trillium.ProgramLogic.Traces
import Trillium.Fairness.Inftraces
import Trillium.Fairness.Fairness

/-!
# Matching execution traces and model traces
Port of `fairness/traces_match.v`.

`exauxTracesMatch stateRel lblRel` (Rocq `exaux_traces_match`) relates an execution trace and a
model trace step by step. `valid_inf_system_trace_implies_traces_match{_strong'}` show that the
traces built from a valid infinite system trace match.
-/

namespace Trillium.Fairness

open Trace Trillium Trillium.FiniteTrace

section ExecTraceMatchHelpers

variable {S L : Type _}

/-- The first state of a trace matching an execution is the last state of the execution. -/
theorem ExecTraceMatch.first_eq {ft : FiniteTrace S L} {il : Stream'.Seq (L × S)}
    {tr : Trace S L} (h : ExecTraceMatch ft il tr) : tr.first = ft.last := by
  rcases h.inv with ⟨s, hs, -, rfl⟩ | ⟨-, -, -, -, -, -, rfl⟩
  · exact hs.symm
  · rfl

theorem ExecTraceMatch.nil_inv {ft : FiniteTrace S L} {tr : Trace S L}
    (h : ExecTraceMatch ft .nil tr) : tr = Trace.singl ft.last := by
  rcases h.inv with ⟨s, hs, -, rfl⟩ | ⟨_, _, _, _, _, e, _⟩
  · rw [hs]
  · exact absurd e.symm Stream'.Seq.cons_ne_nil

theorem ExecTraceMatch.cons_inv {ft : FiniteTrace S L} {ℓ : L} {s : S}
    {il : Stream'.Seq (L × S)} {tr : Trace S L} (h : ExecTraceMatch ft (.cons (ℓ, s) il) tr) :
    ∃ tr', ExecTraceMatch (ft :tr[ℓ]: s) il tr' ∧ tr = Trace.cons ft.last ℓ tr' := by
  rcases h.inv with ⟨-, -, e, -⟩ | ⟨s', ℓ', ift, tr', h', e, rfl⟩
  · exact absurd e Stream'.Seq.cons_ne_nil
  · obtain ⟨he, rfl⟩ := Stream'.Seq.cons_injective2 e
    cases he
    exact ⟨tr', h', rfl⟩

end ExecTraceMatchHelpers

section TracesMatch

variable {Expr Val Ectx State Locale : Type _} [Language Expr Val Ectx State Locale]
variable {M : Model}

variable (evolutionPred : List Expr × State → Option Locale → List Expr × State →
  M.mstate → M.mlabel → M.mstate → Prop)
variable (stateRel : List Expr × State → M.mstate → Prop)
variable (lblRel : Option Locale → M.mlabel → Prop)

/-- An execution trace and a model trace match step by step. -/
@[rocq_alias trillium.fairness.exaux_traces_match]
def exauxTracesMatch : Extrace Expr → Trace M.mstate M.mlabel → Prop :=
  TracesMatch lblRel stateRel Language.LocaleStep M.mtrans

@[rocq_alias trillium.fairness.valid_inf_system_trace_implies_traces_match_strong']
theorem valid_inf_system_trace_implies_traces_match_strong'
    (LBL_REL_EV : ∀ c1 oζ c2 δ1 ℓ δ2, evolutionPred c1 oζ c2 δ1 ℓ δ2 → lblRel oζ ℓ)
    (STEP_EV : ∀ c1 oζ c2 δ1 ℓ δ2, evolutionPred c1 oζ c2 δ1 ℓ δ2 → M.mtrans δ1 ℓ δ2)
    (φ : ExecutionTrace Expr → AuxiliaryTrace M → Prop)
    (ex : ExecutionTrace Expr) (atr : AuxiliaryTrace M) (iex : InfExecutionTrace Expr)
    (iatr : InfAuxiliaryTrace M) (progtr : Extrace Expr) (auxtr : Trace M.mstate M.mlabel)
    (Hφ1 : ∀ (ex : ExecutionTrace Expr) (atr : AuxiliaryTrace M),
      φ ex atr → stateRel ex.last atr.last)
    (Hφ2 : ∀ (ex : ExecutionTrace Expr) (oζ : Option Locale) (c : List Expr × State)
      (atr : AuxiliaryTrace M) (ℓ : M.mlabel) (δ : M.mstate),
      φ (ex :tr[oζ]: c) (atr :tr[ℓ]: δ) → evolutionPred ex.last oζ c atr.last ℓ δ) :
    ExecTraceMatch ex iex progtr → ExecTraceMatch atr iatr auxtr →
    ValidInfSystemTrace φ ex atr iex iatr →
    TracesMatch lblRel stateRel Language.LocaleStep M.mtrans progtr auxtr := by
  intro Hem Ham Hval
  refine TracesMatch.coinduct lblRel stateRel Language.LocaleStep M.mtrans
    (fun progtr auxtr => ∃ ex atr iex iatr, ExecTraceMatch ex iex progtr ∧
      ExecTraceMatch atr iatr auxtr ∧ ValidInfSystemTrace φ ex atr iex iatr) ?_ progtr auxtr
    ⟨ex, atr, iex, iatr, Hem, Ham, Hval⟩
  rintro progtr auxtr ⟨ex, atr, iex, iatr, Hem, Ham, Hval⟩
  rw [ValidInfSystemTrace.eq_def] at Hval
  rcases Hval with ⟨Hphi, rfl, rfl⟩ |
    ⟨c, c', δ', iex', iatr', ζ, ℓ, Hphi, Hends, Hstep, Hinf, rfl, rfl⟩
  · exact .inl ⟨ex.last, atr.last, Hφ1 ex atr Hphi, Hem.nil_inv, Ham.nil_inv⟩
  · obtain ⟨tr1, Hem', rfl⟩ := Hem.cons_inv
    obtain ⟨tr2, Ham', rfl⟩ := Ham.cons_inv
    have STEP := Hφ2 _ _ _ _ _ _ (ValidInfSystemTrace.inv Hinf)
    rw [endsIn_iff] at Hends
    subst Hends
    refine .inr ⟨ex.last, ζ, tr1, atr.last, ℓ, tr2, LBL_REL_EV _ _ _ _ _ _ STEP,
      Hφ1 ex atr Hphi, ?_, ?_, ⟨_, _, iex', iatr', Hem', Ham', Hinf⟩, rfl, rfl⟩
    · rw [Hem'.first_eq]; exact Hstep
    · rw [Ham'.first_eq]; exact STEP_EV _ _ _ _ _ _ STEP

/-- The evolution predicate holds for the last step of the traces. -/
@[rocq_alias trillium.fairness.valid_state_evolution_fairness]
def validStateEvolutionFairness (extr : ExecutionTrace Expr) (auxtr : AuxiliaryTrace M) : Prop :=
  match extr, auxtr with
  | .extend extr oζ (es, σ), .extend auxtr ℓ δ =>
    evolutionPred extr.last oζ (es, σ) auxtr.last ℓ δ
  | _, _ => True

@[rocq_alias trillium.fairness.valid_inf_system_trace_implies_traces_match]
theorem valid_inf_system_trace_implies_traces_match
    (LBL_REL_EV : ∀ c1 oζ c2 δ1 ℓ δ2, evolutionPred c1 oζ c2 δ1 ℓ δ2 → lblRel oζ ℓ)
    (STEP_EV : ∀ c1 oζ c2 δ1 ℓ δ2, evolutionPred c1 oζ c2 δ1 ℓ δ2 → M.mtrans δ1 ℓ δ2)
    (φ : ExecutionTrace Expr → AuxiliaryTrace M → Prop)
    (ex : ExecutionTrace Expr) (atr : AuxiliaryTrace M) (iex : InfExecutionTrace Expr)
    (iatr : InfAuxiliaryTrace M) (progtr : Extrace Expr) (auxtr : Trace M.mstate M.mlabel)
    (Hφ1 : ∀ (ex : ExecutionTrace Expr) (atr : AuxiliaryTrace M),
      φ ex atr → stateRel ex.last atr.last)
    (Hφ2 : ∀ (ex : ExecutionTrace Expr) (atr : AuxiliaryTrace M),
      φ ex atr → validStateEvolutionFairness evolutionPred ex atr) :
    ExecTraceMatch ex iex progtr → ExecTraceMatch atr iatr auxtr →
    ValidInfSystemTrace φ ex atr iex iatr →
    TracesMatch lblRel stateRel Language.LocaleStep M.mtrans progtr auxtr :=
  valid_inf_system_trace_implies_traces_match_strong' evolutionPred stateRel lblRel LBL_REL_EV
    STEP_EV φ ex atr iex iatr progtr auxtr Hφ1
    (fun ex oζ c atr ℓ δ H => by
      have := Hφ2 _ _ H
      obtain ⟨es, σ⟩ := c
      exact this)

end TracesMatch

end Trillium.Fairness
