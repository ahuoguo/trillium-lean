/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.ProgramLogic.Language
import Trillium.Traces.Trace
import Trillium.Traces.InfiniteTrace
import Trillium.Prelude.Fixpoint

/-!
# Execution traces, models and simulations
Port of `trillium/program_logic/traces.v`.

* `ExecutionTrace Expr` (Rocq `execution_trace Λ`): finite traces of configurations
  `List Expr × State` labelled by `Option Locale`.
* `Model` (Rocq `Model`): a structure with a type of states `mstate` (coerced to `Type`, Rocq's
  `mstate :>`), a type of labels `mlabel` and a transition relation `mtrans`.
  `AuxiliaryTrace M` (Rocq notation `auxiliary_trace M`) is `FiniteTrace M.mstate M.mlabel`.
* `ValidExec ex` (Rocq `valid_exec`): every step of `ex` is a `LocaleStep`.
* `ValidSystemTrace ex atr` (Rocq `valid_system_trace`).
* `ContinuedSimulation φ ex atr` (Rocq `continued_simulation`), defined, as in Rocq, as the
  greatest fixpoint `GFX` of `ContinuedSimulationPreCurried φ`; `continuedSimulation_unfold`
  is the unfolding lemma.
* `InfExecutionTrace Expr` (Rocq `inf_execution_trace Λ`) and `InfAuxiliaryTrace M` are
  possibly-infinite lists (`Stream'.Seq`, see `Trillium.Traces.InfiniteTrace`).
  `ValidInfExec` and `ValidInfSystemTrace` (Rocq `CoInductive`s) are Lean `coinductive`
  predicates; use `ValidInfExec.coinduct` to prove them and `cases h` (or the `…dest` lemmas)
  to destruct them.
* `produceInfAuxTrace` (Rocq `CoFixpoint produce_inf_aux_trace`) is defined with
  `Stream'.Seq.corec`; `produceInfAuxTrace_nil` / `produceInfAuxTrace_cons` are its unfolding
  equations.

Rocq's `epsilon` is `Classical.choose`. The language `Λ` is represented by the class
`Trillium.Language Expr Val Ectx State Locale` (see `Trillium.ProgramLogic.Language`); the Rocq
notation `olocale Λ` is `Option Locale`.
-/

namespace Trillium

open FiniteTrace Language

/-- Execution traces of a language: finite traces of configurations, labelled by the locale of
the thread taking the step (`none` for configuration steps). -/
@[rocq_alias trillium.execution_trace]
abbrev ExecutionTrace (Expr : Type _) {Val Ectx State Locale : Type _}
    [Language Expr Val Ectx State Locale] : Type _ :=
  FiniteTrace (List Expr × State) (Option Locale)

/-- A model: a labelled transition system. Its states are obtained by coercing the model to a
type (Rocq `mstate :>`). -/
@[rocq_alias trillium.Model]
structure Model where
  /-- The states of the model. -/
  mstate : Type _
  /-- The labels of the model. -/
  mlabel : Type _
  /-- The transition relation of the model. -/
  mtrans : mstate → mlabel → mstate → Prop

instance : CoeSort Model (Type _) := ⟨Model.mstate⟩

/-- Rocq notation `auxiliary_trace M`: finite traces of model states labelled by model labels. -/
abbrev AuxiliaryTrace (M : Model) : Type _ := FiniteTrace M.mstate M.mlabel

variable {Expr Val Ectx State Locale : Type _} [Language Expr Val Ectx State Locale]

/-! ## Valid executions -/

section execution_trace

/-- Every step of the execution is a (locale-labelled) step of the language. -/
@[rocq_alias trillium.valid_exec]
abbrev ValidExec (ex : ExecutionTrace Expr) : Prop := TraceSteps LocaleStep ex

@[rocq_alias trillium.valid_singleton_exec]
theorem ValidExec.singleton (c : List Expr × State) :
    ValidExec ({tr[c]} : ExecutionTrace Expr) :=
  TraceSteps.singleton c

@[rocq_alias trillium.extend_valid_exec]
theorem ValidExec.extend {ex : ExecutionTrace Expr} {c : List Expr × State} {ζ : Option Locale}
    {c' : List Expr × State} :
    ValidExec ex → ex.EndsIn c → LocaleStep c ζ c' → ValidExec (ex :tr[ζ]: c') :=
  fun h1 h2 h3 => .step _ _ _ _ h2 h3 h1

@[rocq_alias trillium.valid_exec_exec_extend_inv]
theorem ValidExec.extend_inv {ex : ExecutionTrace Expr} {ζ : Option Locale}
    {c' : List Expr × State} :
    ValidExec (ex :tr[ζ]: c') → ValidExec ex ∧ ∃ c, ex.EndsIn c ∧ LocaleStep c ζ c' :=
  TraceSteps.step_inv

end execution_trace

/-! ## Valid system traces -/

section system_trace

variable {M : Model}

/-- The execution trace and the auxiliary trace advance in lockstep, the execution trace taking
valid steps. -/
@[rocq_alias trillium.valid_system_trace]
inductive ValidSystemTrace : ExecutionTrace Expr → AuxiliaryTrace M → Prop where
  | singleton (c : List Expr × State) (δ : M.mstate) : ValidSystemTrace {tr[c]} {tr[δ]}
  | step (ex : ExecutionTrace Expr) (atr : AuxiliaryTrace M) (c c' : List Expr × State)
      (δ' : M.mstate) (ζ : Option Locale) (ℓ : M.mlabel) :
      ex.EndsIn c → LocaleStep c ζ c' → ValidSystemTrace ex atr →
      ValidSystemTrace (ex :tr[ζ]: c') (atr :tr[ℓ]: δ')

@[rocq_alias trillium.valid_system_trace_valid_exec_trace]
theorem ValidSystemTrace.validExec {ex : ExecutionTrace Expr} {atr : AuxiliaryTrace M} :
    ValidSystemTrace ex atr → ValidExec ex := by
  intro h
  induction h with
  | singleton c δ => exact .singleton c
  | step _ _ _ _ _ _ _ h1 h2 _ ih => exact ih.extend h1 h2

@[rocq_alias trillium.valid_system_trace_singletons]
theorem ValidSystemTrace.singletons (c : List Expr × State) (δ : M.mstate) :
    ValidSystemTrace (M := M) ({tr[c]} : ExecutionTrace Expr) {tr[δ]} :=
  .singleton c δ

@[rocq_alias trillium.valid_system_trace_extend]
theorem ValidSystemTrace.extend {ex : ExecutionTrace Expr} {atr : AuxiliaryTrace M}
    {c c' : List Expr × State} {δ' : M.mstate} {ζ : Option Locale} {ℓ : M.mlabel} :
    ValidSystemTrace ex atr → ex.EndsIn c → LocaleStep c ζ c' →
    ValidSystemTrace (ex :tr[ζ]: c') (atr :tr[ℓ]: δ') :=
  fun h1 h2 h3 => .step _ _ _ _ _ _ _ h2 h3 h1

@[rocq_alias trillium.valid_system_trace_extend_inv]
theorem ValidSystemTrace.extend_inv {ex : ExecutionTrace Expr} {atr : AuxiliaryTrace M}
    {c' : List Expr × State} {δ' : M.mstate} {ζ : Option Locale} {ℓ : M.mlabel} :
    ValidSystemTrace (ex :tr[ζ]: c') (atr :tr[ℓ]: δ') →
    ∃ c, ValidSystemTrace ex atr ∧ ex.EndsIn c ∧ LocaleStep c ζ c' := by
  rintro (_ | ⟨_, _, c, _, _, _, _, h1, h2, h3⟩)
  exact ⟨c, h3, h1, h2⟩

@[rocq_alias trillium.valid_system_trace_ends_in]
theorem ValidSystemTrace.endsIn {ex : ExecutionTrace Expr} {atr : AuxiliaryTrace M} :
    ValidSystemTrace ex atr → ∃ c δ, ex.EndsIn c ∧ atr.EndsIn δ :=
  fun _ => ⟨_, _, ex.endsIn_last, atr.endsIn_last⟩

@[rocq_alias trillium.traces.trace_steps2_trace_steps]
theorem trace_steps2_trace_steps (R : M.mstate → M.mlabel → M.mstate → Prop) :
    (∀ (ex : ExecutionTrace Expr) (atr : AuxiliaryTrace M) c δ c' δ' ζ ℓ,
        ex.EndsIn c → atr.EndsIn δ → LocaleStep c ζ c' → R δ ℓ δ') →
    ∀ (ex : ExecutionTrace Expr) (atr : AuxiliaryTrace M),
      ValidSystemTrace ex atr → ValidExec ex ∧ TraceSteps R atr := by
  intro HR ex atr h
  induction h with
  | singleton c δ => exact ⟨.singleton c, .singleton δ⟩
  | step ex atr c c' δ' ζ ℓ h1 h2 _ ih =>
    exact ⟨ih.1.extend h1 h2,
      .step _ _ _ _ atr.endsIn_last (HR ex atr c _ c' δ' ζ ℓ h1 atr.endsIn_last h2) ih.2⟩

end system_trace

/-! ## Simulations -/

section simulation

variable {M : Model}

/-- One unfolding of `ContinuedSimulation`: `φ` holds now, and every step of the execution can
be matched by a step of the auxiliary trace, after which the simulation continues. -/
@[rocq_alias trillium.continued_simulation_pre]
def ContinuedSimulationPre (φ : ExecutionTrace Expr → AuxiliaryTrace M → Prop)
    (continuedSimulation : ExecutionTrace Expr → AuxiliaryTrace M → Prop) :
    ExecutionTrace Expr → AuxiliaryTrace M → Prop :=
  fun ex atr =>
    φ ex atr ∧
    ∀ c c' ζ, ex.EndsIn c → LocaleStep c ζ c' →
      ∃ δ' ℓ, continuedSimulation (ex :tr[ζ]: c') (atr :tr[ℓ]: δ')

/-- `ContinuedSimulationPre` on pairs (Rocq `Local Definition`). -/
@[rocq_alias trillium.continued_simulation_pre_curried]
def ContinuedSimulationPreCurried (φ : ExecutionTrace Expr → AuxiliaryTrace M → Prop) :
    (ExecutionTrace Expr × AuxiliaryTrace M → Prop) →
    (ExecutionTrace Expr × AuxiliaryTrace M → Prop) :=
  fun ψ exatr => ContinuedSimulationPre φ (fun ex atr => ψ (ex, atr)) exatr.1 exatr.2

@[rocq_alias trillium.continued_simulation_pre_curried_mono]
theorem continuedSimulationPreCurried_mono (φ : ExecutionTrace Expr → AuxiliaryTrace M → Prop) :
    PredMonotone (ContinuedSimulationPreCurried φ) := by
  rintro P Q HPQ ⟨ex, atr⟩ ⟨Hφ, HP⟩
  refine ⟨Hφ, fun c c' ζ h1 h2 => ?_⟩
  obtain ⟨δ', ℓ, h⟩ := HP c c' ζ h1 h2
  exact ⟨δ', ℓ, HPQ _ h⟩

/-- The simulation relation: the greatest fixpoint of `ContinuedSimulationPre φ`. -/
@[rocq_alias trillium.continued_simulation]
def ContinuedSimulation (φ : ExecutionTrace Expr → AuxiliaryTrace M → Prop) :
    ExecutionTrace Expr → AuxiliaryTrace M → Prop :=
  fun ex atr => GFX (ContinuedSimulationPreCurried φ) (ex, atr)

@[rocq_alias trillium.continued_simulation_unfold]
theorem continuedSimulation_unfold (φ : ExecutionTrace Expr → AuxiliaryTrace M → Prop)
    (ex : ExecutionTrace Expr) (atr : AuxiliaryTrace M) :
    ContinuedSimulation φ ex atr ↔ ContinuedSimulationPre φ (ContinuedSimulation φ) ex atr :=
  (GFX.fixpoint (continuedSimulationPreCurried_mono φ) (ex, atr)).symm

@[rocq_alias trillium.continued_simulation_rel]
theorem ContinuedSimulation.rel {Φ : ExecutionTrace Expr → AuxiliaryTrace M → Prop}
    {ex : ExecutionTrace Expr} {tr : AuxiliaryTrace M} :
    ContinuedSimulation Φ ex tr → Φ ex tr :=
  fun h => ((continuedSimulation_unfold Φ ex tr).mp h).1

@[rocq_alias trillium.continued_simulation_next_aux_state_exists]
theorem ContinuedSimulation.next_aux_state_exists
    {φ : ExecutionTrace Expr → AuxiliaryTrace M → Prop} {ex : ExecutionTrace Expr}
    {atr : AuxiliaryTrace M} {c : List Expr × State} {ζ : Option Locale} :
    ContinuedSimulation φ ex atr → ValidExec (ex :tr[ζ]: c) →
    ∃ δℓ : M.mstate × M.mlabel, ContinuedSimulation φ (ex :tr[ζ]: c) (atr :tr[δℓ.2]: δℓ.1) := by
  rw [continuedSimulation_unfold]
  rintro ⟨-, Hext⟩ Hvex
  obtain ⟨-, c1, Hc1, Hstep⟩ := Hvex.extend_inv
  obtain ⟨δ', ℓ, h⟩ := Hext c1 c ζ Hc1 Hstep
  exact ⟨(δ', ℓ), h⟩

@[rocq_alias trillium.simulation_does_continue]
theorem simulation_does_continue {es : List Expr} {σ : State} {δ : M.mstate}
    {φ : ExecutionTrace Expr → AuxiliaryTrace M → Prop} :
    ContinuedSimulation φ {tr[(es, σ)]} {tr[δ]} →
    ∀ ex : ExecutionTrace Expr, ex.StartsIn (es, σ) → ValidExec ex →
      ∃ atr : AuxiliaryTrace M, atr.StartsIn δ ∧ ContinuedSimulation φ ex atr := by
  intro Hsm ex Hexstr Hex
  induction Hex with
  | singleton x =>
    cases singleton_startsIn_inv Hexstr
    exact ⟨{tr[δ]}, rfl, Hsm⟩
  | step ex x ℓ y h1 h2 hex IHex =>
    obtain ⟨atr, Hstarts, Hsim⟩ := IHex (StartsIn.of_extend Hexstr)
    obtain ⟨⟨δ', ℓ'⟩, h⟩ := Hsim.next_aux_state_exists (ValidExec.extend hex h1 h2)
    exact ⟨_, StartsIn.extend _ _ Hstarts, h⟩

@[rocq_alias trillium.continued_simulation_impl]
theorem ContinuedSimulation.impl {Φ Ψ : ExecutionTrace Expr → AuxiliaryTrace M → Prop}
    {ex : ExecutionTrace Expr} {tr : AuxiliaryTrace M} (Himpl : ∀ ex tr, Φ ex tr → Ψ ex tr) :
    ContinuedSimulation Φ ex tr → ContinuedSimulation Ψ ex tr := by
  intro Hphi
  refine GFX.coind (fun p => ContinuedSimulation Φ p.1 p.2) ?_ Hphi
  rintro ⟨ex, atr⟩ h
  obtain ⟨h1, h2⟩ := (continuedSimulation_unfold Φ ex atr).mp h
  exact ⟨Himpl _ _ h1, h2⟩

end simulation

/-! ## Infinite execution traces -/

/-- Possibly-infinite continuations of execution traces. -/
@[rocq_alias trillium.inf_execution_trace]
abbrev InfExecutionTrace (Expr : Type _) {Val Ectx State Locale : Type _}
    [Language Expr Val Ectx State Locale] : Type _ :=
  Stream'.Seq (Option Locale × (List Expr × State))

@[rocq_alias trillium.inf_exec_prepend]
abbrev infExecPrepend (ζ : Option Locale) (c : List Expr × State) (iex : InfExecutionTrace Expr) :
    InfExecutionTrace Expr :=
  .cons (ζ, c) iex

/-- `ValidInfExec ex iex`: `ex` is a valid execution, and its continuation by `iex` consists of
valid steps. -/
@[rocq_alias trillium.valid_inf_exec]
coinductive ValidInfExec : ExecutionTrace Expr → InfExecutionTrace Expr → Prop where
  | singleton ex : ValidExec ex → ValidInfExec ex .nil
  | step ex c c' iex ζ :
    ValidExec ex → ex.EndsIn c → LocaleStep c ζ c' → ValidInfExec (ex :tr[ζ]: c') iex →
    ValidInfExec ex (infExecPrepend ζ c' iex)

/-- Possibly-infinite continuations of auxiliary traces. -/
@[rocq_alias trillium.inf_auxiliary_trace]
abbrev InfAuxiliaryTrace (M : Model) : Type _ := Stream'.Seq (M.mlabel × M.mstate)

@[rocq_alias trillium.inf_auxtr_prepend]
abbrev infAuxtrPrepend {M : Model} (ℓ : M.mlabel) (δ : M.mstate) (atr : InfAuxiliaryTrace M) :
    InfAuxiliaryTrace M :=
  .cons (ℓ, δ) atr

/-- `ValidInfSystemTrace Ψ ex atr iex iatr`: the infinite continuations `iex`, `iatr` advance in
lockstep with valid execution steps, and `Ψ` holds at every point. -/
@[rocq_alias trillium.valid_inf_system_trace]
coinductive ValidInfSystemTrace {M : Model} (Ψ : ExecutionTrace Expr → AuxiliaryTrace M → Prop) :
    ExecutionTrace Expr → AuxiliaryTrace M → InfExecutionTrace Expr → InfAuxiliaryTrace M →
      Prop where
  | singleton ex atr : Ψ ex atr → ValidInfSystemTrace Ψ ex atr .nil .nil
  | step ex atr c c' δ' iex iatr ζ ℓ :
    Ψ ex atr → ex.EndsIn c → LocaleStep c ζ c' →
    ValidInfSystemTrace Ψ (ex :tr[ζ]: c') (atr :tr[ℓ]: δ') iex iatr →
    ValidInfSystemTrace Ψ ex atr (infExecPrepend ζ c' iex) (infAuxtrPrepend ℓ δ' iatr)

@[rocq_alias trillium.valid_inf_system_trace_inv]
theorem ValidInfSystemTrace.inv {M : Model} {Ψ : ExecutionTrace Expr → AuxiliaryTrace M → Prop}
    {ex : ExecutionTrace Expr} {atr : AuxiliaryTrace M} {iex : InfExecutionTrace Expr}
    {itr : InfAuxiliaryTrace M} :
    ValidInfSystemTrace Ψ ex atr iex itr → Ψ ex atr := by
  intro h
  rw [ValidInfSystemTrace.eq_def] at h
  rcases h with ⟨h, -⟩ | ⟨-, -, -, -, -, -, -, h, -⟩ <;> exact h

section inf_simulation

variable {M : Model} (φ : ExecutionTrace Expr → AuxiliaryTrace M → Prop)

@[rocq_alias trillium.valid_system_trace_start_or_contract]
theorem ValidSystemTrace.start_or_contract {ex : ExecutionTrace Expr} {atr : AuxiliaryTrace M} :
    ValidSystemTrace ex atr →
    (ex = {tr[ex.first]} ∧ atr = {tr[atr.first]}) ∨
    (∃ ex' atr' oζ ℓ, ex.Contract oζ ex' ∧ atr.Contract ℓ atr') := by
  rintro (_ | ⟨ex', atr', _, c', δ', oζ, ℓ, -, -, -⟩)
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨ex', atr', oζ, ℓ, ⟨c', rfl⟩, ⟨δ', rfl⟩⟩

/-- Destruct a `ValidInfExec` on a non-empty continuation. -/
theorem ValidInfExec.cons_inv {ex : ExecutionTrace Expr} {ζ : Option Locale}
    {c : List Expr × State} {iex : InfExecutionTrace Expr} :
    ValidInfExec ex (.cons (ζ, c) iex) →
    ValidExec ex ∧ ∃ c0, ex.EndsIn c0 ∧ LocaleStep c0 ζ c ∧ ValidInfExec (ex :tr[ζ]: c) iex := by
  intro h
  rw [ValidInfExec.eq_def] at h
  rcases h with ⟨-, h⟩ | ⟨c0, c', iex', ζ', h1, h2, h3, h4, heq⟩
  · exact absurd h Stream'.Seq.cons_ne_nil
  · obtain ⟨h, rfl⟩ := Stream'.Seq.cons_injective2 heq
    cases h
    exact ⟨h1, c0, h2, h3, h4⟩

@[rocq_alias trillium.valid_inf_exec_prepend_valid_exec_extend]
theorem ValidInfExec.prepend_validExec_extend {ex : ExecutionTrace Expr}
    {c : List Expr × State} {iex : InfExecutionTrace Expr} {ζ : Option Locale} :
    ValidInfExec ex (infExecPrepend ζ c iex) → ValidExec (ex :tr[ζ]: c) := by
  intro h
  obtain ⟨h1, c0, h2, h3, -⟩ := h.cons_inv
  exact h1.extend h2 h3

@[rocq_alias trillium.produce_inf_aux_trace_next_aux_state_exists]
theorem produceInfAuxTrace_next_aux_state_exists (ex : ExecutionTrace Expr)
    (atr : AuxiliaryTrace M) (Hcsm : ContinuedSimulation φ ex atr) (c : List Expr × State)
    (ζ : Option Locale) (iex : InfExecutionTrace Expr)
    (Hvex : ValidInfExec ex (infExecPrepend ζ c iex)) :
    ∃ δℓ : M.mstate × M.mlabel, ContinuedSimulation φ (ex :tr[ζ]: c) (atr :tr[δℓ.2]: δℓ.1) :=
  Hcsm.next_aux_state_exists Hvex.prepend_validExec_extend

/-- The next state and label of the auxiliary trace, chosen by the axiom of choice. -/
@[rocq_alias trillium.produce_inf_aux_trace_next_aux_state]
noncomputable def produceInfAuxTraceNextAuxState (ex : ExecutionTrace Expr)
    (atr : AuxiliaryTrace M) (Hcsm : ContinuedSimulation φ ex atr) (c : List Expr × State)
    (ζ : Option Locale) (iex : InfExecutionTrace Expr)
    (Hvex : ValidInfExec ex (infExecPrepend ζ c iex)) : M.mstate × M.mlabel :=
  Classical.choose (produceInfAuxTrace_next_aux_state_exists φ ex atr Hcsm c ζ iex Hvex)

@[rocq_alias trillium.trace_extend_uncurry]
def traceExtendUncurry (tr : AuxiliaryTrace M) (xy : M.mstate × M.mlabel) : AuxiliaryTrace M :=
  tr :tr[xy.2]: xy.1

@[rocq_alias trillium.produce_inf_aux_trace_next_aux_state_continued_simulation]
theorem produceInfAuxTraceNextAuxState_continuedSimulation (ex : ExecutionTrace Expr)
    (atr : AuxiliaryTrace M) (Hcsm : ContinuedSimulation φ ex atr) (c : List Expr × State)
    (ζ : Option Locale) (iex : InfExecutionTrace Expr)
    (Hvex : ValidInfExec ex (infExecPrepend ζ c iex)) :
    ContinuedSimulation φ (ex :tr[ζ]: c)
      (traceExtendUncurry atr (produceInfAuxTraceNextAuxState φ ex atr Hcsm c ζ iex Hvex)) :=
  Classical.choose_spec (produceInfAuxTrace_next_aux_state_exists φ ex atr Hcsm c ζ iex Hvex)

@[rocq_alias trillium.valid_inf_exec_adjust]
theorem ValidInfExec.adjust {ex : ExecutionTrace Expr}
    {c : List Expr × State} {iex : InfExecutionTrace Expr} {ζ : Option Locale} :
    ValidInfExec ex (.cons (ζ, c) iex) → ValidInfExec (ex :tr[ζ]: c) iex :=
  fun h => by
    obtain ⟨-, -, -, -, h⟩ := h.cons_inv
    exact h

@[rocq_alias trillium.valid_inf_exe_valid_exec]
theorem ValidInfExec.validExec {ex : ExecutionTrace Expr} {iex : InfExecutionTrace Expr} :
    ValidInfExec ex iex → ValidExec ex := by
  intro h
  rw [ValidInfExec.eq_def] at h
  rcases h with ⟨h, -⟩ | ⟨-, -, -, -, h, -⟩ <;> exact h

@[rocq_alias trillium.valid_inf_exe_take_drop]
theorem ValidInfExec.take_drop {ex : ExecutionTrace Expr} {iex : InfExecutionTrace Expr} (n : Nat) :
    ValidInfExec ex iex → ValidInfExec (ex +trl+ iex.take n) (iex.drop n) := by
  induction n generalizing ex iex with
  | zero => simp
  | succ n IHn =>
    intro Hvl
    rcases InfList.eq_nil_or_cons iex with rfl | ⟨⟨ζ, c⟩, iex, rfl⟩
    · simpa using Hvl
    · simpa using IHn Hvl.adjust

/-- The state of the corecursion defining `produceInfAuxTrace`. -/
private abbrev ProduceState : Type _ :=
  (ex : ExecutionTrace Expr) ×' (atr : AuxiliaryTrace M) ×' ContinuedSimulation φ ex atr ×'
    (iex : InfExecutionTrace Expr) ×' ValidInfExec ex iex

/-- One step of the corecursion defining `produceInfAuxTrace`. -/
private noncomputable def produceStep (s : ProduceState (Expr := Expr) φ) :
    Option ((M.mlabel × M.mstate) × ProduceState (Expr := Expr) φ) :=
  match h : Stream'.Seq.destruct s.2.2.2.1 with
  | none => none
  | some ((ζ, c), iex') =>
    have Hvex' : ValidInfExec s.1 (infExecPrepend ζ c iex') := by
      have := s.2.2.2.2
      rwa [Stream'.Seq.destruct_eq_cons h] at this
    let δℓ := produceInfAuxTraceNextAuxState φ s.1 s.2.1 s.2.2.1 c ζ iex' Hvex'
    some ((δℓ.2, δℓ.1),
      ⟨s.1 :tr[ζ]: c, s.2.1 :tr[δℓ.2]: δℓ.1,
        produceInfAuxTraceNextAuxState_continuedSimulation φ s.1 s.2.1 s.2.2.1 c ζ iex' Hvex',
        iex', Hvex'.adjust⟩)

/-- Given a simulation between `ex` and `atr`, and an infinite continuation `iex` of `ex`,
produce a matching infinite continuation of `atr` (Rocq `CoFixpoint`). -/
@[rocq_alias trillium.produce_inf_aux_trace]
noncomputable def produceInfAuxTrace (ex : ExecutionTrace Expr) (atr : AuxiliaryTrace M)
    (Hcsm : ContinuedSimulation φ ex atr) (iex : InfExecutionTrace Expr)
    (Hvex : ValidInfExec ex iex) : InfAuxiliaryTrace M :=
  Stream'.Seq.corec (produceStep φ) ⟨ex, atr, Hcsm, iex, Hvex⟩

theorem produceInfAuxTrace_nil (ex : ExecutionTrace Expr) (atr : AuxiliaryTrace M)
    (Hcsm : ContinuedSimulation φ ex atr) (Hvex : ValidInfExec ex .nil) :
    produceInfAuxTrace φ ex atr Hcsm .nil Hvex = .nil := by
  apply Stream'.Seq.destruct_eq_none
  rw [produceInfAuxTrace, Stream'.Seq.corec_eq]
  simp [produceStep]
  rfl

theorem produceInfAuxTrace_cons (ex : ExecutionTrace Expr) (atr : AuxiliaryTrace M)
    (Hcsm : ContinuedSimulation φ ex atr) (ζ : Option Locale) (c : List Expr × State)
    (iex : InfExecutionTrace Expr) (Hvex : ValidInfExec ex (infExecPrepend ζ c iex)) :
    produceInfAuxTrace φ ex atr Hcsm (infExecPrepend ζ c iex) Hvex =
      .cons ((produceInfAuxTraceNextAuxState φ ex atr Hcsm c ζ iex Hvex).2,
        (produceInfAuxTraceNextAuxState φ ex atr Hcsm c ζ iex Hvex).1)
        (produceInfAuxTrace φ (ex :tr[ζ]: c)
          (traceExtendUncurry atr (produceInfAuxTraceNextAuxState φ ex atr Hcsm c ζ iex Hvex))
          (produceInfAuxTraceNextAuxState_continuedSimulation φ ex atr Hcsm c ζ iex Hvex)
          iex Hvex.adjust) := by
  apply Stream'.Seq.destruct_eq_cons
  rw [produceInfAuxTrace, Stream'.Seq.corec_eq]
  unfold produceStep
  split
  · rename_i h; simp at h
  · rename_i ζ' c' iex' h
    simp only [infExecPrepend, Stream'.Seq.destruct_cons] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    rfl

@[rocq_alias trillium.produced_inf_aux_trace_valid_inf]
theorem produced_inf_aux_trace_valid_inf (ex : ExecutionTrace Expr) (atr : AuxiliaryTrace M)
    (Hst : ValidSystemTrace ex atr) (Hcsm : ContinuedSimulation φ ex atr)
    (iex : InfExecutionTrace Expr) (Hvex : ValidInfExec ex iex) :
    ValidInfSystemTrace (ContinuedSimulation φ) ex atr iex
      (produceInfAuxTrace φ ex atr Hcsm iex Hvex) := by
  refine ValidInfSystemTrace.coinduct (ContinuedSimulation φ)
    (fun ex atr iex iatr => ∃ Hcsm Hvex, ValidSystemTrace ex atr ∧
      iatr = produceInfAuxTrace φ ex atr Hcsm iex Hvex) ?_ _ _ _ _ ⟨Hcsm, Hvex, Hst, rfl⟩
  rintro ex atr iex iatr ⟨Hcsm, Hvex, Hst, rfl⟩
  rcases InfList.eq_nil_or_cons iex with rfl | ⟨⟨ζ, c⟩, iex, rfl⟩
  · exact .inl ⟨Hcsm, rfl, produceInfAuxTrace_nil φ ex atr Hcsm Hvex⟩
  · right
    have Hcsm' := produceInfAuxTraceNextAuxState_continuedSimulation φ ex atr Hcsm c ζ iex Hvex
    obtain ⟨-, c0, Hc0, Hstep, -⟩ := Hvex.cons_inv
    refine ⟨c0, c, (produceInfAuxTraceNextAuxState φ ex atr Hcsm c ζ iex Hvex).1, iex, _, ζ,
      (produceInfAuxTraceNextAuxState φ ex atr Hcsm c ζ iex Hvex).2, Hcsm, Hc0, Hstep,
      ⟨Hcsm', Hvex.adjust, Hst.extend Hc0 Hstep, rfl⟩, rfl, produceInfAuxTrace_cons ..⟩

end inf_simulation

end Trillium
