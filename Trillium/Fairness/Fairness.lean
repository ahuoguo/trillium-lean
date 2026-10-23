/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.Fairness.Inftraces
import Trillium.Fairness.TraceLookup
import Trillium.Fairness.TraceUtils
import Trillium.Fairness.UtilsLogic
import Trillium.ProgramLogic.Traces
import Trillium.ProgramLogic.AdequacyLocales
import Trillium.Std.Maps

/-!
# Fair models and fairness of traces
Port of `fairness/fairness.v`.

## Fair models

`FairModel` (Rocq record `FairModel`) is a structure with a type of states `fmstate` (a
`FairModel` coerces to it, Rocq `fmstate :>`), a type of roles `fmrole`, a transition relation
`fmtrans : fmstate → Option fmrole → fmstate → Prop`, the live roles of each state
`liveRoles : fmstate → GSet fmrole` and `fm_live_spec`.

Instance fields (all registered as global instances):
* `fmstate_eqdec : DecidableEq fmstate`, `fmstate_inhabited : Inhabited fmstate`,
  `fmrole_eqdec : DecidableEq fmrole`, `fmrole_inhabited : Inhabited fmrole`;
* Rocq's `fmrole_countable : Countable fmrole` is replaced by the three instances needed by
  `Trillium.GSet`/`Trillium.GMap` keys: `fmrole_ord : Ord fmrole`,
  `fmrole_transOrd : Std.TransOrd fmrole`, `fmrole_lawfulEqOrd : Std.LawfulEqOrd fmrole`
  (the only use of countability in Trillium is to build gsets/gmaps of roles). For a role type
  with an `Encodable` instance, use `Trillium.ordOfEncodable`,
  `Trillium.transOrd_ordOfEncodable` and `Trillium.lawfulEqOrd_ordOfEncodable`.

`FairModel.toModel` (Rocq `fair_model_model`) is the underlying `Trillium.Model`.

## Fairness

* `fairByGen`, `fairBy` (Rocq `fair_by_gen`, `fair_by`) and their variants on lookups;
* `Extrace Expr` (Rocq `extrace Λ`): traces of configurations labelled by `Option Locale`;
  `ExtraceValid` (Rocq's `CoInductive extrace_valid`) is a Lean `coinductive` predicate;
  `fairEx` (Rocq `fair_ex`);
* `Mtrace M` (Rocq `mtrace M`), `fairModelTrace` (Rocq `fair_model_trace`), `MtraceValid`.

Rocq's `from_option f d o` is `o.elim d f`; `ClassicalFacts.Minimal P m` is
`IsLeast {d | P d} m`. Decidability hypotheses that are only used to find minimal elements are
dropped (Lean proofs use classical logic).
-/

namespace Trillium.Fairness

open Trace Trillium

/-- A fair model: a labelled transition system whose labels are optional roles, with the set of
roles enabled ("live") in each state. -/
@[rocq_alias trillium.fairness.FairModel]
structure FairModel where
  /-- The states of the model. -/
  fmstate : Type
  [fmstate_eqdec : DecidableEq fmstate]
  [fmstate_inhabited : Inhabited fmstate]
  /-- The roles of the model. -/
  fmrole : Type
  [fmrole_eqdec : DecidableEq fmrole]
  /-- Order on roles, needed for `GSet fmrole` (replaces Rocq's `fmrole_countable`). -/
  [fmrole_ord : Ord fmrole]
  [fmrole_transOrd : Std.TransOrd fmrole]
  [fmrole_lawfulEqOrd : Std.LawfulEqOrd fmrole]
  [fmrole_inhabited : Inhabited fmrole]
  /-- The transition relation. -/
  fmtrans : fmstate → Option fmrole → fmstate → Prop
  /-- The roles that are live in a state. -/
  liveRoles : fmstate → GSet fmrole
  fm_live_spec : ∀ s ρ s', fmtrans s (some ρ) s' → ρ ∈ liveRoles s


-- The fields correspond to the Rocq record fields of the same names (`live_roles` is
-- `liveRoles`, `fmrole_countable` is replaced by `fmrole_ord`/`fmrole_transOrd`/
-- `fmrole_lawfulEqOrd`); record fields are not tracked by the correspondence check.

attribute [instance] FairModel.fmstate_eqdec FairModel.fmstate_inhabited FairModel.fmrole_eqdec
  FairModel.fmrole_ord FairModel.fmrole_transOrd FairModel.fmrole_lawfulEqOrd
  FairModel.fmrole_inhabited

instance : CoeSort FairModel Type := ⟨FairModel.fmstate⟩

/-- The model underlying a fair model (Rocq `fair_model_model`). -/
@[rocq_alias trillium.fairness.fair_model_model]
def FairModel.toModel (FM : FairModel) : Model where
  mstate := FM.fmstate
  mlabel := Option FM.fmrole
  mtrans := FM.fmtrans

/-! ## Generalized fairness -/

section GeneralizedFairness

variable {S L T : Type _}
variable (localeProp : T → S → Prop) (doesStep : T → S → Option (L × S) → Prop)

@[rocq_alias trillium.fairness.fairness_sat_gen]
def fairnessSatGen (t : T) (s : S) (step : Option (L × S)) : Prop :=
  ¬ localeProp t s ∨ doesStep t s step

/-- Whenever `t` is enabled (`localeProp`), it is eventually disabled or takes a step. -/
@[rocq_alias trillium.fairness.fair_by_gen]
def fairByGen (t : T) (otr : Trace S L) : Prop :=
  ∀ n, predAt otr n (fun c _ => localeProp t c) →
    ∃ m s step, otr !! (n + m) = some (s, step) ∧ fairnessSatGen localeProp doesStep t s step

@[rocq_alias trillium.fairness.fair_by_gen_after]
theorem fair_by_gen_after (t : T) (tr tr' : Trace S L) (k : Nat) :
    after k tr = some tr' → fairByGen localeProp doesStep t tr →
      fairByGen localeProp doesStep t tr' := by
  intro Haf Hf n Hp
  have Hp' : predAt tr (k + n) (fun c _ => localeProp t c) := by
    rw [pred_at_sum, Haf]; exact Hp
  obtain ⟨m, s, step, STEP, SAT⟩ := Hf (k + n) Hp'
  refine ⟨m, s, step, ?_, SAT⟩
  rw [trace_lookup_after tr tr' k Haf, ← Nat.add_assoc]
  exact STEP

@[rocq_alias trillium.fairness.fair_by_gen_cons]
theorem fair_by_gen_cons (t : T) (c : S) (tid' : L) (r : Trace S L) :
    fairByGen localeProp doesStep t (c -[tid']-> r) → fairByGen localeProp doesStep t r :=
  fair_by_gen_after localeProp doesStep t (c -[tid']-> r) r 1 (by simp)

@[rocq_alias trillium.fairness.fair_by_gen_cons_forall]
theorem fair_by_gen_cons_forall (δ : S) (ℓ' : L) (r : Trace S L) :
    (∀ ℓ, fairByGen localeProp doesStep ℓ (δ -[ℓ']-> r)) →
      (∀ ℓ, fairByGen localeProp doesStep ℓ r) :=
  fun H ℓ => fair_by_gen_cons localeProp doesStep ℓ δ ℓ' r (H ℓ)

/-- `fairByGen` stated with lookups. -/
@[rocq_alias trillium.fairness.fair_by_gen']
def fairByGen' (t : T) (otr : Trace S L) : Prop :=
  ∀ n, (otr S!! n).elim False (localeProp t) →
    ∃ m s' step, otr !! (n + m) = some (s', step) ∧ fairnessSatGen localeProp doesStep t s' step

/-- `fairByGen'` where the step is the first one satisfying the fairness condition. -/
@[rocq_alias trillium.fairness.fair_by_gen'_strong]
def fairByGenStrong (t : T) (otr : Trace S L) : Prop :=
  ∀ n, (otr S!! n).elim False (localeProp t) →
    ∃ m s' step, otr !! (n + m) = some (s', step) ∧
      fairnessSatGen localeProp doesStep t s' step ∧
      (∀ k sk stepk, n ≤ k ∧ k < n + m → otr !! k = some (sk, stepk) →
        ¬ fairnessSatGen localeProp doesStep t sk stepk)

/-- `predAt` of a state predicate in terms of `S!!`. -/
private theorem predAt_state_iff (otr : Trace S L) (n : Nat) (P : S → Prop) :
    predAt otr n (fun c _ => P c) ↔ (otr S!! n).elim False P := by
  rw [pred_at_trace_lookup]
  cases otr S!! n <;> simp

@[rocq_alias trillium.fairness.fair_by_gen_equiv]
theorem fair_by_gen_equiv (t : T) (otr : Trace S L) :
    fairByGen localeProp doesStep t otr ↔ fairByGen' localeProp doesStep t otr := by
  unfold fairByGen fairByGen'
  simp only [predAt_state_iff]

/-- Rocq's version assumes decidability of `localeProp` and `doesStep`; it is not needed here. -/
@[rocq_alias trillium.fairness.fair_by_gen'_strong_equiv]
theorem fair_by_gen'_strong_equiv (t : T) (otr : Trace S L) :
    fairByGen' localeProp doesStep t otr ↔ fairByGenStrong localeProp doesStep t otr := by
  unfold fairByGen' fairByGenStrong
  constructor
  · intro FAIR n EN
    obtain ⟨m_, STEP⟩ := FAIR n EN
    classical
    obtain ⟨m, ⟨s, step, NTH, SAT⟩, MINm⟩ := min_prop_dec
      (fun k => ∃ s step, otr !! (n + k) = some (s, step) ∧
        fairnessSatGen localeProp doesStep t s step) m_ STEP
    refine ⟨m, s, step, NTH, SAT, ?_⟩
    rintro k sk stepk ⟨LE, LT⟩ KTH SATk
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le LE
    have := MINm ⟨sk, stepk, KTH, SATk⟩
    omega
  · intro FAIR n EN
    obtain ⟨m, s, step, NTH, SAT, -⟩ := FAIR n EN
    exact ⟨m, s, step, NTH, SAT⟩

/-- Rocq's `Proper` instance `fair_by_gen_Proper`: `fairByGen` respects pointwise equivalence
of its parameters. -/
@[rocq_alias trillium.fairness.fair_by_gen_Proper]
theorem fair_by_gen_congr {localeProp₁ localeProp₂ : T → S → Prop}
    {doesStep₁ doesStep₂ : T → S → Option (L × S) → Prop}
    (LOC_IFF : ∀ t s, localeProp₁ t s ↔ localeProp₂ t s)
    (STEP_IFF : ∀ t s step, doesStep₁ t s step ↔ doesStep₂ t s step) (t : T) (otr : Trace S L) :
    fairByGen localeProp₁ doesStep₁ t otr ↔ fairByGen localeProp₂ doesStep₂ t otr := by
  obtain rfl : localeProp₁ = localeProp₂ := funext fun t => funext fun s => propext (LOC_IFF t s)
  obtain rfl : doesStep₁ = doesStep₂ :=
    funext fun t => funext fun s => funext fun step => propext (STEP_IFF t s step)
  rfl

end GeneralizedFairness

/-! ## Fairness of locales -/

section LocaleFairness

variable {S L T : Type _}
variable (localeProp : T → S → Prop) (doesStep : T → L → Prop)

@[rocq_alias trillium.fairness.fairness_sat]
def fairnessSat (t : T) (s : S) (ol : Option L) : Prop :=
  ¬ localeProp t s ∨ ∃ ℓ, ol = some ℓ ∧ doesStep t ℓ

/-- Whenever `t` is enabled (`localeProp`), it is eventually disabled or takes a step. -/
@[rocq_alias trillium.fairness.fair_by]
def fairBy (t : T) (otr : Trace S L) : Prop :=
  ∀ n, predAt otr n (fun c _ => localeProp t c) →
    ∃ m, predAt otr (n + m) (fairnessSat localeProp doesStep t)

@[rocq_alias trillium.fairness.fair_by_after]
theorem fair_by_after (t : T) (tr tr' : Trace S L) (k : Nat) :
    after k tr = some tr' → fairBy localeProp doesStep t tr → fairBy localeProp doesStep t tr' := by
  intro Haf Hf n Hp
  have Hp' : predAt tr (k + n) (fun c _ => localeProp t c) := by
    rw [pred_at_sum, Haf]; exact Hp
  obtain ⟨m, Hm⟩ := Hf (k + n) Hp'
  refine ⟨m, ?_⟩
  rw [Nat.add_assoc, pred_at_sum, Haf] at Hm
  exact Hm

@[rocq_alias trillium.fairness.fair_by_cons]
theorem fair_by_cons (t : T) (c : S) (tid' : L) (r : Trace S L) :
    fairBy localeProp doesStep t (c -[tid']-> r) → fairBy localeProp doesStep t r :=
  fair_by_after localeProp doesStep t (c -[tid']-> r) r 1 (by simp)

@[rocq_alias trillium.fairness.fair_by_cons_forall]
theorem fair_by_cons_forall (δ : S) (ℓ' : L) (r : Trace S L) :
    (∀ ℓ, fairBy localeProp doesStep ℓ (δ -[ℓ']-> r)) → (∀ ℓ, fairBy localeProp doesStep ℓ r) :=
  fun H ℓ => fair_by_cons localeProp doesStep ℓ δ ℓ' r (H ℓ)

/-- `fairBy` stated with lookups. -/
@[rocq_alias trillium.fairness.fair_by']
def fairBy' (t : T) (otr : Trace S L) : Prop :=
  ∀ n, (otr S!! n).elim False (localeProp t) →
    ∃ m s', otr S!! (n + m) = some s' ∧ fairnessSat localeProp doesStep t s' (otr L!! (n + m))

/-- `fairBy'` with the minimal such `m`. -/
@[rocq_alias trillium.fairness.fair_by'_strong]
def fairByStrong (t : T) (otr : Trace S L) : Prop :=
  ∀ n, (otr S!! n).elim False (localeProp t) →
    ∃ m, IsLeast {d | ∃ s', otr S!! (n + d) = some s' ∧
      fairnessSat localeProp doesStep t s' (otr L!! (n + d))} m

@[rocq_alias trillium.fairness.fair_by_equiv]
theorem fair_by_equiv (t : T) (otr : Trace S L) :
    fairBy localeProp doesStep t otr ↔ fairBy' localeProp doesStep t otr := by
  unfold fairBy fairBy'
  simp only [predAt_state_iff]
  simp only [pred_at_trace_lookup]

@[rocq_alias trillium.fairness.fairness_sat_dec]
instance fairness_sat_dec [∀ t s, Decidable (localeProp t s)] [∀ t l, Decidable (doesStep t l)] :
    ∀ t s ol, Decidable (fairnessSat localeProp doesStep t s ol) := by
  intro t s ol
  unfold fairnessSat
  cases ol with
  | none => exact decidable_of_iff (¬ localeProp t s) (by simp)
  | some l => exact decidable_of_iff (¬ localeProp t s ∨ doesStep t l) (by simp)

/-- Rocq's version assumes decidability of `fairnessSat`; it is not needed here. -/
@[rocq_alias trillium.fairness.fair_by'_strenghten]
theorem fair_by'_strenghten (t : T) (otr : Trace S L) :
    fairBy' localeProp doesStep t otr ↔ fairByStrong localeProp doesStep t otr := by
  unfold fairBy' fairByStrong
  refine forall_congr' fun n => imp_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨m, EX⟩
    classical
    exact min_prop_dec (fun d => ∃ s', otr S!! (n + d) = some s' ∧
      fairnessSat localeProp doesStep t s' (otr L!! (n + d))) m EX
  · rintro ⟨m, EX, -⟩
    exact ⟨m, EX⟩

/-- Weak fairness: if `t` is eventually always enabled, it takes infinitely many steps. -/
@[rocq_alias trillium.fairness.weakly_fair]
def weaklyFair (t : T) (tr : Trace S L) : Prop :=
  ∀ n, (tr S!! n).isSome →
    -- using `True` as default to support finite traces
    (∀ k, n ≤ k → (tr S!! k).elim True (localeProp t)) →
    ∃ m ℓ, tr L!! (n + m) = some ℓ ∧ doesStep t ℓ

@[rocq_alias trillium.fairness.fair_by'_weakly_fair]
theorem fair_by'_weakly_fair (τ : T) (tr : Trace S L) :
    fairBy' localeProp doesStep τ tr ↔ weaklyFair localeProp doesStep τ tr := by
  unfold fairBy' weaklyFair
  refine forall_congr' fun n => ⟨?_, ?_⟩
  · intro FAIR NTH ALW
    obtain ⟨δ, NTH⟩ := Option.isSome_iff_exists.1 NTH
    have ENn := ALW n le_rfl
    rw [NTH] at ENn FAIR
    obtain ⟨d, δ', MTH, SAT⟩ := FAIR ENn
    rcases SAT with DIS | ⟨ℓ, LBL, STEP⟩
    · have := ALW (n + d) (by omega)
      rw [MTH] at this
      exact (DIS this).elim
    · exact ⟨d, ℓ, LBL, STEP⟩
  · intro FAIR
    cases NTH : tr S!! n with
    | none => intro h; exact h.elim
    | some δ =>
      intro ENn
      by_cases H : ∀ k, n ≤ k → (tr S!! k).elim True (localeProp τ)
      · obtain ⟨m, ℓ, MTHl, STEP⟩ := FAIR (by rw [NTH]; rfl) H
        have := (label_lookup_states tr (n + m)).1 (by rw [MTHl]; rfl)
        obtain ⟨s', MTH⟩ := Option.isSome_iff_exists.1 this.1
        exact ⟨m, s', MTH, .inr ⟨ℓ, MTHl, STEP⟩⟩
      · obtain ⟨m, DIS0⟩ := Classical.not_forall.mp H
        obtain ⟨LE, DIS⟩ := Classical.not_imp.mp DIS0
        clear DIS0
        cases MTH : tr S!! m with
        | none => rw [MTH] at DIS; exact (DIS trivial).elim
        | some s =>
          rw [MTH] at DIS
          obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le LE
          exact ⟨d, s, MTH, .inl DIS⟩

end LocaleFairness

/-! ## Execution traces -/

/-- Traces of configurations of a language, labelled by the locale taking the step (Rocq
`extrace Λ`). -/
@[rocq_alias trillium.fairness.extrace]
abbrev Extrace (Expr : Type _) {Val Ectx State Locale : Type _}
    [Language Expr Val Ectx State Locale] : Type _ :=
  Trace (List Expr × State) (Option Locale)

section exec_trace

variable {Expr Val Ectx State Locale : Type _} [Language Expr Val Ectx State Locale]

/-- The thread with locale `ζ` exists in `c` and is not a value. -/
@[rocq_alias trillium.fairness.locale_enabled]
def localeEnabled [DecidableEq Locale] (ζ : Locale) (c : List Expr × State) : Prop :=
  ∃ e, fromLocale c.1 ζ = some e ∧ toVal e = none

@[rocq_alias trillium.fairness.tid_match]
def tidMatch (ζ : Locale) (oζ' : Option Locale) : Prop := oζ' = some ζ

/-- Fairness of an execution trace w.r.t. the locale `ζ`. -/
@[rocq_alias trillium.fairness.fair_ex]
def fairEx [DecidableEq Locale] (ζ : Locale) (extr : Extrace Expr) : Prop :=
  fairBy (localeEnabled (Expr := Expr)) tidMatch ζ extr

/-- Every step of the execution trace is a `LocaleStep` (Rocq's `CoInductive extrace_valid`). -/
@[rocq_alias trillium.fairness.extrace_valid]
coinductive ExtraceValid : Extrace Expr → Prop where
  | singleton (c : List Expr × State) : ExtraceValid (Trace.singl c)
  | cons (c : List Expr × State) (oζ : Option Locale) (tr : Extrace Expr) :
      Language.LocaleStep c oζ tr.first → ExtraceValid tr → ExtraceValid (Trace.cons c oζ tr)

/-- Inversion for `ExtraceValid`. -/
theorem ExtraceValid.inv {tr : Extrace Expr} (h : ExtraceValid tr) :
    (∃ c, tr = Trace.singl c) ∨
      ∃ c oζ r, Language.LocaleStep c oζ r.first ∧ ExtraceValid r ∧ tr = Trace.cons c oζ r := by
  cases h with
  | singleton c => exact .inl ⟨c, rfl⟩
  | cons c oζ r h1 h2 => exact .inr ⟨c, oζ, r, h1, h2, rfl⟩

theorem ExtraceValid.cons_inv {c : List Expr × State} {oζ : Option Locale} {r : Extrace Expr}
    (h : ExtraceValid (Trace.cons c oζ r)) :
    Language.LocaleStep c oζ r.first ∧ ExtraceValid r := by
  rcases h.inv with ⟨_, e⟩ | ⟨c', oζ', r', h1, h2, e⟩
  · exact absurd e cons_ne_singl
  · obtain ⟨rfl, rfl, rfl⟩ := cons_inj.1 e
    exact ⟨h1, h2⟩

/-- `ExtraceValid` is `TraceValid` for the relation `LocaleStep`. -/
theorem extraceValid_iff_traceValid (tr : Extrace Expr) :
    ExtraceValid tr ↔ TraceValid (Language.LocaleStep (Expr := Expr)) tr := by
  constructor
  · intro h
    refine TraceValid.coinduct _ ExtraceValid ?_ tr h
    intro tr h
    rcases h.inv with ⟨c, rfl⟩ | ⟨c, oζ, r, h1, h2, rfl⟩
    · exact .inl ⟨c, rfl⟩
    · exact .inr ⟨c, oζ, r, h1, h2, rfl⟩
  · intro h
    refine ExtraceValid.coinduct (fun tr => TraceValid (Language.LocaleStep (Expr := Expr)) tr)
      ?_ tr h
    intro tr h
    rcases h.inv with ⟨c, rfl⟩ | ⟨c, oζ, r, h1, h2, rfl⟩
    · exact .inl ⟨c, rfl⟩
    · exact .inr ⟨c, oζ, r, h1, h2, rfl⟩

@[rocq_alias trillium.fairness.to_trace_preserves_validity]
theorem to_trace_preserves_validity (ex : ExecutionTrace Expr) (iex : InfExecutionTrace Expr) :
    ExtraceValid (toTrace ex.last iex) → ValidExec ex → ValidInfExec ex iex := by
  intro Hexval Hval
  refine ValidInfExec.coinduct
    (fun ex iex => ExtraceValid (toTrace ex.last iex) ∧ ValidExec ex) ?_ ex iex ⟨Hexval, Hval⟩
  rintro ex iex ⟨Hexval, Hval⟩
  rcases InfList.eq_nil_or_cons iex with rfl | ⟨⟨ζ, c⟩, iex, rfl⟩
  · exact .inl ⟨Hval, rfl⟩
  · rw [toTrace_cons] at Hexval
    obtain ⟨Hstep, Hexval'⟩ := Hexval.cons_inv
    refine .inr ⟨ex.last, c, iex, ζ, Hval, FiniteTrace.endsIn_iff.2 rfl, Hstep, ⟨?_, ?_⟩, rfl⟩
    · simpa using Hexval'
    · exact Hval.extend (FiniteTrace.endsIn_iff.2 rfl) Hstep

@[rocq_alias trillium.fairness.from_trace_preserves_validity]
theorem from_trace_preserves_validity (extr : Extrace Expr) (ex : ExecutionTrace Expr) :
    ExtraceValid extr → ValidExec ex → ex.last = extr.first →
      ValidInfExec ex (fromTrace extr) := by
  intro Hexval Hval Heq
  refine ValidInfExec.coinduct
    (fun ex iex => ∃ extr, iex = fromTrace extr ∧ ExtraceValid extr ∧ ValidExec ex ∧
      ex.last = extr.first) ?_ ex _ ⟨extr, rfl, Hexval, Hval, Heq⟩
  rintro ex _ ⟨extr, rfl, Hexval, Hval, Heq⟩
  cases extr with
  | singl c => exact .inl ⟨Hval, rfl⟩
  | cons c ζ tr =>
    obtain ⟨Hstep, Hexval'⟩ := Hexval.cons_inv
    simp only [first_cons] at Heq
    refine .inr ⟨c, tr.first, fromTrace tr, ζ, Hval, FiniteTrace.endsIn_iff.2 Heq, Hstep,
      ⟨tr, rfl, Hexval', Hval.extend (FiniteTrace.endsIn_iff.2 Heq) Hstep, by simp⟩, ?_⟩
    rw [fromTrace_cons]

@[rocq_alias trillium.fairness.from_trace_preserves_validity_singleton]
theorem from_trace_preserves_validity_singleton (extr : Extrace Expr) :
    ExtraceValid extr →
      ValidInfExec (FiniteTrace.singleton extr.first : ExecutionTrace Expr) (fromTrace extr) :=
  fun h => from_trace_preserves_validity extr _ h (ValidExec.singleton _) rfl

/-- Valid, fair execution traces terminate. -/
@[rocq_alias trillium.fairness.extrace_fairly_terminating]
def ExtraceFairlyTerminating [DecidableEq Locale] (extr : Extrace Expr) : Prop :=
  ExtraceValid extr → (∀ tid, fairEx tid extr) → terminatingTrace extr

end exec_trace

/-! ## Model traces -/

/-- Traces of a fair model (Rocq `mtrace M`). -/
@[rocq_alias trillium.fairness.mtrace]
abbrev Mtrace (M : FairModel) : Type := Trace M.fmstate (Option M.fmrole)

section model_traces

variable {M : FairModel}

@[rocq_alias trillium.fairness.role_enabled_model]
def roleEnabledModel (ρ : M.fmrole) (s : M.fmstate) : Prop := ρ ∈ M.liveRoles s

@[rocq_alias trillium.fairness.rem_dec]
instance rem_dec : ∀ (ρ : M.fmrole) (st : M.fmstate), Decidable (roleEnabledModel ρ st) :=
  fun ρ st => inferInstanceAs (Decidable (ρ ∈ M.liveRoles st))

@[rocq_alias trillium.fairness.role_match]
def roleMatch (ρ : M.fmrole) (oρ' : Option M.fmrole) : Prop := oρ' = some ρ

/-- Fairness of a model trace w.r.t. the role `ρ`. -/
@[rocq_alias trillium.fairness.fair_model_trace]
def fairModelTrace (ρ : M.fmrole) (mtr : Mtrace M) : Prop :=
  fairBy roleEnabledModel roleMatch ρ mtr

/-- Every step of the model trace is a transition of the model. -/
@[rocq_alias trillium.fairness.mtrace_valid]
abbrev MtraceValid (tr : Mtrace M) : Prop := TraceValid M.fmtrans tr

end model_traces

/-- The live roles are exactly the roles that can take a step. -/
@[rocq_alias trillium.fairness.FM_strong_lr]
def FMStrongLr (FM : FairModel) : Prop :=
  ∀ st ρ, ρ ∈ FM.liveRoles st ↔ ∃ st', FM.fmtrans st (some ρ) st'

end Trillium.Fairness
