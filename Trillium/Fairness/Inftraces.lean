/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.Fairness.UtilsLogic
import Trillium.Fairness.UtilsRelations
import Trillium.Traces.Trace
import Iris.Algebra.BigOp
import Mathlib.Data.Seq.Defs
import Mathlib.Order.WellFounded
import Mathlib.Order.Prod.Lex.Basic

/-!
# Possibly infinite traces
Port of `fairness/inftraces.v`.

## The trace type

Rocq's coinductive `trace S L` (`tr_singl s | tr_cons s ℓ tr`) is the structure
`Trillium.Fairness.Trace S L`, made of the first state `first` and the possibly-infinite
sequence `steps : Stream'.Seq (L × S)` of the following (label, state) pairs:
* `Trace.singl s` (notation `⟨s⟩ₜ`) has no steps;
* `Trace.cons s ℓ tr` (notation `s -[ℓ]-> tr`) is `⟨s, Seq.cons (ℓ, tr.first) tr.steps⟩`.
The notations are `scoped` in `Trillium.Fairness`.

Working with traces:
* **case analysis**: `cases tr` (the eliminator `Trace.casesOn'` is registered as the default
  `cases` eliminator) produces the goals `singl s` and `cons s ℓ r`; `Trace.dest` exposes the
  head of a trace as a sum, with `simp` lemmas `Trace.dest_singl`/`Trace.dest_cons`;
* **injectivity**: `Trace.cons_inj`, `Trace.singl_inj`, `Trace.singl_ne_cons`,
  `Trace.cons_ne_singl` (all `simp`);
* **corecursion** (Rocq `CoFixpoint`): `Trace.corec f b` with `Trace.corec_eq`;
* **coinduction on equality**: `Trace.eq_of_bisim` (Rocq proofs by `cofix` returning equalities);
* **coinductive predicates** (Rocq `CoInductive` and paco definitions) are Lean `coinductive`
  predicates (`TraceValid`, `TracesMatch`, `ExecTraceMatch`): build them with their
  `.coinduct` principle (Rocq `cofix`/`pcofix`) and invert them with the provided `*_inv` lemmas
  (Rocq `inversion`/`punfold`).

`trfirst tr` is the field `tr.first`. `is_Some o` is `o.isSome`.
`inflist (L * S)` is `Stream'.Seq (L × S)`; with this representation `to_trace s il` is just
`⟨s, il⟩` and `from_trace tr` is `tr.steps`.
Rocq's `lexprod` is Mathlib's `Prod.Lex`.
-/

namespace Trillium.Fairness

open Stream'

/-- Possibly infinite traces with states `S` and labels `L` (Rocq's coinductive `trace S L`). -/
@[rocq_alias trillium.fairness.trace, ext]
structure Trace (S : Type _) (L : Type _) where
  /-- The first state (Rocq `trfirst`). -/
  first : S
  /-- The (label, state) pairs of the following steps. -/
  steps : Seq (L × S)

attribute [rocq_alias trillium.fairness.trfirst] Trace.first

namespace Trace

variable {S L : Type _}

/-- The trace made of a single state (Rocq `tr_singl`). -/
def singl (s : S) : Trace S L := ⟨s, .nil⟩

/-- A step from `s` with label `ℓ`, followed by `tr` (Rocq `tr_cons`). -/
def cons (s : S) (ℓ : L) (tr : Trace S L) : Trace S L := ⟨s, .cons (ℓ, tr.first) tr.steps⟩

@[inherit_doc] scoped notation:max "⟨" s "⟩ₜ" => Trace.singl s
@[inherit_doc Trace.cons]
scoped syntax:75 term:76 " -[" term "]-> " term:75 : term
scoped macro_rules | `($s -[ $ℓ ]-> $r) => `(Trace.cons $s $ℓ $r)

/-- Unexpander for `Trace.cons`. -/
@[scoped app_unexpander Trace.cons]
def unexpandCons : Lean.PrettyPrinter.Unexpander
  | `($_ $s $ℓ $r) => `($s -[ $ℓ ]-> $r)
  | _ => throw ()

@[simp] theorem first_singl (s : S) : (singl s : Trace S L).first = s := rfl
@[simp] theorem first_cons (s : S) (ℓ : L) (r : Trace S L) : (cons s ℓ r).first = s := rfl

/-- The head of a trace: either it is a single state, or a first step followed by a trace. -/
def dest (tr : Trace S L) : S ⊕ (S × L × Trace S L) :=
  match tr.steps.destruct with
  | none => .inl tr.first
  | some ((ℓ, s'), rest) => .inr (tr.first, ℓ, ⟨s', rest⟩)

@[simp] theorem dest_singl (s : S) : (singl s : Trace S L).dest = .inl s := by
  simp [dest, singl, Seq.destruct_nil]

@[simp] theorem dest_cons (s : S) (ℓ : L) (r : Trace S L) : (cons s ℓ r).dest = .inr (s, ℓ, r) := by
  simp [dest, cons, Seq.destruct_cons]

/-- Inverse of `dest`. -/
def ofDest : S ⊕ (S × L × Trace S L) → Trace S L
  | .inl s => singl s
  | .inr (s, ℓ, r) => cons s ℓ r

@[simp] theorem ofDest_dest (tr : Trace S L) : ofDest tr.dest = tr := by
  obtain ⟨s, steps⟩ := tr
  cases steps with
  | nil => rfl
  | cons a rest =>
    obtain ⟨ℓ, s'⟩ := a
    simp [dest, ofDest, cons, Seq.destruct_cons]

theorem dest_injective : Function.Injective (dest : Trace S L → _) := fun t₁ t₂ h => by
  rw [← ofDest_dest t₁, ← ofDest_dest t₂, h]

/-- Rocq's `trace_unfold_fold`: a trace is equal to its unfolding. -/
@[rocq_alias trillium.fairness.trace_unfold_fold]
theorem trace_unfold_fold (tr : Trace S L) :
    tr = match tr.dest with
      | .inl s => singl s
      | .inr (s, ℓ, r) => cons s ℓ r :=
  (ofDest_dest tr).symm

@[simp] theorem singl_inj {s s' : S} : (singl s : Trace S L) = singl s' ↔ s = s' :=
  ⟨fun h => by simpa using congrArg dest h, fun h => h ▸ rfl⟩

@[simp] theorem cons_inj {s s' : S} {ℓ ℓ' : L} {r r' : Trace S L} :
    cons s ℓ r = cons s' ℓ' r' ↔ s = s' ∧ ℓ = ℓ' ∧ r = r' := by
  constructor
  · intro h; simpa using congrArg dest h
  · rintro ⟨rfl, rfl, rfl⟩; rfl

@[simp] theorem singl_ne_cons {s s' : S} {ℓ : L} {r : Trace S L} : singl s ≠ cons s' ℓ r :=
  fun h => by simpa using congrArg dest h

@[simp] theorem cons_ne_singl {s s' : S} {ℓ : L} {r : Trace S L} : cons s' ℓ r ≠ singl s :=
  fun h => singl_ne_cons h.symm

private def casesAux {motive : Trace S L → Sort _} (singl : ∀ s, motive (singl s))
    (cons : ∀ s ℓ r, motive (cons s ℓ r)) : (d : S ⊕ (S × L × Trace S L)) → motive (ofDest d)
  | .inl s => singl s
  | .inr (s, ℓ, r) => cons s ℓ r

/-- Case analysis on a trace: it is either `singl s` or `cons s ℓ r`. This is the default
eliminator for `cases tr`. -/
@[elab_as_elim, cases_eliminator]
def casesOn' {motive : Trace S L → Sort _} (tr : Trace S L) (singl : ∀ s, motive (singl s))
    (cons : ∀ s ℓ r, motive (cons s ℓ r)) : motive tr :=
  ofDest_dest tr ▸ casesAux singl cons tr.dest

/-- Every trace is a `singl` or a `cons`. -/
theorem singl_or_cons (tr : Trace S L) :
    (∃ s, tr = singl s) ∨ ∃ s ℓ r, tr = cons s ℓ r := by
  cases tr with
  | singl s => exact .inl ⟨s, rfl⟩
  | cons s ℓ r => exact .inr ⟨s, ℓ, r, rfl⟩

/-- The first element of an unfolding step. -/
private def sumHead {β : Type _} : S ⊕ (S × L × β) → S
  | .inl s => s
  | .inr (s, _, _) => s

/-- Corecursor for traces (to define Rocq `CoFixpoint`s returning traces). -/
def corec {β : Type _} (f : β → S ⊕ (S × L × β)) (b : β) : Trace S L where
  first := sumHead (f b)
  steps := Seq.corec (fun b => match f b with
    | .inl _ => none
    | .inr (_, ℓ, b') => some ((ℓ, sumHead (f b')), b')) b

theorem corec_eq {β : Type _} (f : β → S ⊕ (S × L × β)) (b : β) :
    corec f b = match f b with
      | .inl s => singl s
      | .inr (s, ℓ, b') => cons s ℓ (corec f b') := by
  rcases h : f b with s | ⟨s, ℓ, b'⟩
  · refine Trace.ext ?_ ?_
    · simp [corec, h, sumHead, singl]
    · simp only [corec, singl]
      exact Seq.corec_nil _ _ (by simp [h])
  · refine Trace.ext ?_ ?_
    · simp [corec, h, sumHead, cons]
    · simp only [corec, cons]
      exact Seq.corec_cons (by simp [h])

/-- Coinduction principle for equality of traces (bisimulation). -/
theorem eq_of_bisim (R : Trace S L → Trace S L → Prop)
    (step : ∀ t₁ t₂, R t₁ t₂ →
      (∃ s, t₁ = singl s ∧ t₂ = singl s) ∨
      ∃ s ℓ r₁ r₂, t₁ = cons s ℓ r₁ ∧ t₂ = cons s ℓ r₂ ∧ R r₁ r₂)
    {t₁ t₂ : Trace S L} (h : R t₁ t₂) : t₁ = t₂ := by
  have first_eq : ∀ t₁ t₂, R t₁ t₂ → t₁.first = t₂.first := by
    intro t₁ t₂ h
    rcases step t₁ t₂ h with ⟨s, rfl, rfl⟩ | ⟨s, ℓ, r₁, r₂, rfl, rfl, _⟩ <;> rfl
  refine Trace.ext (first_eq _ _ h) ?_
  · refine Seq.eq_of_bisim' (fun u v => ∃ t₁ t₂, R t₁ t₂ ∧ t₁.steps = u ∧ t₂.steps = v)
      ⟨t₁, t₂, h, rfl, rfl⟩ ?_
    rintro _ _ ⟨t₁, t₂, h, rfl, rfl⟩
    rcases step t₁ t₂ h with ⟨s, rfl, rfl⟩ | ⟨s, ℓ, r₁, r₂, rfl, rfl, hr⟩
    · exact .inl ⟨rfl, rfl⟩
    · refine .inr ⟨(ℓ, r₁.first), r₁.steps, r₂.steps, rfl, ?_, r₁, r₂, hr, rfl, rfl⟩
      simp only [cons, first_eq r₁ r₂ hr]

/-- The label of the first step of a trace, if any. -/
def label? (tr : Trace S L) : Option L :=
  match tr.dest with
  | .inl _ => none
  | .inr (_, ℓ, _) => some ℓ

@[simp] theorem label?_singl (s : S) : (singl s : Trace S L).label? = none := by
  unfold label?; rw [dest_singl]

@[simp] theorem label?_cons (s : S) (ℓ : L) (r : Trace S L) : (cons s ℓ r).label? = some ℓ := by
  unfold label?; rw [dest_cons]

end Trace

open Trace

section traces

variable {S T : Type _}

@[rocq_alias trillium.fairness.pred_first_trace]
theorem pred_first_trace (tr : Trace S T) (P : S → Prop) :
    (match tr.dest with
      | .inl s => P s
      | .inr (s, _, _) => P s) ↔ P tr.first := by
  cases tr <;> simp

end traces

section after

variable {St L : Type _}

/-- The suffix of a trace after `n` steps, if the trace has at least `n` steps. -/
@[rocq_alias trillium.fairness.after]
def after : Nat → Trace St L → Option (Trace St L)
  | 0, t => some t
  | n + 1, t =>
    match t.dest with
    | .inl _ => none
    | .inr (_, _, xs) => after n xs

@[rocq_alias trillium.fairness.after_0_id, simp]
theorem after_0_id (tr : Trace St L) : after 0 tr = some tr := rfl

@[simp] theorem after_succ_singl (n : Nat) (s : St) : after (n + 1) (singl s : Trace St L) = none := by
  simp [after]

@[simp] theorem after_succ_cons (n : Nat) (s : St) (ℓ : L) (r : Trace St L) :
    after (n + 1) (cons s ℓ r) = after n r := by
  simp [after]

/-- `P` holds at the `n`-th position of `tr`, of the state and the label of the next step
(`none` if it is the last state). -/
@[rocq_alias trillium.fairness.pred_at]
def predAt (tr : Trace St L) (n : Nat) (P : St → Option L → Prop) : Prop :=
  match after n tr with
  | none => False
  | some t => P t.first t.label?

theorem predAt_some {tr t : Trace St L} {n : Nat} (h : after n tr = some t)
    (P : St → Option L → Prop) : predAt tr n P ↔ P t.first t.label? := by
  simp [predAt, h]

theorem predAt_none {tr : Trace St L} {n : Nat} (h : after n tr = none)
    (P : St → Option L → Prop) : ¬ predAt tr n P := by
  simp [predAt, h]

@[simp] theorem predAt_singl_0 (s : St) (P : St → Option L → Prop) :
    predAt (singl s) 0 P ↔ P s none := by
  simp [predAt]

@[rocq_alias trillium.fairness.after_sum]
theorem after_sum (m : Nat) : ∀ k (tr : Trace St L),
    after (k + m) tr =
      match after m tr with
      | none => none
      | some tr' => after k tr' := by
  induction m with
  | zero => intro k tr; rfl
  | succ m IH =>
    intro k tr
    rw [show k + (m + 1) = (k + m) + 1 by omega]
    cases tr with
    | singl s => simp
    | cons s ℓ r => simp [IH]

@[rocq_alias trillium.fairness.after_sum']
theorem after_sum' (m : Nat) : ∀ k (tr : Trace St L),
    after (k + m) tr =
      match after k tr with
      | none => none
      | some tr' => after m tr' := by
  intro k tr
  rw [Nat.add_comm]
  exact after_sum k m tr

@[rocq_alias trillium.fairness.after_S_tr_cons]
theorem after_S_tr_cons (tr : Trace St L) (n : Nat) (s : St) (ℓ : L) (atr : Trace St L)
    (AFTER : after n tr = some (cons s ℓ atr)) : after (n + 1) tr = some atr := by
  rw [after_sum' 1 n, AFTER]
  rfl

@[rocq_alias trillium.fairness.pred_at_sum]
theorem pred_at_sum (P : St → Option L → Prop) (n m : Nat) (tr : Trace St L) :
    predAt tr (n + m) P ↔
      match after n tr with
      | none => False
      | some tr' => predAt tr' m P := by
  rw [predAt, after_sum' m n]
  cases after n tr <;> rfl

@[rocq_alias trillium.fairness.pred_at_sum']
theorem pred_at_sum' (P : St → Option L → Prop) (n m : Nat) (tr : Trace St L) :
    predAt tr (n + m) P ↔
      match after m tr with
      | none => False
      | some tr' => predAt tr' n P := by
  rw [predAt, after_sum m n]
  cases after m tr <;> rfl

@[rocq_alias trillium.fairness.pred_at_0, simp]
theorem pred_at_0 (s : St) (ℓ : L) (r : Trace St L) (P : St → Option L → Prop) :
    predAt (cons s ℓ r) 0 P ↔ P s (some ℓ) := by
  simp [predAt]

@[rocq_alias trillium.fairness.pred_at_S, simp]
theorem pred_at_S (s : St) (ℓ : L) (r : Trace St L) (n : Nat) (P : St → Option L → Prop) :
    predAt (cons s ℓ r) (n + 1) P ↔ predAt r n P := by
  simp [predAt]

@[rocq_alias trillium.fairness.pred_at_state_trfirst]
theorem pred_at_state_trfirst (tr : Trace St L) (P : St → Prop) :
    predAt tr 0 (fun st _ => P st) ↔ P tr.first := by
  simp [predAt]

@[rocq_alias trillium.fairness.pred_at_dec]
instance pred_at_dec (P : St → Option L → Prop) [DEC : ∀ st ro, Decidable (P st ro)]
    (tr : Trace St L) (i : Nat) : Decidable (predAt tr i P) := by
  unfold predAt
  split <;> infer_instance

@[rocq_alias trillium.fairness.pred_at_or]
theorem pred_at_or (P1 P2 : St → Option L → Prop) (tr : Trace St L) (i : Nat) :
    predAt tr i P1 ∨ predAt tr i P2 ↔ predAt tr i (fun x y => P1 x y ∨ P2 x y) := by
  unfold predAt
  split <;> simp

@[rocq_alias trillium.fairness.pred_at_ex]
theorem pred_at_ex {T : Type _} (P : T → St → Option L → Prop) (tr : Trace St L) (n : Nat) :
    predAt tr n (fun s ol => ∃ t, P t s ol) ↔ ∃ t, predAt tr n (P t) := by
  unfold predAt
  split <;> simp

@[rocq_alias trillium.fairness.pred_at_impl]
theorem pred_at_impl (P Q : St → Option L → Prop) (IMPL : ∀ s ol, P s ol → Q s ol) :
    ∀ tr i, predAt tr i P → predAt tr i Q := by
  intro tr i
  unfold predAt
  split
  · exact id
  · exact IMPL _ _

@[rocq_alias trillium.fairness.pred_at_iff]
theorem pred_at_iff (P Q : St → Option L → Prop) (IFF : ∀ s ol, P s ol ↔ Q s ol) :
    ∀ tr i, predAt tr i P ↔ predAt tr i Q := by
  intro tr i
  unfold predAt
  split
  · exact .rfl
  · exact IFF _ _

/-- The trace has infinitely many steps. -/
@[rocq_alias trillium.fairness.infinite_trace]
def infiniteTrace (tr : Trace St L) : Prop := ∀ n, (after n tr).isSome

/-- The trace has finitely many steps. -/
@[rocq_alias trillium.fairness.terminating_trace]
def terminatingTrace (tr : Trace St L) : Prop := ∃ n, after n tr = none

@[rocq_alias trillium.fairness.terminating_trace_cons]
theorem terminating_trace_cons (s : St) (ℓ : L) (tr : Trace St L) :
    terminatingTrace tr → terminatingTrace (cons s ℓ tr) :=
  fun ⟨n, h⟩ => ⟨n + 1, by simpa using h⟩

@[rocq_alias trillium.fairness.infinite_trace_after]
theorem infinite_trace_after (n : Nat) (tr : Trace St L) :
    infiniteTrace tr →
      match after n tr with
      | none => False
      | some tr' => infiniteTrace tr' := by
  intro Hinf
  obtain ⟨tr', Htr'⟩ := Option.isSome_iff_exists.1 (Hinf n)
  rw [Htr']
  intro m
  have Hnm := Hinf (n + m)
  rwa [after_sum', Htr'] at Hnm

@[rocq_alias trillium.fairness.infinite_cons]
theorem infinite_cons (s : St) (ℓ : L) (r : Trace St L) :
    infiniteTrace (cons s ℓ r) → infiniteTrace r :=
  fun Hinf n => by simpa using Hinf (n + 1)

@[rocq_alias trillium.fairness.infinite_neg_finite]
theorem infinite_neg_finite (tr : Trace St L) : terminatingTrace tr ↔ ¬ infiniteTrace tr := by
  simp only [terminatingTrace, infiniteTrace, not_forall, Option.not_isSome_iff_eq_none]

@[rocq_alias trillium.fairness.terminating_trace_after]
theorem terminating_trace_after (tr atr : Trace St L) (i : Nat)
    (AFTER : after i tr = some atr) (FIN_ATR : terminatingTrace atr) : terminatingTrace tr := by
  obtain ⟨n, FIN⟩ := FIN_ATR
  exact ⟨i + n, by rw [after_sum', AFTER]; exact FIN⟩

end after

section TraceValid

variable {St L : Type _} (trans : St → L → St → Prop)

/-- A trace is valid if every step is a `trans` step (Rocq's paco predicate `trace_valid`,
built from the functor `trace_valid_ind`). -/
@[rocq_alias trillium.fairness.trace_valid]
coinductive TraceValid : Trace St L → Prop where
  | singl (δ : St) : TraceValid (singl δ)
  | cons (δ : St) (ℓ : L) (tr : Trace St L) :
      trans δ ℓ tr.first → TraceValid tr → TraceValid (cons δ ℓ tr)

#rocq_ignore trillium.fairness.trace_valid_ind
  "Generating functor of the paco definition; Lean's `coinductive` builds it internally"
#rocq_ignore trillium.fairness.trace_valid_mono
  "Monotonicity of the paco generating functor; Lean's `coinductive` proves it internally"

variable {trans}

/-- Inversion for `TraceValid`. -/
theorem TraceValid.inv {tr : Trace St L} (h : TraceValid trans tr) :
    (∃ s, tr = Trillium.Fairness.Trace.singl s) ∨ ∃ s ℓ r, trans s ℓ r.first ∧ TraceValid trans r ∧ tr = Trillium.Fairness.Trace.cons s ℓ r := by
  cases h with
  | singl s => exact .inl ⟨s, rfl⟩
  | cons s ℓ r ht hv => exact .inr ⟨s, ℓ, r, ht, hv, rfl⟩

@[rocq_alias trillium.fairness.trace_valid_cons_inv]
theorem trace_valid_cons_inv (tr : Trace St L) (s : St) (l : L)
    (VALID : TraceValid trans (Trillium.Fairness.Trace.cons s l tr)) : TraceValid trans tr ∧ trans s l tr.first := by
  rcases VALID.inv with ⟨_, h⟩ | ⟨s', l', r, ht, hv, h⟩
  · exact absurd h cons_ne_singl
  · obtain ⟨rfl, rfl, rfl⟩ := cons_inj.1 h
    exact ⟨hv, ht⟩

@[rocq_alias trillium.fairness.trace_valid_after]
theorem trace_valid_after (mtr mtr' : Trace St L) (k : Nat) :
    after k mtr = some mtr' → TraceValid trans mtr → TraceValid trans mtr' := by
  induction k generalizing mtr with
  | zero => intro h hv; simp only [after_0_id, Option.some.injEq] at h; exact h ▸ hv
  | succ k IH =>
    intro Hafter Hvalid
    cases mtr with
    | singl s => simp at Hafter
    | cons s ℓ r =>
      rw [after_succ_cons] at Hafter
      exact IH r Hafter (trace_valid_cons_inv r s ℓ Hvalid).1

@[rocq_alias trillium.fairness.trace_valid_tail]
theorem trace_valid_tail (s : St) (l : L) (tr : Trace St L)
    (VALID' : TraceValid trans (Trillium.Fairness.Trace.cons s l tr)) : TraceValid trans tr :=
  (trace_valid_cons_inv tr s l VALID').1

end TraceValid

section simulation

variable {L1 L2 S1 S2 : Type _}
variable (Rℓ : L1 → L2 → Prop) (Rs : S1 → S2 → Prop)
variable (trans1 : S1 → L1 → S1 → Prop) (trans2 : S2 → L2 → S2 → Prop)

/-- Two traces match step by step (Rocq's coinductive `traces_match`). -/
@[rocq_alias trillium.fairness.traces_match]
coinductive TracesMatch : Trace S1 L1 → Trace S2 L2 → Prop where
  | singl (s1 : S1) (s2 : S2) : Rs s1 s2 → TracesMatch (Trillium.Fairness.Trace.singl s1) (Trillium.Fairness.Trace.singl s2)
  | cons (s1 : S1) (ℓ1 : L1) (r1 : Trace S1 L1) (s2 : S2) (ℓ2 : L2) (r2 : Trace S2 L2) :
      Rℓ ℓ1 ℓ2 → Rs s1 s2 → trans1 s1 ℓ1 r1.first → trans2 s2 ℓ2 r2.first →
      TracesMatch r1 r2 → TracesMatch (Trillium.Fairness.Trace.cons s1 ℓ1 r1) (Trillium.Fairness.Trace.cons s2 ℓ2 r2)

variable {Rℓ Rs trans1 trans2}

/-- Inversion for `TracesMatch`. -/
theorem TracesMatch.inv {tr1 : Trace S1 L1} {tr2 : Trace S2 L2}
    (h : TracesMatch Rℓ Rs trans1 trans2 tr1 tr2) :
    (∃ s1 s2, Rs s1 s2 ∧ tr1 = Trillium.Fairness.Trace.singl s1 ∧ tr2 = Trillium.Fairness.Trace.singl s2) ∨
    ∃ s1 ℓ1 r1 s2 ℓ2 r2, Rℓ ℓ1 ℓ2 ∧ Rs s1 s2 ∧ trans1 s1 ℓ1 r1.first ∧ trans2 s2 ℓ2 r2.first ∧
      TracesMatch Rℓ Rs trans1 trans2 r1 r2 ∧ tr1 = Trillium.Fairness.Trace.cons s1 ℓ1 r1 ∧ tr2 = Trillium.Fairness.Trace.cons s2 ℓ2 r2 := by
  cases h with
  | singl s1 s2 h => exact .inl ⟨s1, s2, h, rfl, rfl⟩
  | cons s1 ℓ1 r1 s2 ℓ2 r2 h1 h2 h3 h4 h5 =>
    exact .inr ⟨s1, ℓ1, r1, s2, ℓ2, r2, h1, h2, h3, h4, h5, rfl, rfl⟩

theorem TracesMatch.singl_inv {s1 : S1} {s2 : S2}
    (h : TracesMatch Rℓ Rs trans1 trans2 (Trillium.Fairness.Trace.singl s1) (Trillium.Fairness.Trace.singl s2)) : Rs s1 s2 := by
  rcases h.inv with ⟨_, _, h, e1, e2⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, e1, _⟩
  · rw [singl_inj.1 e1, singl_inj.1 e2]; exact h
  · exact absurd e1 singl_ne_cons

theorem TracesMatch.cons_inv {s1 : S1} {ℓ1 : L1} {r1 : Trace S1 L1} {s2 : S2} {ℓ2 : L2}
    {r2 : Trace S2 L2} (h : TracesMatch Rℓ Rs trans1 trans2 (Trillium.Fairness.Trace.cons s1 ℓ1 r1) (Trillium.Fairness.Trace.cons s2 ℓ2 r2)) :
    Rℓ ℓ1 ℓ2 ∧ Rs s1 s2 ∧ trans1 s1 ℓ1 r1.first ∧ trans2 s2 ℓ2 r2.first ∧
      TracesMatch Rℓ Rs trans1 trans2 r1 r2 := by
  rcases h.inv with ⟨_, _, _, e1, _⟩ | ⟨_, _, _, _, _, _, h1, h2, h3, h4, h5, e1, e2⟩
  · exact absurd e1 cons_ne_singl
  · obtain ⟨rfl, rfl, rfl⟩ := cons_inj.1 e1
    obtain ⟨rfl, rfl, rfl⟩ := cons_inj.1 e2
    exact ⟨h1, h2, h3, h4, h5⟩

theorem TracesMatch.singl_cons_false {s1 : S1} {s2 : S2} {ℓ2 : L2} {r2 : Trace S2 L2}
    (h : TracesMatch Rℓ Rs trans1 trans2 (Trillium.Fairness.Trace.singl s1) (Trillium.Fairness.Trace.cons s2 ℓ2 r2)) : False := by
  rcases h.inv with ⟨_, _, _, _, e2⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, e1, _⟩
  · exact cons_ne_singl e2
  · exact singl_ne_cons e1

theorem TracesMatch.cons_singl_false {s1 : S1} {ℓ1 : L1} {r1 : Trace S1 L1} {s2 : S2}
    (h : TracesMatch Rℓ Rs trans1 trans2 (Trillium.Fairness.Trace.cons s1 ℓ1 r1) (Trillium.Fairness.Trace.singl s2)) : False := by
  rcases h.inv with ⟨_, _, _, e1, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, e2⟩
  · exact cons_ne_singl e1
  · exact singl_ne_cons e2

@[rocq_alias trillium.fairness.traces_match_after]
theorem traces_match_after (tr1 : Trace S1 L1) (tr2 : Trace S2 L2) (n : Nat)
    (tr2' : Trace S2 L2) :
    TracesMatch Rℓ Rs trans1 trans2 tr1 tr2 → after n tr2 = some tr2' →
      ∃ tr1', after n tr1 = some tr1' ∧ TracesMatch Rℓ Rs trans1 trans2 tr1' tr2' := by
  induction n generalizing tr1 tr2 with
  | zero =>
    intro Hm Ha
    simp only [after_0_id, Option.some.injEq] at Ha
    exact ⟨tr1, rfl, Ha ▸ Hm⟩
  | succ n IHn =>
    intro Hm Ha
    cases tr2 with
    | singl s => simp at Ha
    | cons s ℓ tr2'' =>
      cases tr1 with
      | singl s1 => exact Hm.singl_cons_false.elim
      | cons s1 ℓ1 r1 =>
        rw [after_succ_cons] at Ha ⊢
        exact IHn r1 tr2'' Hm.cons_inv.2.2.2.2 Ha

@[rocq_alias trillium.fairness.traces_match_first]
theorem traces_match_first (tr1 : Trace S1 L1) (tr2 : Trace S2 L2) :
    TracesMatch Rℓ Rs trans1 trans2 tr1 tr2 → Rs tr1.first tr2.first := by
  intro Hm
  rcases Hm.inv with ⟨s1, s2, h, rfl, rfl⟩ | ⟨_, _, _, _, _, _, _, h, _, _, _, rfl, rfl⟩ <;>
    exact h

@[rocq_alias trillium.fairness.traces_match_preserves_termination]
theorem traces_match_preserves_termination (tr1 : Trace S1 L1) (tr2 : Trace S2 L2) :
    TracesMatch Rℓ Rs trans1 trans2 tr1 tr2 → terminatingTrace tr2 → terminatingTrace tr1 := by
  rintro Hmatch ⟨n, HNone⟩
  induction n generalizing tr1 tr2 with
  | zero => simp at HNone
  | succ n IHn =>
    cases tr2 with
    | singl s =>
      cases tr1 with
      | singl s1 => exact ⟨1, rfl⟩
      | cons s1 ℓ1 r1 => exact Hmatch.cons_singl_false.elim
    | cons s ℓ tr2' =>
      cases tr1 with
      | singl s1 => exact Hmatch.singl_cons_false.elim
      | cons s1 ℓ1 r1 =>
        rw [after_succ_cons] at HNone
        exact terminating_trace_cons _ _ _ (IHn r1 tr2' Hmatch.cons_inv.2.2.2.2 HNone)

@[rocq_alias trillium.fairness.traces_match_valid1]
theorem traces_match_valid1 (tr1 : Trace S1 L1) (tr2 : Trace S2 L2) :
    TracesMatch Rℓ Rs trans1 trans2 tr1 tr2 → TraceValid trans1 tr1 := by
  intro Hmatch
  refine TraceValid.coinduct trans1 (fun tr1 => ∃ tr2, TracesMatch Rℓ Rs trans1 trans2 tr1 tr2)
    ?_ tr1 ⟨tr2, Hmatch⟩
  rintro tr1 ⟨tr2, Hm⟩
  rcases Hm.inv with ⟨s1, _, _, rfl, _⟩ | ⟨s1, ℓ1, r1, _, _, r2, _, _, h3, _, h5, rfl, _⟩
  · exact .inl ⟨s1, rfl⟩
  · exact .inr ⟨s1, ℓ1, r1, h3, ⟨r2, h5⟩, rfl⟩

@[rocq_alias trillium.fairness.traces_match_valid2]
theorem traces_match_valid2 (tr1 : Trace S1 L1) (tr2 : Trace S2 L2) :
    TracesMatch Rℓ Rs trans1 trans2 tr1 tr2 → TraceValid trans2 tr2 := by
  intro Hmatch
  refine TraceValid.coinduct trans2 (fun tr2 => ∃ tr1, TracesMatch Rℓ Rs trans1 trans2 tr1 tr2)
    ?_ tr2 ⟨tr1, Hmatch⟩
  rintro tr2 ⟨tr1, Hm⟩
  rcases Hm.inv with ⟨_, s2, _, _, rfl⟩ | ⟨_, _, r1, s2, ℓ2, r2, _, _, _, h4, h5, _, rfl⟩
  · exact .inl ⟨s2, rfl⟩
  · exact .inr ⟨s2, ℓ2, r2, h4, ⟨r1, h5⟩, rfl⟩

@[rocq_alias trillium.fairness.traces_match_after']
theorem traces_match_after' (tr1 : Trace S1 L1) (tr2 : Trace S2 L2) (n : Nat)
    (tr1' : Trace S1 L1) :
    TracesMatch Rℓ Rs trans1 trans2 tr1 tr2 → after n tr1 = some tr1' →
      ∃ tr2', after n tr2 = some tr2' ∧ TracesMatch Rℓ Rs trans1 trans2 tr1' tr2' := by
  induction n generalizing tr1 tr2 with
  | zero =>
    intro Hm Ha
    simp only [after_0_id, Option.some.injEq] at Ha
    exact ⟨tr2, rfl, Ha ▸ Hm⟩
  | succ n IHn =>
    intro Hm Ha
    cases tr1 with
    | singl s => simp at Ha
    | cons s ℓ tr1'' =>
      cases tr2 with
      | singl s2 => exact Hm.cons_singl_false.elim
      | cons s2 ℓ2 r2 =>
        rw [after_succ_cons] at Ha ⊢
        exact IHn tr1'' r2 Hm.cons_inv.2.2.2.2 Ha

end simulation

@[rocq_alias trillium.fairness.traces_match_flip]
theorem traces_match_flip {S1 S2 L1 L2 : Type _} (Rℓ : L1 → L2 → Prop) (Rs : S1 → S2 → Prop)
    (trans1 : S1 → L1 → S1 → Prop) (trans2 : S2 → L2 → S2 → Prop)
    (tr1 : Trace S1 L1) (tr2 : Trace S2 L2) :
    TracesMatch Rℓ Rs trans1 trans2 tr1 tr2 ↔
      TracesMatch (flip Rℓ) (flip Rs) trans2 trans1 tr2 tr1 := by
  constructor
  · intro H
    refine TracesMatch.coinduct (flip Rℓ) (flip Rs) trans2 trans1
      (fun tr2 tr1 => TracesMatch Rℓ Rs trans1 trans2 tr1 tr2) ?_ tr2 tr1 H
    intro tr2 tr1 Hm
    rcases Hm.inv with ⟨s1, s2, h, rfl, rfl⟩ | ⟨s1, ℓ1, r1, s2, ℓ2, r2, h1, h2, h3, h4, h5, rfl, rfl⟩
    · exact .inl ⟨s2, s1, h, rfl, rfl⟩
    · exact .inr ⟨s2, ℓ2, r2, s1, ℓ1, r1, h1, h2, h4, h3, h5, rfl, rfl⟩
  · intro H
    refine TracesMatch.coinduct Rℓ Rs trans1 trans2
      (fun tr1 tr2 => TracesMatch (flip Rℓ) (flip Rs) trans2 trans1 tr2 tr1) ?_ tr1 tr2 H
    intro tr1 tr2 Hm
    rcases Hm.inv with ⟨s2, s1, h, rfl, rfl⟩ | ⟨s2, ℓ2, r2, s1, ℓ1, r1, h1, h2, h3, h4, h5, rfl, rfl⟩
    · exact .inl ⟨s1, s2, h, rfl, rfl⟩
    · exact .inr ⟨s1, ℓ1, r1, s2, ℓ2, r2, h1, h2, h4, h3, h5, rfl, rfl⟩

@[rocq_alias trillium.fairness.traces_match_compose]
theorem traces_match_compose {L1 L2 L3 S1 S2 S3 : Type _}
    {Rℓ12 : L1 → L2 → Prop} {Rs12 : S1 → S2 → Prop} {Rℓ23 : L2 → L3 → Prop}
    {Rs23 : S2 → S3 → Prop} {trans1 : S1 → L1 → S1 → Prop} {trans2 : S2 → L2 → S2 → Prop}
    {trans3 : S3 → L3 → S3 → Prop}
    (tr1 : Trace S1 L1) (tr2 : Trace S2 L2) (tr3 : Trace S3 L3) :
    TracesMatch Rℓ12 Rs12 trans1 trans2 tr1 tr2 →
    TracesMatch Rℓ23 Rs23 trans2 trans3 tr2 tr3 →
    TracesMatch (fun l1 l3 => ∃ l2, Rℓ12 l1 l2 ∧ Rℓ23 l2 l3)
      (fun s1 s3 => ∃ s2, Rs12 s1 s2 ∧ Rs23 s2 s3) trans1 trans3 tr1 tr3 := by
  intro H12 H23
  refine TracesMatch.coinduct _ _ trans1 trans3
    (fun tr1 tr3 => ∃ tr2, TracesMatch Rℓ12 Rs12 trans1 trans2 tr1 tr2 ∧
      TracesMatch Rℓ23 Rs23 trans2 trans3 tr2 tr3) ?_ tr1 tr3 ⟨tr2, H12, H23⟩
  rintro tr1 tr3 ⟨tr2, H12, H23⟩
  rcases H12.inv with ⟨s1, s2, h, rfl, rfl⟩ | ⟨s1, ℓ1, r1, s2, ℓ2, r2, h1, h2, h3, _, h5, rfl, rfl⟩
  · rcases H23.inv with ⟨_, s3, h', e, rfl⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, e, _⟩
    · rw [← singl_inj.1 e] at h'
      exact .inl ⟨s1, s3, ⟨s2, h, h'⟩, rfl, rfl⟩
    · exact absurd e singl_ne_cons
  · rcases H23.inv with ⟨_, _, _, e, _⟩ | ⟨_, _, r2', s3, ℓ3, r3, h1', h2', _, h4', h5', e, rfl⟩
    · exact absurd e cons_ne_singl
    · obtain ⟨rfl, rfl, rfl⟩ := cons_inj.1 e
      exact .inr ⟨s1, ℓ1, r1, s3, ℓ3, r3, ⟨ℓ2, h1, h1'⟩, ⟨s2, h2, h2'⟩, h3, h4', ⟨r2, h5, h5'⟩,
        rfl, rfl⟩

section execs_and_traces

variable {S L : Type _}

open Trillium (FiniteTrace)

/-- An execution `ft` (finite prefix) continued by the steps `il` matches the trace `tr`
(Rocq's coinductive `exec_trace_match`). -/
@[rocq_alias trillium.fairness.exec_trace_match]
coinductive ExecTraceMatch : FiniteTrace S L → Seq (L × S) → Trace S L → Prop where
  | singl (ft : FiniteTrace S L) (s : S) : ft.last = s → ExecTraceMatch ft .nil (singl s)
  | cons (ft : FiniteTrace S L) (s : S) (ℓ : L) (ift : Seq (L × S)) (tr : Trace S L) :
      ExecTraceMatch (.extend ft ℓ s) ift tr →
      ExecTraceMatch ft (.cons (ℓ, s) ift) (cons ft.last ℓ tr)

/-- Inversion for `ExecTraceMatch`. -/
theorem ExecTraceMatch.inv {ft : FiniteTrace S L} {il : Seq (L × S)} {tr : Trace S L}
    (h : ExecTraceMatch ft il tr) :
    (∃ s, ft.last = s ∧ il = .nil ∧ tr = Trillium.Fairness.Trace.singl s) ∨
    ∃ s ℓ ift tr', ExecTraceMatch (.extend ft ℓ s) ift tr' ∧ il = .cons (ℓ, s) ift ∧
      tr = Trillium.Fairness.Trace.cons ft.last ℓ tr' := by
  cases h with
  | singl _ s h => exact .inl ⟨s, h, rfl, rfl⟩
  | cons _ s ℓ ift tr h => exact .inr ⟨s, ℓ, ift, tr, h, rfl, rfl⟩

/-- The trace starting in `s` with steps `il`. -/
@[rocq_alias trillium.fairness.to_trace]
def toTrace (s : S) (il : Seq (L × S)) : Trace S L := ⟨s, il⟩

@[simp] theorem toTrace_nil (s : S) : toTrace s (.nil : Seq (L × S)) = singl s := rfl

@[simp] theorem toTrace_cons (s s' : S) (ℓ : L) (rest : Seq (L × S)) :
    toTrace s (.cons (ℓ, s') rest) = cons s ℓ (toTrace s' rest) := rfl

@[rocq_alias trillium.fairness.to_trace_spec]
theorem to_trace_spec (fl : FiniteTrace S L) (il : Seq (L × S)) :
    ExecTraceMatch fl il (toTrace fl.last il) := by
  refine ExecTraceMatch.coinduct (fun fl il tr => tr = toTrace fl.last il) ?_ fl il _ rfl
  rintro fl il tr rfl
  cases il with
  | nil => exact .inl ⟨fl.last, rfl, rfl, rfl⟩
  | cons p rest =>
    obtain ⟨ℓ, x⟩ := p
    exact .inr ⟨x, ℓ, rest, toTrace x rest, rfl, rfl, rfl⟩

@[rocq_alias trillium.fairness.to_trace_singleton]
theorem to_trace_singleton (s : S) (il : Seq (L × S)) :
    ExecTraceMatch (.singleton s) il (toTrace s il) :=
  to_trace_spec (.singleton s) il

/-- The steps of a trace. -/
@[rocq_alias trillium.fairness.from_trace]
def fromTrace (tr : Trace S L) : Seq (L × S) := tr.steps

@[simp] theorem fromTrace_singl (s : S) : fromTrace (singl s : Trace S L) = .nil := rfl

@[simp] theorem fromTrace_cons (s : S) (ℓ : L) (tr : Trace S L) :
    fromTrace (cons s ℓ tr) = .cons (ℓ, tr.first) (fromTrace tr) := rfl

@[rocq_alias trillium.fairness.from_trace_spec]
theorem from_trace_spec (fl : FiniteTrace S L) (tr : Trace S L) :
    fl.last = tr.first → ExecTraceMatch fl (fromTrace tr) tr := by
  intro Heq
  refine ExecTraceMatch.coinduct (fun fl il tr => fl.last = tr.first ∧ il = fromTrace tr) ?_
    fl _ tr ⟨Heq, rfl⟩
  rintro fl il tr ⟨Heq, rfl⟩
  cases tr with
  | singl s => exact .inl ⟨s, Heq, rfl, rfl⟩
  | cons s ℓ tr' =>
    refine .inr ⟨tr'.first, ℓ, fromTrace tr', tr', ⟨rfl, rfl⟩, rfl, ?_⟩
    simp only [first_cons] at Heq
    rw [Heq]

end execs_and_traces

@[rocq_alias trillium.fairness.oleq]
def oleq : Option Nat → Option Nat → Prop
  | some x, some y => x ≤ y
  | _, _ => False

@[rocq_alias trillium.fairness.oless]
def oless : Option Nat → Option Nat → Prop
  | some x, some y => x < y
  | _, _ => False

@[rocq_alias trillium.fairness.oleq_oless]
theorem oleq_oless (a b : Option Nat) : oless a b → oleq a b := by
  cases a <;> cases b <;> simp [oless, oleq]
  omega

@[rocq_alias trillium.fairness.oless_dec]
instance oless_dec : ∀ x y, Decidable (oless x y)
  | some x, some y => inferInstanceAs (Decidable (x < y))
  | none, _ => inferInstanceAs (Decidable False)
  | some _, none => inferInstanceAs (Decidable False)

@[rocq_alias trillium.fairness.oleq_dec]
instance oleq_dec : ∀ x y, Decidable (oleq x y)
  | some x, some y => inferInstanceAs (Decidable (x ≤ y))
  | none, _ => inferInstanceAs (Decidable False)
  | some _, none => inferInstanceAs (Decidable False)

section lex_ind

section Lexicographic

variable (A B : Type _) (leA : A → A → Prop) (leB : B → B → Prop)

attribute [rocq_alias trillium.fairness.lexprod] Prod.Lex

@[rocq_alias trillium.fairness.wf_trans]
theorem wf_trans (tA : ∀ x y z, leA x y → leA y z → leA x z)
    (tB : ∀ x y z, leB x y → leB y z → leB x z) :
    ∀ x y z : A × B, Prod.Lex leA leB x y → Prod.Lex leA leB y z → Prod.Lex leA leB x z := by
  rintro ⟨x1, y1⟩ ⟨x2, y2⟩ ⟨x3, y3⟩ H H'
  cases H with
  | left _ _ h =>
    cases H' with
    | left _ _ h' => exact .left _ _ (tA _ _ _ h h')
    | right _ h' => exact .left _ _ h
  | right _ h =>
    cases H' with
    | left _ _ h' => exact .left _ _ h'
    | right _ h' => exact .right _ (tB _ _ _ h h')

@[rocq_alias trillium.fairness.wf_lexprod]
theorem wf_lexprod : WellFounded leA → WellFounded leB → WellFounded (Prod.Lex leA leB) :=
  fun wfA wfB => WellFounded.prod_lex wfA wfB

end Lexicographic

@[rocq_alias trillium.fairness.lt_lex]
def ltLex : ℕ × ℕ → ℕ × ℕ → Prop := fun p q => p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2)

/-- stdpp's `PartialOrder lt_lex` (reflexive, transitive, antisymmetric). -/
@[rocq_alias trillium.fairness.lt_lex_partial_order]
instance ltLex_partialOrder : IsPartialOrder (ℕ × ℕ) ltLex where
  refl _ := .inr ⟨rfl, le_rfl⟩
  trans _ _ _ := by simp only [ltLex]; omega
  antisymm a b := by
    simp only [ltLex]
    intro h1 h2
    ext <;> omega

@[rocq_alias trillium.fairness.myrel]
def myrel : ℕ × ℕ → ℕ × ℕ → Prop := Prod.Lex (· < ·) (· < ·)

@[rocq_alias trillium.fairness.lex_ind]
theorem lex_ind (n : ℕ × ℕ) (P : ℕ × ℕ → Prop)
    (HI : ∀ n0 : ℕ × ℕ, (∀ m : ℕ × ℕ, strict ltLex m n0 → P m) → P n0) : P n := by
  have Hwf : WellFounded myrel := wf_lexprod _ _ _ _ Nat.lt_wfRel.wf Nat.lt_wfRel.wf
  induction n using Hwf.induction with
  | _ n H =>
    apply HI
    rintro ⟨m1, m2⟩ ⟨Ha, Hb⟩
    apply H
    obtain ⟨n1, n2⟩ := n
    simp only [ltLex] at Ha Hb
    rcases Ha with Ha | ⟨rfl, Ha2⟩
    · exact .left _ _ Ha
    · exact .right _ (by omega)

end lex_ind

/-- The discrete OFE on `Nat`, used for the additive big operators. -/
scoped instance natOFE : Iris.OFE Nat := Iris.OFE.ofDiscrete Nat

/-- Rocq's `Monoid Nat.add` instance. -/
@[rocq_alias trillium.fairness.add_monoid]
scoped instance add_monoid : Iris.Algebra.MonoidOps (M := Nat) Nat.add 0 where
  op_ne := ⟨fun _ _ _ h _ _ h' => by
    simp only [Iris.OFE.Dist] at h h' ⊢; rw [h, h']⟩
  op_assoc := Nat.add_assoc _ _ _
  op_comm := Nat.add_comm _ _
  op_left_id := Nat.zero_add _

section addition_monoid

open Iris.Std Iris.Algebra

variable {K : Type _} {M : Type _ → Type _} [LawfulFiniteMap M K]

/-- Stated for iris-lean's generic finite maps (which cover `GMap` with
`M := (Std.ExtTreeMap K · compare)`); `k ∈ dom X` is `(get? X k).isSome`. -/
@[rocq_alias trillium.fairness.big_addM_leq_forall]
theorem big_addM_leq_forall (X Y : M Nat) :
    (∀ k, (get? X k).isSome → oleq (get? X k) (get? Y k)) →
      ([^ Nat.add map] _k ↦ x ∈ X, x) ≤ ([^ Nat.add map] _k ↦ y ∈ Y, y) := by
  classical
  induction X using LawfulFiniteMap.induction_on generalizing Y with
  | hemp => intro _; simp
  | hins k v X HXk IH =>
    intro Hx
    rw [BigOpM.bigOpM_insert_eq _ v HXk]
    have Hol : oleq (get? (Iris.Std.PartialMap.insert X k v) k) (get? Y k) := Hx k (by simp [get?_insert_eq])
    rw [get?_insert_eq rfl] at Hol
    cases Heq : get? Y k with
    | none => rw [Heq] at Hol; exact Hol.elim
    | some v' =>
      rw [Heq] at Hol
      rw [BigOpM.bigOpM_delete_eq _ Heq]
      refine Nat.add_le_add Hol (IH _ fun k' Hin => ?_)
      have hne : k ≠ k' := by rintro rfl; rw [HXk] at Hin; cases Hin
      rw [get?_delete_ne hne, ← get?_insert_ne (v := v) hne]
      exact Hx k' (by rwa [get?_insert_ne hne])

end addition_monoid

section infinite_or_finite

variable {St L : Type _}

@[rocq_alias trillium.fairness.infinite_or_finite]
theorem infinite_or_finite (tr : Trace St L) : infiniteTrace tr ∨ terminatingTrace tr := by
  by_cases h : infiniteTrace tr
  · exact .inl h
  · exact .inr ((infinite_neg_finite tr).2 h)

end infinite_or_finite

end Trillium.Fairness
