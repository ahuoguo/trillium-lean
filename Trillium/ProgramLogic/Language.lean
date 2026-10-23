/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Iris.ProgramLogic.Language
import Iris.ProgramLogic.EctxLanguage
import Mathlib.Data.List.Forall2
import Mathlib.Logic.Relation

/-!
# Trillium languages

Port of `trillium/program_logic/language.v`.

Trillium's notion of language differs from Iris': besides values and a primitive step relation
(without observations), a language has

* a type of *locales* (thread identifiers) together with `localeOf : List Expr → Expr → Locale`,
  computing the locale of a thread from the thread pool prefix in front of it;
* a step relation `configStep : State → State → Prop` on states alone ("configuration steps",
  taken by the environment rather than by a thread);
* evaluation contexts (`Ectx` with `fill`, `comp` and `empty`), which are part of the language
  since the program logic uses them to form program traces.

## Representation

The Rocq `Record language` with its mixin `LanguageMixin` is represented by the class
`Trillium.Language Expr Val Ectx State Locale`, indexed by the expression type, with the other
carriers as `outParam`s (following iris-lean's `Iris.ProgramLogic.Language`). It extends

* iris-lean's `Iris.ProgramLogic.ToVal Expr Val` (`toVal`/`ofVal` with `to_of_val`/`of_to_val`),
* iris-lean's `Iris.ProgramLogic.EvContext Expr Ectx` (`fill`, `EvContextOps.comp`,
  `EvContextOps.empty` with `fill_empty`, `fill_comp`, `fill_inj`), and
* `Trillium.LanguageCore Expr State Locale`, holding `configStep`, `localeOf` and the two laws
  about locales that do not mention steps or contexts (`locale_equiv`, `locale_injective`).

The same `ToVal`, `EvContext` and `LanguageCore` parents are used by `Trillium.EctxLanguage` and
`Trillium.EctxiLanguage`, so that the `Language` instances derived from them share
`toVal`, `fill`, `configStep` and `localeOf` syntactically with the underlying language.

The mixin field `mixin_is_eval_ctx` (a conjunction) is split into the three fields
`fill_not_val`, `fill_step`, `fill_step_inv`; `isEvalCtx` recovers the Rocq statement.

Since `State` is an `outParam` determined by `Expr`, `configStep σ σ'` cannot infer the
language; write `LanguageCore.configStep (Expr := Expr) σ σ'`.

Rocq's `is_Some (to_val e)` is rendered as `(toVal e).isSome` (as in iris-lean), and stdpp's
`relations.nsteps` as iris-lean's `Relation.Iterate`.
-/

namespace Trillium

open Iris.ProgramLogic (ToVal EvContext EvContextOps)
open Iris.ProgramLogic.ToVal (ofVal)

export Iris.ProgramLogic.ToVal (toVal)
export Iris.ProgramLogic.EvContext (fill)

/-! ## Prefixes of a list -/

section Prefixes

variable {A : Type _}

/-- `prefixesFrom pref l` lists, for every element `x` of `l`, the pair of `x` and the list of
elements in front of it (starting with `pref`). -/
@[rocq_alias trillium.prefixes_from]
def prefixesFrom : List A → List A → List (List A × A)
  | _, [] => []
  | pref, x :: xs => (pref, x) :: prefixesFrom (pref ++ [x]) xs

/-- Rocq notation `prefixes l`. -/
abbrev prefixes (l : List A) : List (List A × A) := prefixesFrom [] l

@[simp]
theorem prefixesFrom_nil (pref : List A) : prefixesFrom pref [] = [] := rfl

@[simp]
theorem prefixesFrom_cons (pref : List A) (x : A) (xs : List A) :
    prefixesFrom pref (x :: xs) = (pref, x) :: prefixesFrom (pref ++ [x]) xs := rfl

@[rocq_alias trillium.prefixes_from_app]
theorem prefixesFrom_append (l0 l1 l2 : List A) :
    prefixesFrom l0 (l1 ++ l2) = prefixesFrom l0 l1 ++ prefixesFrom (l0 ++ l1) l2 := by
  induction l1 generalizing l0 with
  | nil => simp
  | cons a l1 ih => simp [ih]

/-- Rocq's version assumes `EqDecision A`; this is not needed in Lean. -/
@[rocq_alias trillium.prefixes_from_spec]
theorem mem_prefixesFrom_iff (tp0 tp1 : List A) (e : A) (tp : List A) :
    (tp, e) ∈ prefixesFrom tp0 tp1 ↔ ∃ t t', tp = tp0 ++ t ∧ tp1 = t ++ e :: t' := by
  induction tp1 generalizing tp0 with
  | nil => simp
  | cons e' t' ih =>
    simp only [prefixesFrom_cons, List.mem_cons, Prod.mk.injEq, ih]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨t, t'', rfl, rfl⟩)
      · exact ⟨[], t', by simp, by simp⟩
      · exact ⟨e' :: t, t'', by simp, by simp⟩
    · rintro ⟨t, t'', rfl, h⟩
      cases t with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        left; simp
      | cons a t =>
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        right; exact ⟨t, t'', by simp, rfl⟩

@[rocq_alias trillium.prefixes_from_lookup]
theorem prefixesFrom_getElem? (tp0 tp1 : List A) (n : Nat) (e : A) :
    tp1[n]? = some e → (prefixesFrom tp0 tp1)[n]? = some (tp0 ++ tp1.take n, e) := by
  induction tp1 generalizing tp0 n with
  | nil => simp
  | cons e1 tp1 ih =>
    cases n with
    | zero => simp_all
    | succ n =>
      intro h
      simp only [prefixesFrom_cons, List.getElem?_cons_succ, List.take_succ_cons] at h ⊢
      rw [ih _ _ h]
      simp

end Prefixes

/-! ## Languages -/

/-- The part of a Trillium language concerning locales and configuration steps. Shared as a
parent by `Language`, `EctxLanguage` and `EctxiLanguage`. The two laws are the mixin fields
`mixin_locale_equiv` and `mixin_locale_injective`. -/
class LanguageCore (Expr : Type _) (State Locale : outParam (Type _)) where
  /-- Steps of the environment, changing only the state. -/
  configStep : State → State → Prop
  /-- The locale of a thread `e`, given the threads `t` in front of it in the thread pool. -/
  localeOf : List Expr → Expr → Locale
  /-- The locale of a thread only depends on the locales of the threads in front of it. -/
  locale_equiv (t t' : List Expr) (e : Expr) :
    List.Forall₂ (fun p q => localeOf p.1 p.2 = localeOf q.1 q.2)
      (prefixes t) (prefixes t') →
    localeOf t e = localeOf t' e
  /-- Different threads have different locales. -/
  locale_injective (tp0 : List Expr) (e0 : Expr) (tp1 tp : List Expr) (e : Expr) :
    (tp, e) ∈ prefixesFrom (tp0 ++ [e0]) tp1 → localeOf tp0 e0 ≠ localeOf tp e

export LanguageCore (localeOf)

attribute [rocq_alias trillium.locale_equiv] LanguageCore.locale_equiv
attribute [rocq_alias trillium.locale_injective] LanguageCore.locale_injective

/-- Rocq notation `locales_equiv t t'`: the thread pools `t` and `t'` assign the same locales to
corresponding threads. -/
abbrev LocalesEquiv {Expr State Locale : Type _} [LanguageCore Expr State Locale]
    (t t' : List Expr) : Prop :=
  List.Forall₂ (fun p q => localeOf p.1 p.2 = localeOf q.1 q.2) (prefixes t) (prefixes t')

/-- A Trillium language (Rocq `language` together with `LanguageMixin`). -/
@[rocq_alias trillium.language, rocq_alias trillium.LanguageMixin]
class Language (Expr : Type _) (Val Ectx State Locale : outParam (Type _))
    extends ToVal Expr Val, EvContext Expr Ectx, LanguageCore Expr State Locale where
  /-- The primitive (per-thread) step relation: `primStep e σ e' σ' efs` steps `e` in state
  `σ` to `e'` in state `σ'`, forking the threads `efs`. -/
  primStep : Expr → State → Expr → State → List Expr → Prop
  val_stuck {e σ e' σ' efs} : primStep e σ e' σ' efs → toVal e = none
  fill_not_val (K : Ectx) {e : Expr} : toVal e = none → toVal (fill K e) = none
  fill_step (K : Ectx) {e1 σ1 e2 σ2 efs} :
    primStep e1 σ1 e2 σ2 efs → primStep (fill K e1) σ1 (fill K e2) σ2 efs
  fill_step_inv (K : Ectx) {e1' σ1 e2 σ2 efs} :
    toVal e1' = none → primStep (fill K e1') σ1 e2 σ2 efs →
    ∃ e2', e2 = fill K e2' ∧ primStep e1' σ1 e2' σ2 efs
  ectx_fill_positive (K K' : Ectx) (e e' : Expr) :
    toVal e = none → toVal e' = none → fill K e = fill K' e' →
    (∃ K'', K' = comp K K'') ∨ (∃ K'', K = comp K' K'')
  locale_step_preserve {e1 e2 : Expr} (t1 : List Expr) {σ1 σ2 efs} :
    primStep e1 σ1 e2 σ2 efs → localeOf t1 e1 = localeOf t1 e2
  locale_fill (e : Expr) (K : Ectx) (t1 : List Expr) : localeOf t1 (fill K e) = localeOf t1 e

export Language (primStep)

attribute [rocq_alias trillium.val_stuck] Language.val_stuck
attribute [rocq_alias trillium.language.fill_not_val] Language.fill_not_val
attribute [rocq_alias trillium.fill_step] Language.fill_step
attribute [rocq_alias trillium.fill_step_inv] Language.fill_step_inv
attribute [rocq_alias trillium.ectx_fill_positive] Language.ectx_fill_positive
attribute [rocq_alias trillium.locale_step_preserve] Language.locale_step_preserve
attribute [rocq_alias trillium.language.locale_fill] Language.locale_fill

-- Fields of `ToVal`/`EvContext` that are Trillium lemmas.
attribute [rocq_alias trillium.to_of_val] Iris.ProgramLogic.ToVal.toVal_coe
attribute [rocq_alias trillium.of_to_val] Iris.ProgramLogic.ToVal.coe_of_toVal_eq_some
attribute [rocq_alias trillium.ectx_fill_emp] Iris.ProgramLogic.EvContext.fill_empty
attribute [rocq_alias trillium.of_val_inj] Iris.ProgramLogic.ToVal.TovVal.ofVal_inj

attribute [rocq_alias trillium.exprO] Iris.ProgramLogic.exprO
attribute [rocq_alias trillium.valO] Iris.ProgramLogic.valO
attribute [rocq_alias trillium.stateO] Iris.ProgramLogic.stateO

attribute [rocq_alias trillium.atomicity] Iris.ProgramLogic.Language.Atomicity

/-- Atomicity (`StronglyAtomic`/`WeaklyAtomic`), shared with iris-lean. -/
abbrev Atomicity := Iris.ProgramLogic.Language.Atomicity

/-- Configurations: a thread pool together with a state. -/
@[rocq_alias trillium.cfg]
abbrev Cfg (Expr : Type _) {Val Ectx State Locale : Type _}
    [Language Expr Val Ectx State Locale] : Type _ :=
  List Expr × State

namespace Language

variable {Expr Val Ectx State Locale : Type _} [Λ : Language Expr Val Ectx State Locale]

/-- The properties of an evaluation context, as a function on expressions. -/
@[rocq_alias trillium.is_an_eval_ctx]
structure IsAnEvalCtx (K : Expr → Expr) : Prop where
  fill_not_val {e : Expr} : toVal e = none → toVal (K e) = none
  fill_step {e1 : Expr} {σ1 : State} {e2 σ2 efs} :
    primStep e1 σ1 e2 σ2 efs → primStep (K e1) σ1 (K e2) σ2 efs
  fill_step_inv {e1' : Expr} {σ1 : State} {e2 σ2 efs} :
    toVal e1' = none → primStep (K e1') σ1 e2 σ2 efs →
    ∃ e2', e2 = K e2' ∧ primStep e1' σ1 e2' σ2 efs

@[rocq_alias trillium.is_eval_ctx]
theorem isEvalCtx (K : Ectx) : IsAnEvalCtx (fill (Expr := Expr) K) :=
  ⟨Λ.fill_not_val K, Λ.fill_step K, Λ.fill_step_inv K⟩

@[rocq_alias trillium.ectx_comp_comp]
theorem ectx_comp_comp (K K' : Ectx) (e : Expr) :
    fill (EvContextOps.comp K K') e = fill K (fill K' e) :=
  (EvContext.fill_comp K K' e).symm

@[rocq_alias trillium.ectx_fill_inj]
theorem ectx_fill_inj (K : Ectx) {e e' : Expr} : fill K e = fill K e' → e = e' :=
  fun h => EvContext.fill_inj h

@[rocq_alias trillium.locale_fill_step]
theorem locale_fill_step {e1 e2 : Expr} {σ1 σ2 : State} (t1 : List Expr) {efs} (K : Ectx) :
    primStep e1 σ1 e2 σ2 efs → localeOf t1 (fill K e1) = localeOf t1 (fill K e2) := by
  intro h
  rw [locale_fill, locale_fill]
  exact locale_step_preserve t1 h

/-! ### Reducibility -/

@[rocq_alias trillium.reducible]
def Reducible (e : Expr) (σ : State) : Prop :=
  ∃ e' σ' efs, primStep e σ e' σ' efs

@[rocq_alias trillium.irreducible]
def Irreducible (e : Expr) (σ : State) : Prop :=
  ∀ e' σ' efs, ¬ primStep e σ e' σ' efs

@[rocq_alias trillium.stuck]
def Stuck (e : Expr) (σ : State) : Prop :=
  toVal e = none ∧ Irreducible e σ

@[rocq_alias trillium.not_stuck]
def NotStuck (e : Expr) (σ : State) : Prop :=
  (toVal e).isSome ∨ Reducible e σ

/-- `Atomic a e`: every step of `e` ends in an irreducible expression (`WeaklyAtomic`) or in a
value (`StronglyAtomic`). See the Rocq source for a discussion of the two variants. -/
@[rocq_alias trillium.Atomic]
class Atomic (a : Atomicity) (e : Expr) : Prop where
  atomic {σ : State} {e' σ' efs} :
    primStep e σ e' σ' efs →
    match a with
    | .WeaklyAtomic => Irreducible e' σ'
    | .StronglyAtomic => (toVal e').isSome

/-- Like `Atomic`, but `e` may also take stuttering steps (to itself, without changing the
state or forking). -/
@[rocq_alias trillium.StutteringAtomic]
class StutteringAtomic (a : Atomicity) (e : Expr) : Prop where
  stutteringatomic {σ : State} {e' σ' efs} :
    primStep e σ e' σ' efs →
    (e' = e ∧ σ' = σ ∧ efs = []) ∨
    match a with
    | .WeaklyAtomic => Irreducible e' σ'
    | .StronglyAtomic => (toVal e').isSome

@[rocq_alias trillium.atomic_stutteringatomic]
instance atomic_stutteringAtomic (a : Atomicity) (e : Expr) [h : Atomic (State := State) a e] :
    StutteringAtomic (State := State) a e :=
  ⟨fun hs => .inr (h.atomic hs)⟩

/-! ### Thread-pool steps -/

/-- A step of a configuration: either a thread takes a primitive step, or the environment
takes a configuration step. -/
@[rocq_alias trillium.step]
inductive Step : List Expr × State → List Expr × State → Prop where
  | atomic {e1 σ1 e2 σ2 efs} (t1 t2 : List Expr) :
    primStep e1 σ1 e2 σ2 efs → Step (t1 ++ e1 :: t2, σ1) (t1 ++ e2 :: (t2 ++ efs), σ2)
  | state {σ1 σ2 : State} (t : List Expr) :
    LanguageCore.configStep (Expr := Expr) σ1 σ2 → Step (t, σ1) (t, σ2)

/-- A step of a configuration labelled with the locale of the thread that took it (`none` for
configuration steps). -/
@[rocq_alias trillium.locale_step]
inductive LocaleStep : List Expr × State → Option Locale → List Expr × State → Prop where
  | atomic {e1 σ1 e2 σ2 efs} (t1 t2 : List Expr) :
    primStep e1 σ1 e2 σ2 efs →
    LocaleStep (t1 ++ e1 :: t2, σ1) (some (localeOf t1 e1)) (t1 ++ e2 :: (t2 ++ efs), σ2)
  | state {σ1 σ2 : State} (t : List Expr) :
    LanguageCore.configStep (Expr := Expr) σ1 σ2 → LocaleStep (t, σ1) none (t, σ2)

/-- `n` steps of configurations. -/
@[rocq_alias trillium.nsteps]
inductive NSteps : Nat → List Expr × State → List Expr × State → Prop where
  | refl (ρ : List Expr × State) : NSteps 0 ρ ρ
  | l {n : Nat} {ρ1 ρ2 ρ3 : List Expr × State} : Step ρ1 ρ2 → NSteps n ρ2 ρ3 → NSteps (n + 1) ρ1 ρ3

/-- `rtc step` and `nsteps` encode the same thing. -/
@[rocq_alias trillium.steps_nsteps]
theorem steps_nsteps (ρ1 ρ2 : List Expr × State) :
    Relation.ReflTransGen (Step (Expr := Expr)) ρ1 ρ2 ↔ ∃ n, NSteps n ρ1 ρ2 := by
  constructor
  · intro h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨0, .refl _⟩
    | head hs _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, .l hs hn⟩
  · rintro ⟨n, h⟩
    induction h with
    | refl => exact .refl
    | l hs _ ih => exact .head hs ih

/-! ### Basic lemmas -/

@[rocq_alias trillium.of_to_val_flip]
theorem of_to_val_flip {v : Val} {e : Expr} : ofVal v = e → toVal e = some v := by
  rintro rfl; exact ToVal.toVal_coe v

@[rocq_alias trillium.not_reducible]
theorem not_reducible {e : Expr} {σ : State} : ¬ Reducible e σ ↔ Irreducible e σ := by
  simp [Reducible, Irreducible]

@[rocq_alias trillium.reducible_not_val]
theorem reducible_not_val {e : Expr} {σ : State} : Reducible e σ → toVal e = none :=
  fun ⟨_, _, _, h⟩ => val_stuck h

@[rocq_alias trillium.val_irreducible]
theorem val_irreducible {e : Expr} {σ : State} : (toVal e).isSome → Irreducible e σ := by
  intro hv e' σ' efs hs
  rw [val_stuck hs] at hv
  simp at hv

@[rocq_alias trillium.not_not_stuck]
theorem not_not_stuck {e : Expr} {σ : State} : ¬ NotStuck e σ ↔ Stuck e σ := by
  simp [NotStuck, Stuck, ← not_reducible]

@[rocq_alias trillium.strongly_atomic_atomic]
theorem strongly_atomic_atomic {e : Expr} {a : Atomicity} :
    Atomic (State := State) .StronglyAtomic e → Atomic (State := State) a e := by
  rintro ⟨h⟩
  cases a with
  | StronglyAtomic => exact ⟨h⟩
  | WeaklyAtomic => exact ⟨fun hs => val_irreducible (h hs)⟩

@[rocq_alias trillium.strongly_stutteringatomic_stutteringatomic]
theorem strongly_stutteringAtomic_stutteringAtomic {e : Expr} {a : Atomicity} :
    StutteringAtomic (State := State) .StronglyAtomic e →
    StutteringAtomic (State := State) a e := by
  rintro ⟨h⟩
  cases a with
  | StronglyAtomic => exact ⟨h⟩
  | WeaklyAtomic =>
    refine ⟨fun hs => ?_⟩
    rcases h hs with h | h
    · exact .inl h
    · exact .inr (val_irreducible h)

@[rocq_alias trillium.reducible_fill]
theorem reducible_fill (K : Ectx) {e : Expr} {σ : State} :
    Reducible e σ → Reducible (fill K e) σ :=
  fun ⟨e', σ', efs, h⟩ => ⟨fill K e', σ', efs, fill_step K h⟩

@[rocq_alias trillium.reducible_fill_inv]
theorem reducible_fill_inv (K : Ectx) {e : Expr} {σ : State} :
    toVal e = none → Reducible (fill K e) σ → Reducible e σ := by
  rintro hv ⟨e', σ', efs, hs⟩
  obtain ⟨e2', -, hs⟩ := fill_step_inv K hv hs
  exact ⟨e2', σ', efs, hs⟩

@[rocq_alias trillium.irreducible_fill]
theorem irreducible_fill (K : Ectx) {e : Expr} {σ : State} :
    toVal e = none → Irreducible e σ → Irreducible (fill K e) σ := by
  intro hv hirr
  rw [← not_reducible] at hirr ⊢
  exact fun h => hirr (reducible_fill_inv K hv h)

@[rocq_alias trillium.irreducible_fill_inv]
theorem irreducible_fill_inv (K : Ectx) {e : Expr} {σ : State} :
    Irreducible (fill K e) σ → Irreducible e σ := by
  intro hirr
  rw [← not_reducible] at hirr ⊢
  exact fun h => hirr (reducible_fill K h)

@[rocq_alias trillium.not_stuck_fill_inv]
theorem not_stuck_fill_inv (K : Ectx) {e : Expr} {σ : State} :
    NotStuck (fill K e) σ → NotStuck e σ := by
  rintro (h | h)
  · left
    cases hv : toVal e with
    | some _ => simp
    | none => rw [fill_not_val K hv] at h; simp at h
  · cases hv : toVal e with
    | some _ => left; simp [hv]
    | none => right; exact reducible_fill_inv K hv h

@[rocq_alias trillium.stuck_fill]
theorem stuck_fill (K : Ectx) {e : Expr} {σ : State} : Stuck e σ → Stuck (fill K e) σ := by
  rw [← not_not_stuck, ← not_not_stuck]
  exact fun h h' => h (not_stuck_fill_inv K h')

open List in
@[rocq_alias trillium.step_Permutation]
theorem step_perm {t1 t1' t2 : List Expr} {σ1 σ2 : State} (ht : t1 ~ t1') :
    Step (t1, σ1) (t2, σ2) → ∃ t2', t2 ~ t2' ∧ Step (t1', σ1) (t2', σ2) := by
  intro hs
  cases hs with
  | atomic tl tr hstep =>
    rename_i e1 e2 efs
    obtain ⟨tl', tr', rfl⟩ := List.append_of_mem (show e1 ∈ t1' from ht.subset (by simp))
    refine ⟨tl' ++ e2 :: (tr' ++ efs), ?_, .atomic _ _ hstep⟩
    have h1 : tl ++ tr ~ tl' ++ tr' :=
      (List.perm_cons e1).mp (perm_middle.symm.trans (ht.trans perm_middle))
    calc tl ++ e2 :: (tr ++ efs)
      _ ~ e2 :: (tl ++ (tr ++ efs)) := perm_middle
      _ = e2 :: ((tl ++ tr) ++ efs) := by simp
      _ ~ e2 :: ((tl' ++ tr') ++ efs) := (h1.append_right efs).cons e2
      _ = e2 :: (tl' ++ (tr' ++ efs)) := by simp
      _ ~ tl' ++ e2 :: (tr' ++ efs) := perm_middle.symm
  | state _ hc => exact ⟨t1', ht, .state _ hc⟩

@[rocq_alias trillium.step_insert]
theorem step_insert {i : Nat} {t2 : List Expr} {σ2 : State} {e e' : Expr} {σ3 : State} {efs}
    (hi : t2[i]? = some e) (hs : primStep e σ2 e' σ3 efs) :
    Step (t2, σ2) (t2.set i e' ++ efs, σ3) := by
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  have key : t2 = t2.take i ++ t2[i] :: t2.drop (i + 1) := by
    simp
  have hset : t2.set i e' ++ efs = t2.take i ++ e' :: (t2.drop (i + 1) ++ efs) := by
    rw [List.set_eq_take_append_cons_drop]; simp [hlt]
  rw [hset]
  conv => lhs; rw [key]
  exact .atomic _ _ hs

/-! ### Pure steps -/

/-- A pure step: `e1` is reducible in every state, and every step of `e1` goes to `e2` without
changing the state or forking. -/
@[rocq_alias trillium.pure_step]
structure PureStep (e1 e2 : Expr) : Prop where
  safe (σ1 : State) : Reducible e1 σ1
  det {σ1 : State} {e2' σ2 efs} : primStep e1 σ1 e2' σ2 efs → σ2 = σ1 ∧ e2' = e2 ∧ efs = []

/-- Rocq notation `pure_steps_tp`: each thread of the first pool takes pure steps to the
corresponding thread of the second. -/
abbrev PureStepsTp (t1 t2 : List Expr) : Prop :=
  List.Forall₂ (Relation.ReflTransGen (PureStep (Λ := Λ))) t1 t2

/-- `PureExec φ n e1 e2`: if `φ` holds, `e1` takes `n` pure steps to `e2`. As in iris-lean,
`φ`, `n` and `e2` are output parameters, so instances are found from `e1`. -/
@[ipm_class, rocq_alias trillium.PureExec]
class PureExec (φ : outParam Prop) (n : outParam Nat) (e1 : Expr) (e2 : outParam Expr) :
    Prop where
  pure_exec : φ → Relation.Iterate (PureStep (Λ := Λ)) n e1 e2

@[rocq_alias trillium.pure_step_ctx]
theorem pure_step_ctx (K : Ectx) {e1 e2 : Expr} :
    PureStep (Λ := Λ) e1 e2 → PureStep (Λ := Λ) (fill K e1) (fill K e2) := by
  rintro ⟨hred, hstep⟩
  refine ⟨fun σ => reducible_fill K (hred σ), fun {σ1 e2' σ2 efs} hp => ?_⟩
  obtain ⟨e2'', rfl, hp'⟩ := fill_step_inv K (reducible_not_val (hred σ1)) hp
  obtain ⟨rfl, rfl, rfl⟩ := hstep hp'
  exact ⟨rfl, rfl, rfl⟩

@[rocq_alias trillium.pure_step_nsteps_ctx]
theorem pure_step_nsteps_ctx (K : Ectx) {n : Nat} {e1 e2 : Expr} :
    Relation.Iterate (PureStep (Λ := Λ)) n e1 e2 →
    Relation.Iterate (PureStep (Λ := Λ)) n (fill K e1) (fill K e2) := by
  intro h
  induction h with
  | rfl => exact .rfl _
  | tail y _ hs ih => exact .tail _ ih (pure_step_ctx K hs)

@[rocq_alias trillium.rtc_pure_step_ctx]
theorem rtc_pure_step_ctx (K : Ectx) {e1 e2 : Expr} :
    Relation.ReflTransGen (PureStep (Λ := Λ)) e1 e2 →
    Relation.ReflTransGen (PureStep (Λ := Λ)) (fill K e1) (fill K e2) :=
  fun h => h.lift (fill K) (fun _ _ => pure_step_ctx K)

/-- Not an instance, because it is awfully general. -/
@[rocq_alias trillium.pure_exec_ctx]
theorem pure_exec_ctx (K : Ectx) {φ : Prop} {n : Nat} {e1 e2 : Expr} :
    PureExec (Λ := Λ) φ n e1 e2 → PureExec (Λ := Λ) φ n (fill K e1) (fill K e2) :=
  fun h => ⟨fun hφ => pure_step_nsteps_ctx K (h.pure_exec hφ)⟩

/-- A family of frequent assumptions for `PureExec`. -/
@[rocq_alias trillium.IntoVal]
class IntoVal (e : Expr) (v : Val) : Prop where
  into_val : ofVal v = e

@[rocq_alias trillium.AsVal]
class AsVal (e : Expr) : Prop where
  as_val : ∃ v : Val, ofVal v = e

@[rocq_alias trillium.as_vals_of_val]
instance as_vals_of_val (vs : List Val) :
    Iris.Std.TCForall (AsVal (Λ := Λ)) (vs.map (ofVal (Expr := Expr))) := by
  refine Iris.Std.forall_TCForall.mpr fun e h => ?_
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp h
  exact ⟨v, rfl⟩

@[rocq_alias trillium.as_val_is_Some]
theorem as_val_isSome {e : Expr} : (∃ v : Val, ofVal v = e) → (toVal e).isSome := by
  rintro ⟨v, rfl⟩
  simp

@[rocq_alias trillium.prim_step_not_stuck]
theorem prim_step_not_stuck {e : Expr} {σ : State} {e' σ' efs} :
    primStep e σ e' σ' efs → NotStuck e σ :=
  fun h => .inr ⟨e', σ', efs, h⟩

@[rocq_alias trillium.rtc_pure_step_val]
theorem rtc_pure_step_val [Inhabited State] {v : Val} {e : Expr} :
    Relation.ReflTransGen (PureStep (Λ := Λ)) (ofVal v) e → toVal e = some v := by
  intro h
  cases h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ToVal.toVal_coe v
  | head hs _ =>
    obtain ⟨_, _, _, hp⟩ := hs.safe default
    have := val_stuck hp
    simp at this

/-- Let thread pools `t1` and `t3` be such that each thread in `t1` makes (zero or more) pure
steps to the corresponding thread in `t3`. Furthermore, let `t2` be a thread pool such that `t1`
under state `σ1` makes a (single) step to thread pool `t2` and state `σ2`. In this situation,
either the step from `t1` to `t2` corresponds to one of the pure steps between `t1` and `t3`,
or there is an `i` such that the `i`th thread does not participate in the pure steps between
`t1` and `t3` and `t2` corresponds to taking a step in the `i`th thread starting from `t1`, or
the step is a configuration step. -/
@[rocq_alias trillium.step_pure_step_tp]
theorem step_pure_step_tp {t1 : List Expr} {σ1 : State} {t2 : List Expr} {σ2 : State}
    {t3 : List Expr} :
    Step (t1, σ1) (t2, σ2) → PureStepsTp (Λ := Λ) t1 t3 →
    (σ1 = σ2 ∧ PureStepsTp (Λ := Λ) t2 t3) ∨
    (∃ i e efs e', t1[i]? = some e ∧ t3[i]? = some e ∧ t2 = t1.set i e' ++ efs ∧
      primStep e σ1 e' σ2 efs) ∨
    LanguageCore.configStep (Expr := Expr) σ1 σ2 := by
  intro ht hps
  cases ht with
  | atomic t11 t12 hstep =>
    rename_i e e' efs
    have hps1 : List.Forall₂ (Relation.ReflTransGen (PureStep (Λ := Λ))) t11
        (t3.take t11.length) := by
      simpa using List.forall₂_take t11.length hps
    have hps2 : List.Forall₂ (Relation.ReflTransGen (PureStep (Λ := Λ))) (e :: t12)
        (t3.drop t11.length) := by
      simpa using List.forall₂_drop t11.length hps
    rw [← List.take_append_drop t11.length t3]
    generalize t3.take t11.length = t31 at hps1 ⊢
    generalize t3.drop t11.length = rest at hps2 ⊢
    rcases hps2 with _ | ⟨hpe, hps2⟩
    have hlen := hps1.length_eq
    rcases Relation.ReflTransGen.cases_head hpe with rfl | ⟨e2, hp, hrest⟩
    · right; left
      refine ⟨t11.length, e, efs, e', by simp, by simp [hlen], ?_, hstep⟩
      simp
    · obtain ⟨rfl, rfl, rfl⟩ := hp.det hstep
      left
      refine ⟨rfl, ?_⟩
      simp only [List.append_nil]
      exact List.rel_append hps1 (.cons hrest hps2)
  | state _ hc => right; right; exact hc

end Language

end Trillium
