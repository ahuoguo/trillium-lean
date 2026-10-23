/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.ProgramLogic.Language

/-!
# Evaluation-context based languages

Port of `trillium/program_logic/ectx_language.v`.

An axiomatization of evaluation-context based languages (with Trillium's locales and
configuration steps), including a proof that this gives rise to a `Trillium.Language`.

## Representation

The Rocq `Structure ectxLanguage` with its mixin `EctxLanguageMixin` is the class
`Trillium.EctxLanguage Expr Val Ectx State Locale`. Like `Trillium.Language`, it extends
iris-lean's `ToVal` and `EvContext` (whose fields `fill_empty`, `fill_comp`, `fill_inj` are the
Rocq lemmas of the same names) and `Trillium.LanguageCore` (configuration steps and locales);
the head step relation lives in the small class `Trillium.HeadStep`, which is shared with
`Trillium.EctxiLanguage`.

The Rocq canonical structure `ectx_lang` (and `LanguageOfEctx`) is the instance
`Trillium.EctxLanguage.instLanguage`, whose `primStep` is the context closure
`Trillium.EctxLanguage.PrimStep` of the head step relation.
-/

namespace Trillium

open Iris.ProgramLogic (ToVal EvContext EvContextOps)
open Iris.ProgramLogic.ToVal (ofVal)

/-- The head step relation of an evaluation-context based language. -/
class HeadStep (Expr : Type _) (State : outParam (Type _)) where
  headStep : Expr → State → Expr → State → List Expr → Prop

export HeadStep (headStep)

/-- An evaluation-context based language (Rocq `ectxLanguage` with `EctxLanguageMixin`). -/
@[rocq_alias trillium.ectxLanguage, rocq_alias trillium.EctxLanguageMixin]
class EctxLanguage (Expr : Type _) (Val Ectx State Locale : outParam (Type _))
    extends ToVal Expr Val, EvContext Expr Ectx, LanguageCore Expr State Locale,
      HeadStep Expr State where
  val_head_stuck {e1 σ1 e2 σ2 efs} : headStep e1 σ1 e2 σ2 efs → toVal e1 = none
  fill_val (K : Ectx) (e : Expr) : (toVal (fill K e)).isSome → (toVal e).isSome
  fill_positive (K K' : Ectx) (e e' : Expr) :
    toVal e = none → toVal e' = none → fill K e = fill K' e' →
    (∃ K'', K' = comp K K'') ∨ (∃ K'', K = comp K' K'')
  /-- Given a head redex `e1_redex` somewhere in a term, and another decomposition of the same
  term into `fill K' e1'` such that `e1'` is not a value, then the head redex context is
  `e1'`'s context `K'` filled with another context `K''`. In particular, this implies
  `e1' = fill K'' e1_redex` by `fill_inj`, i.e., `e1'` contains the head redex.

  This implies there can be only one head redex, see `head_redex_unique`. -/
  step_by_val {K' K_redex : Ectx} {e1' e1_redex : Expr} {σ1 e2 σ2 efs} :
    fill K' e1' = fill K_redex e1_redex → toVal e1' = none →
    headStep e1_redex σ1 e2 σ2 efs → ∃ K'', K_redex = comp K' K''
  /-- If `fill K e` takes a head step, then either `e` is a value or `K` is the empty
  evaluation context. In other words, if `e` is not a value wrapping it in a context does not
  add new head redex positions. -/
  head_ctx_step_val {K : Ectx} {e : Expr} {σ1 e2 σ2 efs} :
    headStep (fill K e) σ1 e2 σ2 efs → (toVal e).isSome ∨ K = empty
  locale_step {e1 e2 : Expr} (t1 : List Expr) {σ1 σ2 efs} :
    headStep e1 σ1 e2 σ2 efs → localeOf t1 e1 = localeOf t1 e2
  locale_fill (e : Expr) (K : Ectx) (t1 : List Expr) : localeOf t1 (fill K e) = localeOf t1 e

attribute [rocq_alias trillium.val_head_stuck] EctxLanguage.val_head_stuck
attribute [rocq_alias trillium.fill_val] EctxLanguage.fill_val
attribute [rocq_alias trillium.fill_positive] EctxLanguage.fill_positive
attribute [rocq_alias trillium.step_by_val] EctxLanguage.step_by_val
attribute [rocq_alias trillium.ectx_language.head_ctx_step_val] EctxLanguage.head_ctx_step_val
attribute [rocq_alias trillium.ectx_language.locale_fill] EctxLanguage.locale_fill

attribute [rocq_alias trillium.fill_empty] Iris.ProgramLogic.EvContext.fill_empty
attribute [rocq_alias trillium.fill_comp] Iris.ProgramLogic.EvContext.fill_comp
attribute [rocq_alias trillium.fill_inj] Iris.ProgramLogic.EvContext.fill_inj

namespace EctxLanguage

variable {Expr Val Ectx State Locale : Type _} [Λ : EctxLanguage Expr Val Ectx State Locale]

@[rocq_alias trillium.head_reducible]
def HeadReducible (e : Expr) (σ : State) : Prop :=
  ∃ e' σ' efs, headStep e σ e' σ' efs

@[rocq_alias trillium.head_irreducible]
def HeadIrreducible (e : Expr) (σ : State) : Prop :=
  ∀ e' σ' efs, ¬ headStep e σ e' σ' efs

@[rocq_alias trillium.head_stuck]
def HeadStuck (e : Expr) (σ : State) : Prop :=
  toVal e = none ∧ HeadIrreducible e σ

/-- All non-value redexes are at the root. In other words, all sub-redexes are values. -/
@[rocq_alias trillium.sub_redexes_are_values]
def SubRedexesAreValues (e : Expr) : Prop :=
  ∀ (K : Ectx) e', e = fill K e' → toVal e' = none → K = EvContextOps.empty

/-- The primitive step relation of an ectx language: the closure of the head step relation
under evaluation contexts. -/
@[rocq_alias trillium.prim_step]
inductive PrimStep (e1 : Expr) (σ1 : State) (e2 : Expr) (σ2 : State) (efs : List Expr) :
    Prop where
  | ectx_step (K : Ectx) (e1' e2' : Expr) :
    e1 = fill K e1' → e2 = fill K e2' → headStep e1' σ1 e2' σ2 efs →
    PrimStep e1 σ1 e2 σ2 efs

@[rocq_alias trillium.Ectx_step']
theorem PrimStep.ectx_step' (K : Ectx) {e1 : Expr} {σ1 : State} {e2 σ2 efs} :
    headStep e1 σ1 e2 σ2 efs → PrimStep (fill K e1) σ1 (fill K e2) σ2 efs :=
  fun h => .ectx_step K e1 e2 rfl rfl h

@[rocq_alias trillium.ectx_language.fill_not_val]
theorem fill_not_val (K : Ectx) {e : Expr} : toVal e = none → toVal (fill K e) = none := by
  intro h
  cases hv : toVal (fill K e) with
  | none => rfl
  | some _ =>
    have := fill_val K e (by simp [hv])
    simp [h] at this

/-- The language of an ectx language (Rocq `ectx_lang_mixin`, `ectx_lang` and
`LanguageOfEctx`). -/
@[rocq_alias trillium.ectx_lang_mixin, rocq_alias trillium.ectx_lang,
  rocq_alias trillium.LanguageOfEctx]
instance instLanguage : Language Expr Val Ectx State Locale where
  toToVal := Λ.toToVal
  toEvContext := Λ.toEvContext
  toLanguageCore := Λ.toLanguageCore
  primStep := PrimStep
  val_stuck := by
    rintro e σ e' σ' efs ⟨K, e1', e2', rfl, rfl, hs⟩
    exact fill_not_val K (val_head_stuck hs)
  fill_not_val := fill_not_val
  fill_step K := by
    rintro e1 σ1 e2 σ2 efs ⟨K', e1', e2', rfl, rfl, hs⟩
    exact ⟨EvContextOps.comp K K', e1', e2', EvContext.fill_comp .., EvContext.fill_comp .., hs⟩
  fill_step_inv K := by
    rintro e1 σ1 e2 σ2 efs hnv ⟨K'', e1'', e2'', heq, rfl, hs⟩
    obtain ⟨K', rfl⟩ := step_by_val heq hnv hs
    rw [← EvContext.fill_comp] at heq
    have heq := EvContext.fill_inj heq
    exact ⟨fill K' e2'', (EvContext.fill_comp ..).symm, ⟨K', e1'', e2'', heq, rfl, hs⟩⟩
  ectx_fill_positive := fill_positive
  locale_step_preserve t1 := by
    rintro σ1 σ2 efs ⟨K, e1', e2', rfl, rfl, hs⟩
    rw [locale_fill, locale_fill]
    exact locale_step t1 hs
  locale_fill := locale_fill

@[rocq_alias trillium.head_atomic]
def HeadAtomic (a : Atomicity) (e : Expr) : Prop :=
  ∀ (σ : State) e' σ' efs, headStep e σ e' σ' efs →
    match a with
    | .WeaklyAtomic => Language.Irreducible e' σ'
    | .StronglyAtomic => (toVal e').isSome

@[rocq_alias trillium.head_stutteringatomic]
def HeadStutteringAtomic (a : Atomicity) (e : Expr) : Prop :=
  ∀ (σ : State) e' σ' efs, headStep e σ e' σ' efs →
    (e' = e ∧ σ' = σ ∧ efs = []) ∨
    match a with
    | .WeaklyAtomic => Language.Irreducible e' σ'
    | .StronglyAtomic => (toVal e').isSome

variable {e : Expr} {σ : State}

@[rocq_alias trillium.not_head_reducible]
theorem not_head_reducible : ¬ HeadReducible e σ ↔ HeadIrreducible e σ := by
  simp [HeadReducible, HeadIrreducible]

/-- The decomposition into head redex and context is unique.

In all sensible instances, `comp K' empty` will be the same as `K'`, so the conclusion is
`K = K' ∧ e = e'`, but we do not require a law to actually prove that so we cannot use that
fact here. -/
@[rocq_alias trillium.head_redex_unique]
theorem head_redex_unique {K K' : Ectx} {e e' : Expr} {σ : State} :
    fill K e = fill K' e' → HeadReducible e σ → HeadReducible e' σ →
    K = EvContextOps.comp K' EvContextOps.empty ∧ e = e' := by
  rintro heq ⟨e2, σ2, efs, hred⟩ ⟨e2', σ2', efs', hred'⟩
  obtain ⟨K'', rfl⟩ := step_by_val heq.symm (val_head_stuck hred') hred
  rw [← EvContext.fill_comp] at heq
  obtain rfl := EvContext.fill_inj heq
  rcases head_ctx_step_val hred' with h | rfl
  · rw [val_head_stuck hred] at h; simp at h
  · exact ⟨rfl, (EvContext.fill_empty _).symm⟩

@[rocq_alias trillium.head_prim_step]
theorem head_prim_step {e1 : Expr} {σ1 : State} {e2 σ2 efs} :
    headStep e1 σ1 e2 σ2 efs → primStep e1 σ1 e2 σ2 efs :=
  fun h => .ectx_step EvContextOps.empty e1 e2 (EvContext.fill_empty _).symm
    (EvContext.fill_empty _).symm h

@[rocq_alias trillium.head_step_not_stuck]
theorem head_step_not_stuck {e' σ' efs} : headStep e σ e' σ' efs → Language.NotStuck e σ :=
  fun h => Language.prim_step_not_stuck (head_prim_step h)

@[rocq_alias trillium.fill_prim_step]
theorem fill_prim_step (K : Ectx) {e1 : Expr} {σ1 : State} {e2 σ2 efs} :
    primStep e1 σ1 e2 σ2 efs → primStep (fill K e1) σ1 (fill K e2) σ2 efs :=
  Language.fill_step K

@[rocq_alias trillium.fill_reducible]
theorem fill_reducible (K : Ectx) : Language.Reducible e σ → Language.Reducible (fill K e) σ :=
  Language.reducible_fill K

@[rocq_alias trillium.head_prim_reducible]
theorem head_prim_reducible : HeadReducible e σ → Language.Reducible e σ :=
  fun ⟨e', σ', efs, h⟩ => ⟨e', σ', efs, head_prim_step h⟩

@[rocq_alias trillium.head_prim_fill_reducible]
theorem head_prim_fill_reducible (K : Ectx) :
    HeadReducible e σ → Language.Reducible (fill K e) σ :=
  fun h => fill_reducible K (head_prim_reducible h)

@[rocq_alias trillium.head_prim_irreducible]
theorem head_prim_irreducible : Language.Irreducible e σ → HeadIrreducible e σ := by
  rw [← Language.not_reducible, ← not_head_reducible]
  exact fun h h' => h (head_prim_reducible h')

@[rocq_alias trillium.prim_head_reducible]
theorem prim_head_reducible :
    Language.Reducible e σ → SubRedexesAreValues e → HeadReducible e σ := by
  rintro ⟨e', σ', efs, ⟨K, e1', e2', rfl, rfl, hs⟩⟩ hsub
  obtain rfl := hsub K e1' rfl (val_head_stuck hs)
  rw [EvContext.fill_empty]
  exact ⟨e2', σ', efs, hs⟩

@[rocq_alias trillium.prim_head_irreducible]
theorem prim_head_irreducible :
    HeadIrreducible e σ → SubRedexesAreValues e → Language.Irreducible e σ := by
  rw [← Language.not_reducible, ← not_head_reducible]
  exact fun h hsub h' => h (prim_head_reducible h' hsub)

@[rocq_alias trillium.head_stuck_stuck]
theorem head_stuck_stuck : HeadStuck e σ → SubRedexesAreValues e → Language.Stuck e σ :=
  fun ⟨hv, hirr⟩ hsub => ⟨hv, prim_head_irreducible hirr hsub⟩

@[rocq_alias trillium.ectx_language_atomic]
theorem ectx_language_atomic (a : Atomicity) :
    HeadAtomic a e → SubRedexesAreValues e → Language.Atomic (State := State) a e := by
  intro hat hsub
  refine ⟨fun {σ e' σ' efs} hs => ?_⟩
  obtain ⟨K, e1', e2', rfl, rfl, hs⟩ := hs
  obtain rfl := hsub K e1' rfl (val_head_stuck hs)
  simp only [EvContext.fill_empty] at hat ⊢
  exact hat σ e2' σ' efs hs

@[rocq_alias trillium.ectx_language_stutteringatomic]
theorem ectx_language_stutteringatomic (a : Atomicity) :
    HeadStutteringAtomic a e → SubRedexesAreValues e →
    Language.StutteringAtomic (State := State) a e := by
  intro hat hsub
  refine ⟨fun {σ e' σ' efs} hs => ?_⟩
  obtain ⟨K, e1', e2', rfl, rfl, hs⟩ := hs
  obtain rfl := hsub K e1' rfl (val_head_stuck hs)
  simp only [EvContext.fill_empty] at hat ⊢
  exact hat σ e2' σ' efs hs

@[rocq_alias trillium.head_reducible_prim_step_ctx]
theorem head_reducible_prim_step_ctx (K : Ectx) {e1 : Expr} {σ1 : State} {e2 σ2 efs} :
    HeadReducible e1 σ1 → primStep (fill K e1) σ1 e2 σ2 efs →
    ∃ e2', e2 = fill K e2' ∧ headStep e1 σ1 e2' σ2 efs := by
  rintro ⟨e2'', σ2'', efs'', hK⟩ ⟨K', e1', e2', hKe1, rfl, hs⟩
  obtain ⟨K'', rfl⟩ := step_by_val hKe1 (val_head_stuck hK) hs
  rw [← EvContext.fill_comp] at hKe1
  obtain rfl := EvContext.fill_inj hKe1
  rcases head_ctx_step_val hK with h | rfl
  · rw [val_head_stuck hs] at h; simp at h
  · refine ⟨e2', ?_, ?_⟩
    · rw [← EvContext.fill_comp, EvContext.fill_empty]
    · rwa [EvContext.fill_empty]

@[rocq_alias trillium.head_reducible_prim_step]
theorem head_reducible_prim_step {e1 : Expr} {σ1 : State} {e2 σ2 efs} :
    HeadReducible e1 σ1 → primStep e1 σ1 e2 σ2 efs → headStep e1 σ1 e2 σ2 efs := by
  intro hred hs
  rw [← EvContext.fill_empty (Expr := Expr) (Ectx := Ectx) e1] at hs
  obtain ⟨e2', rfl, hs⟩ := head_reducible_prim_step_ctx EvContextOps.empty hred hs
  rwa [EvContext.fill_empty]

/-- A pure head step. -/
@[rocq_alias trillium.pure_head_step]
structure PureHeadStep (e1 e2 : Expr) : Prop where
  safe (σ1 : State) : HeadReducible e1 σ1
  det {σ1 : State} {e2' σ2 efs} : headStep e1 σ1 e2' σ2 efs → σ2 = σ1 ∧ e2' = e2 ∧ efs = []

@[rocq_alias trillium.pure_head_step_pure_step]
theorem pure_head_step_pure_step {e1 e2 : Expr} :
    PureHeadStep (Λ := Λ) e1 e2 → Language.PureStep (Λ := instLanguage) e1 e2 := by
  rintro ⟨hp1, hp2⟩
  exact ⟨fun σ => head_prim_reducible (hp1 σ),
    fun hs => hp2 (head_reducible_prim_step (hp1 _) hs)⟩

/-- This is not an instance because HeapLang's `wp_pure` tactic already takes care of handling
the evaluation context. -/
@[rocq_alias trillium.pure_exec_fill]
theorem pure_exec_fill (K : Ectx) {φ : Prop} {n : Nat} {e1 e2 : Expr} :
    Language.PureExec (Λ := instLanguage) φ n e1 e2 →
    Language.PureExec (Λ := instLanguage) φ n (fill K e1) (fill K e2) :=
  Language.pure_exec_ctx K

@[rocq_alias trillium.head_locale_step]
theorem head_locale_step (K : Ectx) {e1 e2 : Expr} (tp1 tp2 : List Expr) {efs}
    {σ1 σ2 : State} :
    headStep e1 σ1 e2 σ2 efs →
    Language.LocaleStep (tp1 ++ fill K e1 :: tp2, σ1) (some (localeOf tp1 e1))
      (tp1 ++ fill K e2 :: (tp2 ++ efs), σ2) := by
  intro hs
  rw [← locale_fill e1 K tp1]
  exact .atomic _ _ (Language.fill_step K (head_prim_step hs))

end EctxLanguage

end Trillium
