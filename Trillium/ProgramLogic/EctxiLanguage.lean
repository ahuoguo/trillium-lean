/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.ProgramLogic.EctxLanguage
import Mathlib.Data.List.Induction

/-!
# Languages based on evaluation context items

Port of `trillium/program_logic/ectxi_language.v`.

An axiomatization of languages based on evaluation context items, including a proof that these
are instances of general ectx-based languages.

## Representation

The Rocq `Structure ectxiLanguage` with its mixin `EctxiLanguageMixin` is the class
`Trillium.EctxiLanguage Expr Val EctxItem State Locale`, extending iris-lean's `ToVal`,
`Trillium.LanguageCore` and `Trillium.HeadStep`.

Evaluation contexts are lists of items, `fill K e` folds `fillItem` over `K` starting from the
innermost item (the head of the list), `comp K₁ K₂ = K₂ ++ K₁` and `empty = []`
(`Trillium.EctxiLanguage.instEvContext`). The Rocq canonical structures `ectxi_lang_ectx`
(`EctxLanguageOfEctxi`) and `ectxi_lang` are the instances
`Trillium.EctxiLanguage.instEctxLanguage` and (through it)
`Trillium.EctxLanguage.instLanguage`.

To set up a language (cf. `heap_lang`), declare an instance of `EctxiLanguage`; the
`EctxLanguage` and `Language` instances are then found automatically.
-/

namespace Trillium

open Iris.ProgramLogic (ToVal EvContext EvContextOps)
open Iris.ProgramLogic.ToVal (ofVal)

/-- A language based on evaluation context items (Rocq `ectxiLanguage` with
`EctxiLanguageMixin`). -/
@[rocq_alias trillium.ectxiLanguage, rocq_alias trillium.EctxiLanguageMixin]
class EctxiLanguage (Expr : Type _) (Val EctxItem State Locale : outParam (Type _))
    extends ToVal Expr Val, LanguageCore Expr State Locale, HeadStep Expr State where
  fillItem : EctxItem → Expr → Expr
  val_stuck {e1 σ1 e2 σ2 efs} : headStep e1 σ1 e2 σ2 efs → toVal e1 = none
  fill_item_val (Ki : EctxItem) (e : Expr) : (toVal (fillItem Ki e)).isSome → (toVal e).isSome
  /-- `fillItem` is always injective on the expression for a fixed context. -/
  fill_item_inj (Ki : EctxItem) : Function.Injective (fillItem Ki)
  /-- `fillItem` with (potentially different) non-value expressions is injective on the
  context. -/
  fill_item_no_val_inj (Ki1 Ki2 : EctxItem) {e1 e2 : Expr} :
    toVal e1 = none → toVal e2 = none → fillItem Ki1 e1 = fillItem Ki2 e2 → Ki1 = Ki2
  /-- If `fillItem Ki e` takes a head step, then `e` is a value (unlike for `EctxLanguage`, an
  empty context is impossible here). In other words, if `e` is not a value then wrapping it in
  a context does not add new head redex positions. -/
  head_ctx_step_val {Ki : EctxItem} {e : Expr} {σ1 e2 σ2 efs} :
    headStep (fillItem Ki e) σ1 e2 σ2 efs → (toVal e).isSome
  locale_step {e1 e2 : Expr} (t1 : List Expr) {σ1 σ2 efs} :
    headStep e1 σ1 e2 σ2 efs → localeOf t1 e1 = localeOf t1 e2
  locale_fill (e : Expr) (Ki : EctxItem) (t1 : List Expr) :
    localeOf t1 (fillItem Ki e) = localeOf t1 e

export EctxiLanguage (fillItem)

attribute [rocq_alias trillium.fill_item_inj] EctxiLanguage.fill_item_inj
attribute [rocq_alias trillium.fill_item_val] EctxiLanguage.fill_item_val
attribute [rocq_alias trillium.fill_item_no_val_inj] EctxiLanguage.fill_item_no_val_inj
attribute [rocq_alias trillium.ectxi_language.head_ctx_step_val]
  EctxiLanguage.head_ctx_step_val

namespace EctxiLanguage

variable {Expr Val EctxItem State Locale : Type _}
  [Λ : EctxiLanguage Expr Val EctxItem State Locale]

/-- Filling a context (a list of items, innermost first). Rocq `fill`. -/
@[rocq_alias trillium.fill]
def fillCtx (K : List EctxItem) (e : Expr) : Expr := K.foldl (flip fillItem) e

/-- Evaluation contexts of an ectxi language are lists of items. -/
instance instEvContext : EvContext Expr (List EctxItem) where
  empty := []
  comp K1 K2 := K2 ++ K1
  fill := fillCtx
  fill_empty _ := rfl
  fill_comp K1 K2 e := by simp [fillCtx, List.foldl_append]
  fill_inj {K} := by
    induction K with
    | nil => exact fun _ _ h => h
    | cons Ki K ih => exact fun x y h => fill_item_inj Ki (ih h)

@[simp]
theorem fill_nil (e : Expr) : EvContext.fill ([] : List EctxItem) e = e := rfl

@[simp]
theorem fill_cons (Ki : EctxItem) (K : List EctxItem) (e : Expr) :
    EvContext.fill (Ki :: K) e = EvContext.fill K (fillItem Ki e) := rfl

@[simp]
theorem empty_eq : (EvContextOps.empty : List EctxItem) = [] := rfl

@[simp]
theorem comp_eq (K1 K2 : List EctxItem) : EvContextOps.comp K1 K2 = K2 ++ K1 := rfl

@[rocq_alias trillium.fill_app]
theorem fill_append (K1 K2 : List EctxItem) (e : Expr) :
    EvContext.fill (K1 ++ K2) e = EvContext.fill K2 (EvContext.fill K1 e) := by
  simp [EvContext.fill, fillCtx, List.foldl_append]

theorem fill_append_singleton (K : List EctxItem) (Ki : EctxItem) (e : Expr) :
    EvContext.fill (K ++ [Ki]) e = fillItem Ki (EvContext.fill K e) := by
  simp [fill_append]

theorem fill_val (K : List EctxItem) (e : Expr) :
    (toVal (EvContext.fill K e)).isSome → (toVal e).isSome := by
  induction K generalizing e with
  | nil => exact id
  | cons Ki K ih => exact fun h => fill_item_val Ki e (ih _ h)

theorem fill_not_val' (K : List EctxItem) {e : Expr} :
    toVal e = none → toVal (EvContext.fill K e) = none := by
  intro h
  cases hv : toVal (EvContext.fill K e) with
  | none => rfl
  | some _ =>
    have := fill_val K e (by simp [hv])
    simp [h] at this

/-- The ectx language of an ectxi language (Rocq `ectxi_lang_ectx_mixin`, `ectxi_lang_ectx`
and `EctxLanguageOfEctxi`). -/
@[rocq_alias trillium.ectxi_lang_ectx_mixin, rocq_alias trillium.ectxi_lang_ectx,
  rocq_alias trillium.EctxLanguageOfEctxi]
instance instEctxLanguage : EctxLanguage Expr Val (List EctxItem) State Locale where
  toToVal := Λ.toToVal
  toEvContext := instEvContext
  toLanguageCore := Λ.toLanguageCore
  toHeadStep := Λ.toHeadStep
  val_head_stuck := val_stuck
  fill_val := fill_val
  fill_positive K := by
    induction K using List.reverseRec with
    | nil => intro K' _ _ _ _ _; left; exact ⟨K', by simp⟩
    | append_singleton K Ki ih =>
      intro K' e e' he he' hes
      cases K' using List.reverseRec with
      | nil => right; exact ⟨K ++ [Ki], by simp⟩
      | append_singleton K' Ki' _ =>
        rw [fill_append_singleton, fill_append_singleton] at hes
        obtain rfl := fill_item_no_val_inj Ki Ki' (fill_not_val' K he) (fill_not_val' K' he') hes
        rcases ih K' e e' he he' (fill_item_inj Ki hes) with ⟨Kx, rfl⟩ | ⟨Kx, rfl⟩
        · left; exact ⟨Kx, by simp⟩
        · right; exact ⟨Kx, by simp⟩
  step_by_val {K K' e1 e1' σ1 e2 σ2 efs} hfill hred hstep := by
    induction K using List.reverseRec generalizing K' with
    | nil => exact ⟨K', by simp⟩
    | append_singleton K Ki ih =>
      cases K' using List.reverseRec with
      | nil =>
        rw [fill_nil, fill_append_singleton] at hfill
        subst hfill
        have := fill_val K e1 (head_ctx_step_val hstep)
        simp [hred] at this
      | append_singleton K' Ki' _ =>
        rw [fill_append_singleton, fill_append_singleton] at hfill
        obtain rfl := fill_item_no_val_inj Ki Ki' (fill_not_val' K hred)
          (fill_not_val' K' (val_stuck hstep)) hfill
        obtain ⟨K'', rfl⟩ := ih (fill_item_inj Ki hfill)
        exact ⟨K'', by simp⟩
  head_ctx_step_val {K e σ1 e2 σ2 efs} := by
    cases K using List.reverseRec with
    | nil => intro; right; rfl
    | append_singleton K Ki _ =>
      rw [fill_append_singleton]
      intro h
      exact .inl (fill_val K e (head_ctx_step_val h))
  locale_step := locale_step
  locale_fill e K t1 := by
    induction K generalizing e with
    | nil => rfl
    | cons Ki K ih => rw [fill_cons, ih, locale_fill]

attribute [rocq_alias trillium.ectxi_lang] EctxLanguage.instLanguage

@[rocq_alias trillium.ectxi_language.fill_not_val]
theorem fill_not_val (K : List EctxItem) {e : Expr} :
    toVal e = none → toVal (EvContext.fill K e) = none :=
  fill_not_val' K

@[rocq_alias trillium.ectxi_language_sub_redexes_are_values]
theorem ectxi_language_sub_redexes_are_values {e : Expr} :
    (∀ Ki e', e = fillItem Ki e' → (toVal e').isSome) →
    EctxLanguage.SubRedexesAreValues (Λ := instEctxLanguage) e := by
  rintro hsub K e' rfl hnv
  cases K using List.reverseRec with
  | nil => rfl
  | append_singleton K Ki _ =>
    have := fill_val K e' (hsub Ki _ (fill_append_singleton K Ki e'))
    simp [hnv] at this

end EctxiLanguage

end Trillium
