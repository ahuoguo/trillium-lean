/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.ProgramLogic.AdequacyLocales
import Trillium.Fairness.Utils

/-!
# Locale helpers
Port of `fairness/locales_helpers.v`.

Helpers relating the locales of a thread pool (`localesOfList`, `fromLocale`) and the set of
locales of a configuration (`localesOfCfg`), plus the locale forked by a step (`stepFork`,
`extrLastFork`).

Representation: stdpp's `Countable (locale Λ)` (needed for `gset (locale Λ)`) becomes
`[Ord Locale] [Std.TransOrd Locale] [Std.LawfulEqOrd Locale]` (the keys of `GSet`), plus
`[DecidableEq Locale]` (needed by `fromLocale`). `list_to_set` is `LawfulSet.ofList`, and
`is_Some o` is `o.isSome`.
-/

namespace Trillium.Fairness

open Trillium Iris.Std FiniteTrace Language

section LanguageCore

variable {Expr State Locale : Type _} [LanguageCore Expr State Locale] [DecidableEq Locale]

/-- Converse of `mem_localesOfListFrom_of_fromLocaleFrom`. -/
@[rocq_alias trillium.fairness.locales_of_list_from_locale_from']
theorem fromLocaleFrom_isSome_of_mem_localesOfListFrom {tp0 tp1 : List Expr} {ζ : Locale} :
    ζ ∈ localesOfListFrom tp0 tp1 → (fromLocaleFrom tp0 tp1 ζ).isSome := by
  induction tp1 generalizing tp0 with
  | nil => simp [localesOfListFrom]
  | cons e1 tp1 IH =>
    rw [localesOfListFrom_cons, List.mem_cons]
    intro H
    simp only [fromLocaleFrom]
    by_cases h : localeOf tp0 e1 = ζ
    · simp [h]
    · simp only [h, ↓reduceIte]
      rcases H with H | H
      · exact absurd H.symm h
      · exact IH H

end LanguageCore

section Language

variable {Expr Val Ectx State Locale : Type _} [Language Expr Val Ectx State Locale]
  [DecidableEq Locale]

@[rocq_alias trillium.fairness.locale_step_from_locale_src]
theorem locale_step_from_locale_src {c1 c2 : List Expr × State} {ζ : Locale} :
    LocaleStep c1 (some ζ) c2 → (fromLocale c1.1 ζ).isSome := by
  intro Hstep
  cases Hstep with
  | atomic t1 t2 _ =>
    rename_i e1 _ _ _ _
    rw [fromLocale, fromLocaleFrom_some]
    · rfl
    · rw [mem_prefixesFrom_iff]
      exact ⟨t1, t2, by simp, rfl⟩

variable [Ord Locale] [Std.TransOrd Locale] [Std.LawfulEqOrd Locale]

/-- The set of locales of the threads of a configuration. -/
@[rocq_alias trillium.fairness.locales_of_cfg]
def localesOfCfg (c : List Expr × State) : GSet Locale :=
  LawfulSet.ofList (localesOfList c.1)

omit [DecidableEq Locale] in
@[rocq_alias trillium.fairness.locales_of_cfg_singleton]
theorem localesOfCfg_singleton (e : Expr) (σ : State) :
    localesOfCfg ([e], σ) = ({localeOf ([] : List Expr) e} : GSet Locale) := by
  apply LawfulSet.ext
  intro x
  rw [localesOfCfg, ← LawfulSet.mem_ofList, LawfulSet.mem_singleton]
  simp [localesOfListFrom]

@[rocq_alias trillium.fairness.locales_of_cfg_Some]
theorem mem_localesOfCfg_iff (τ : Locale) (tp : List Expr) (σ : State) :
    τ ∈ localesOfCfg (tp, σ) ↔ (fromLocale tp τ).isSome := by
  rw [localesOfCfg, ← LawfulSet.mem_ofList]
  exact ⟨fromLocaleFrom_isSome_of_mem_localesOfListFrom,
    mem_localesOfListFrom_of_fromLocaleFrom⟩

/-- Some locale that exists in `c2` but not in `c1` (the thread forked by a step), if any. -/
@[rocq_alias trillium.fairness.step_fork]
def stepFork (c1 c2 : List Expr × State) : Option Locale :=
  gsetPick (localesOfCfg c2 \ localesOfCfg c1)

/-- The locale forked by the last step of an execution, if any. -/
@[rocq_alias trillium.fairness.extr_last_fork]
def extrLastFork : ExecutionTrace Expr → Option Locale
  | .singleton _ => none
  | .extend extr' _ c' => stepFork extr'.last c'

end Language

end Trillium.Fairness
