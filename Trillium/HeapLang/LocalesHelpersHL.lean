/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.Fairness.LocalesHelpers
import Trillium.HeapLang.Lang

/-!
# Locale helpers for HeapLang
Port of `heap_lang/locales_helpers_hl.v`.

In HeapLang the locale of a thread is its index in the thread pool (`localeOf c e = c.length`),
so `fromLocale` is list lookup, the locales of a thread pool are its indexes, and the set of
locales of a configuration is `{0, …, n - 1}` (stdpp's `set_seq 0 n`, iris-lean's
`LawfulSet.setSeq 0 n`).

Representation: stdpp's `imap f l` is `List.mapIdx f l`, `l !! i` is `l[i]?`.
-/

namespace Trillium.HeapLang

open Trillium Trillium.Fairness Iris.Std Language

@[rocq_alias trillium.heap_lang.from_locale_from_lookup]
theorem fromLocaleFrom_eq_some_iff (tp0 tp : List Expr) (tid : Nat) (e : Expr) :
    fromLocaleFrom tp0 tp tid = some e ↔ tp[tid - tp0.length]? = some e ∧ tp0.length ≤ tid := by
  induction tp generalizing tp0 with
  | nil => simp [fromLocaleFrom]
  | cons e1 tp1 IH =>
    simp only [fromLocaleFrom]
    by_cases h : localeOf tp0 e1 = tid
    · simp only [h, ↓reduceIte]
      rw [localeOf_eq] at h
      subst h
      simp
    · simp only [h, ↓reduceIte]
      rw [IH]
      rw [localeOf_eq] at h
      rcases Nat.lt_or_gt_of_ne h with h' | h'
      · obtain ⟨k, rfl⟩ : ∃ k, tid = tp0.length + k + 1 := ⟨tid - tp0.length - 1, by omega⟩
        simp [show tp0.length + k + 1 - tp0.length = k + 1 by omega,
          show tp0.length + k + 1 - (tp0.length + 1) = k by omega]
        omega
      · constructor
        · rintro ⟨_, h''⟩
          simp at h''
          omega
        · rintro ⟨_, h''⟩
          omega

@[rocq_alias trillium.heap_lang.from_locale_lookup]
theorem fromLocale_eq_some_iff (tp : List Expr) (tid : Nat) (e : Expr) :
    fromLocale tp tid = some e ↔ tp[tid]? = some e := by
  rw [fromLocale, fromLocaleFrom_eq_some_iff]
  simp

/-- The list of indexes `[0, …, xs.length - 1]` of a list. -/
@[rocq_alias trillium.heap_lang.indexes]
def indexes {A : Type _} (xs : List A) : List Nat := xs.mapIdx fun i _ => i

@[rocq_alias trillium.heap_lang.locales_of_list_from_indexes]
theorem localesOfListFrom_eq_mapIdx (es' es : List Expr) :
    localesOfListFrom es' es = es.mapIdx fun i _ => es'.length + i := by
  induction es generalizing es' with
  | nil => rfl
  | cons e es IH =>
    rw [localesOfListFrom_cons, IH, List.mapIdx_cons, localeOf_eq]
    congr 1
    exact congrArg (fun f => List.mapIdx f es) (funext fun i => funext fun _ => by
      simp only [List.length_append, List.length_cons, List.length_nil]; omega)

@[rocq_alias trillium.heap_lang.locales_of_list_indexes]
theorem localesOfList_eq_indexes (es : List Expr) : localesOfList es = indexes es :=
  (localesOfListFrom_eq_mapIdx [] es).trans (by simp [indexes])

@[rocq_alias trillium.heap_lang.locales_of_cfg_simpl]
theorem localesOfCfg_eq_setSeq (l : List Expr) (σ : State) :
    localesOfCfg (l, σ) = (LawfulSet.setSeq 0 l.length : GSet Nat) := by
  apply LawfulSet.ext
  intro x
  change x ∈ (LawfulSet.ofList (localesOfList l) : GSet Nat) ↔ _
  rw [← LawfulSet.mem_ofList, LawfulSet.mem_setSeq,
    localesOfList_eq_indexes, indexes, List.mem_mapIdx]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · intro hx
    exact ⟨x, by omega, rfl⟩

/-- Membership form of `localesOfCfg_eq_setSeq`. -/
theorem mem_localesOfCfg_iff_lt (l : List Expr) (σ : State) (x : Nat) :
    x ∈ localesOfCfg (l, σ) ↔ x < l.length := by
  rw [localesOfCfg_eq_setSeq, LawfulSet.mem_setSeq]
  omega

@[rocq_alias trillium.heap_lang.length_upd_middle]
theorem length_upd_middle {A : Type _} (x y : A) (l1 l2 : List A) :
    (l1 ++ x :: l2).length = (l1 ++ y :: l2).length := by
  simp

@[rocq_alias trillium.heap_lang.locale_step_sub]
theorem locale_step_sub {c1 c2 : List Expr × State} {τ : Nat} (STEP : LocaleStep c1 (some τ) c2) :
    localesOfCfg c1 ⊆ localesOfCfg c2 := by
  cases STEP with
  | atomic t1 t2 _ =>
    intro x
    rw [mem_localesOfCfg_iff_lt, mem_localesOfCfg_iff_lt]
    simp
    omega

/-- A HeapLang step forks at most one thread (Rocq: by inversion on the head step). -/
theorem primStep_efs_length_le {e1 : Expr} {σ1 : State} {e2 : Expr} {σ2 : State}
    {efs : List Expr} : primStep e1 σ1 e2 σ2 efs → efs.length ≤ 1 := by
  rintro ⟨K, e1', e2', _, _, hs⟩
  change BaseStep e1' σ1 e2' σ2 efs at hs
  cases hs <;> simp

@[rocq_alias trillium.heap_lang.locale_step_fresh_exact]
theorem locale_step_fresh_exact {c1 c2 : List Expr × State} {τ τ' : Nat}
    (STEP : LocaleStep c1 (some τ) c2) (FRESH : τ' ∈ localesOfCfg c2 \ localesOfCfg c1) :
    localesOfCfg c2 = localesOfCfg c1 ∪ {τ'} ∧ τ' ∉ localesOfCfg c1 := by
  cases STEP with
  | atomic t1 t2 Hstep =>
    rename_i e1 σ1 e2 σ2 efs
    have Hefs := primStep_efs_length_le Hstep
    rw [LawfulSet.mem_diff, mem_localesOfCfg_iff_lt, mem_localesOfCfg_iff_lt] at FRESH
    refine ⟨?_, by rw [mem_localesOfCfg_iff_lt]; exact FRESH.2⟩
    apply LawfulSet.ext
    intro x
    rw [LawfulSet.mem_union, LawfulSet.mem_singleton, mem_localesOfCfg_iff_lt,
      mem_localesOfCfg_iff_lt]
    simp only [List.length_append, List.length_cons] at FRESH ⊢
    change Nat at x
    show x < _ ↔ x < _ ∨ @Eq Nat x τ'
    omega

@[rocq_alias trillium.heap_lang.locale_step_fork_Some]
theorem locale_step_fork_some {c1 c2 : List Expr × State} {τ τ' : Nat}
    (STEP : LocaleStep c1 (some τ) c2) (FORK : stepFork c1 c2 = some τ') :
    localesOfCfg c2 = localesOfCfg c1 ∪ {τ'} ∧ τ' ∉ localesOfCfg c1 :=
  locale_step_fresh_exact STEP (gsetPick_some _ _ FORK)

@[rocq_alias trillium.heap_lang.heap_lang_locales_equiv_from_length]
theorem locales_equiv_from_of_length_eq {es10 es1 es20 es2 : List Expr} :
    es10.length = es20.length → es1.length = es2.length → LocalesEquivFrom es10 es20 es1 es2 := by
  induction es1 generalizing es10 es20 es2 with
  | nil =>
    intro _ Hlen
    cases es2 with
    | nil => exact .nil
    | cons _ _ => simp at Hlen
  | cons e es1 IH =>
    intro Hlen0 Hlen
    cases es2 with
    | nil => simp at Hlen
    | cons e' es2 =>
      refine List.Forall₂.cons (by simpa [localeOf_eq] using Hlen0) (IH ?_ ?_)
      · simp [Hlen0]
      · simpa using Hlen

@[rocq_alias trillium.heap_lang.heap_lang_locales_equiv_length]
theorem locales_equiv_of_length_eq {es1 es2 : List Expr} :
    es1.length = es2.length → LocalesEquiv es1 es2 :=
  locales_equiv_from_of_length_eq rfl

end Trillium.HeapLang
