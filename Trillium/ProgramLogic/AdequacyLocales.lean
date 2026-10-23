/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Iris.BI.WeakestPre
import Trillium.ProgramLogic.Traces
import Trillium.Prelude.Finitary

/-!
# Thread-pool and locale lemmas for adequacy
Port of the pure (WP-free) part of `trillium/program_logic/adequacy.v`; the rest of that file
(everything mentioning `iProp`, `WP`, `irisG`) is in `Trillium/ProgramLogic/Adequacy.lean`.

This file contains

* lemmas about thread pools and executions (`step_tp_length`, `valid_exec_length`,
  `locale_valid_exec`),
* `LocalesEquivFrom t0 t0' t1 t1'` (Rocq notation `locales_equiv_from`) and its lemmas,
* `fromLocaleFrom` / `fromLocale` (finding the thread of a given locale),
* `localesOfListFrom` / `localesOfList` (the list of locales of a thread pool),
* `LocalesEquivPrefixFrom` (Rocq `locales_equiv_prefix_from`),
* the pure adequacy notions `RelFinitary`, `AdequateMultiple`, `Adequate` and their lemmas.

Representation: stdpp's `is_Some o` is `o.isSome`, `l !! i ≫= to_val` is `l[i]?.bind toVal`,
`from_option f d o` is `o.elim d f`, and `f <$> l` is `l.map f`. The Rocq anonymous functions
`λ '(t, e), locale_of t e` are written `fun p => localeOf p.1 p.2`.
Lemmas that only concern `localeOf` are stated for a `LanguageCore`.
-/

namespace Trillium

open FiniteTrace Language

/-! ## Lengths of thread pools -/

section length

variable {Expr Val Ectx State Locale : Type _} [Language Expr Val Ectx State Locale]

@[rocq_alias trillium.step_tp_length]
theorem step_tp_length {c c' : List Expr × State} {oζ : Option Locale} :
    LocaleStep c oζ c' → c.1.length ≤ c'.1.length := by
  rintro (⟨t1, t2, _⟩ | ⟨t, _⟩)
  · simp
  · exact le_rfl

@[rocq_alias trillium.valid_exec_length]
theorem valid_exec_length {ex : ExecutionTrace Expr} {tp1 tp2 : List Expr} {σ1 σ2 : State} :
    ValidExec ex → ex.StartsIn (tp1, σ1) → ex.EndsIn (tp2, σ2) → tp1.length ≤ tp2.length := by
  induction ex generalizing σ1 σ2 tp1 tp2 with
  | singleton c =>
    intro _ h1 h2
    cases h1.symm.trans h2
    exact le_rfl
  | extend ex oζ c' IH =>
    intro Hval Hstarts Hends
    obtain ⟨Hval', ⟨tp', σ'⟩, Hend, Hstep⟩ := Hval.extend_inv
    cases Hends
    exact (IH Hval' Hstarts Hend).trans (step_tp_length Hstep)

end length

/-! ## Equivalence of locales -/

section locales_helpers

variable {Expr State Locale : Type _} [LanguageCore Expr State Locale]

/-- Rocq notation `locales_equiv_from t0 t0' t1 t1'`: the threads of `t1` (after `t0`) and of
`t1'` (after `t0'`) have pairwise equal locales. -/
abbrev LocalesEquivFrom (t0 t0' t1 t1' : List Expr) : Prop :=
  List.Forall₂ (fun p q => localeOf p.1 p.2 = localeOf q.1 q.2)
    (prefixesFrom t0 t1) (prefixesFrom t0' t1')

@[rocq_alias trillium.locales_equiv_from_app]
theorem locales_equiv_from_app {t0 t0' t1 t1' t2 t2' : List Expr} :
    LocalesEquivFrom t0 t0' t1 t1' → LocalesEquivFrom (t0 ++ t1) (t0' ++ t1') t2 t2' →
    LocalesEquivFrom t0 t0' (t1 ++ t2) (t1' ++ t2') := by
  intro h1 h2
  rw [LocalesEquivFrom, prefixesFrom_append, prefixesFrom_append]
  exact List.rel_append h1 h2

omit [LanguageCore Expr State Locale] in
@[rocq_alias trillium.prefixes_from_length, simp]
theorem prefixesFrom_length {A : Type _} (t0 t1 : List A) :
    (prefixesFrom t0 t1).length = t1.length := by
  induction t1 generalizing t0 with
  | nil => rfl
  | cons a t1 IH => simp [IH]

@[rocq_alias trillium.locales_equiv_from_impl]
theorem locales_equiv_from_impl {t0 t0' t1 t1' t2 t2' : List Expr} :
    t2.length = t2'.length →
    LocalesEquivFrom t0 t0' (t1 ++ t2) (t1' ++ t2') →
    LocalesEquivFrom (t0 ++ t1) (t0' ++ t1') t2 t2' := by
  intro Hlen Hequiv
  have Hlen' := Hequiv.length_eq
  simp only [prefixesFrom_length, List.length_append] at Hlen'
  have := List.forall₂_drop t1.length Hequiv
  rwa [prefixesFrom_append, prefixesFrom_append, List.drop_left' (by simp),
    List.drop_left' (by simp; omega)] at this

@[rocq_alias trillium.locales_equiv_from_refl]
theorem locales_equiv_from_refl {t0 t0' : List Expr} (t : List Expr) :
    LocalesEquiv t0 t0' → LocalesEquivFrom t0 t0' t t := by
  induction t generalizing t0 t0' with
  | nil => intro; exact .nil
  | cons e t IH =>
    intro H
    refine .cons (LanguageCore.locale_equiv t0 t0' e H) (IH ?_)
    exact locales_equiv_from_app (t0 := []) (t0' := []) H
      (.cons (LanguageCore.locale_equiv t0 t0' e H) .nil)

@[rocq_alias trillium.locales_equiv_refl]
theorem locales_equiv_refl (t : List Expr) : LocalesEquiv t t :=
  locales_equiv_from_refl t .nil

@[rocq_alias trillium.locales_equiv_snoc]
theorem locales_equiv_snoc {t0 t0' : List Expr} {e e' : Expr} {t1 t1' : List Expr} :
    LocalesEquiv t0 t0' → LocalesEquivFrom t0 t0' t1 t1' →
    localeOf (t0 ++ t1) e = localeOf (t0' ++ t1') e' →
    LocalesEquivFrom t0 t0' (t1 ++ [e]) (t1' ++ [e']) :=
  fun _ h1 h2 => locales_equiv_from_app h1 (.cons h2 .nil)

@[rocq_alias trillium.locales_equiv_snoc_same]
theorem locales_equiv_snoc_same {t0 : List Expr} {e e' : Expr} {t1 : List Expr} :
    localeOf (t0 ++ t1) e = localeOf (t0 ++ t1) e' →
    LocalesEquivFrom t0 t0 (t1 ++ [e]) (t1 ++ [e']) :=
  locales_equiv_snoc (locales_equiv_refl t0) (locales_equiv_from_refl t1 (locales_equiv_refl t0))

@[rocq_alias trillium.locales_equiv_from_middle]
theorem locales_equiv_from_middle {t0 : List Expr} {e e' : Expr} {t1 t2 : List Expr} :
    localeOf (t0 ++ t1) e = localeOf (t0 ++ t1) e' →
    LocalesEquivFrom t0 t0 (t1 ++ e :: t2) (t1 ++ e' :: t2) := by
  intro H
  refine locales_equiv_from_app (locales_equiv_from_refl t1 (locales_equiv_refl t0)) (.cons H ?_)
  refine locales_equiv_from_refl t2 ?_
  have := locales_equiv_snoc_same (t0 := []) (t1 := t0 ++ t1) H
  simpa using this

@[rocq_alias trillium.locales_equiv_middle]
theorem locales_equiv_middle {e e' : Expr} {t1 t2 : List Expr} :
    localeOf t1 e = localeOf t1 e' → LocalesEquiv (t1 ++ e :: t2) (t1 ++ e' :: t2) :=
  locales_equiv_from_middle (t0 := [])

@[rocq_alias trillium.locales_equiv_from_take]
theorem locales_equiv_from_take {t0 t0' t1 t1' : List Expr} (n : Nat) :
    LocalesEquivFrom t0 t0' t1 t1' → LocalesEquivFrom t0 t0' (t1.take n) (t1'.take n) := by
  induction n generalizing t0 t0' t1 t1' with
  | zero => intro; exact .nil
  | succ n IHn =>
    intro Hequiv
    cases t1 with
    | nil =>
      cases t1' with
      | nil => exact .nil
      | cons => cases Hequiv
    | cons e1 t1 =>
      cases t1' with
      | nil => cases Hequiv
      | cons e1' t1' =>
        cases Hequiv with
        | cons h1 h2 => exact .cons h1 (IHn h2)

@[rocq_alias trillium.locales_equiv_take]
theorem locales_equiv_take {t1 t2 : List Expr} (n : Nat) :
    LocalesEquiv t1 t2 → LocalesEquiv (t1.take n) (t2.take n) :=
  locales_equiv_from_take n

/-- Rocq `Forall2_eq`. -/
@[rocq_alias trillium.Forall2_eq]
theorem forall₂_eq_iff_map_eq {A B : Type _} (f : A → B) (xs ys : List A) :
    List.Forall₂ (fun x y => f x = f y) xs ys ↔ xs.map f = ys.map f := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp
  | cons x xs IH => cases ys <;> simp [IH]

/-- The locales of the threads of `tp` (after the threads `tp0`). -/
@[rocq_alias trillium.locales_of_list_from]
def localesOfListFrom (tp0 tp : List Expr) : List Locale :=
  (prefixesFrom tp0 tp).map fun p => localeOf p.1 p.2

/-- Rocq notation `locales_of_list tp`. -/
abbrev localesOfList (tp : List Expr) : List Locale := localesOfListFrom [] tp

@[rocq_alias trillium.locales_of_list_from_cons]
theorem localesOfListFrom_cons (es' : List Expr) (e : Expr) (es : List Expr) :
    localesOfListFrom es' (e :: es) = localeOf es' e :: localesOfListFrom (es' ++ [e]) es := rfl

@[rocq_alias trillium.locales_of_list_equiv]
theorem locales_of_list_equiv (tp0 tp0' tp1 tp2 : List Expr) :
    LocalesEquivFrom tp0 tp0' tp1 tp2 ↔ localesOfListFrom tp0 tp1 = localesOfListFrom tp0' tp2 :=
  forall₂_eq_iff_map_eq _ _ _

@[rocq_alias trillium.locales_equiv_from_transitive]
theorem locales_equiv_from_transitive {s1 s2 s3 t1 t2 t3 : List Expr} :
    LocalesEquiv s1 s2 → LocalesEquiv s2 s3 →
    LocalesEquivFrom s1 s2 t1 t2 → LocalesEquivFrom s2 s3 t2 t3 →
    LocalesEquivFrom s1 s3 t1 t3 := by
  simp only [locales_of_list_equiv]
  exact fun _ _ h1 h2 => h1.trans h2

@[rocq_alias trillium.locales_equiv_transitive]
theorem locales_equiv_transitive {t1 t2 t3 : List Expr} :
    LocalesEquiv t1 t2 → LocalesEquiv t2 t3 → LocalesEquiv t1 t3 :=
  locales_equiv_from_transitive .nil .nil

@[rocq_alias trillium.locales_equiv_from_comm]
theorem locales_equiv_from_comm {tp0 tp0' tp1 tp2 : List Expr} :
    LocalesEquivFrom tp0 tp0' tp1 tp2 → LocalesEquivFrom tp0' tp0 tp2 tp1 := by
  simp only [locales_of_list_equiv]
  exact Eq.symm

@[rocq_alias trillium.locales_equiv_from_locale_of]
theorem locales_equiv_from_locale_of {tp0 tp0' : List Expr} (tp1 tp2 tp3 : List Expr) :
    LocalesEquiv tp0 tp0' →
    (LocalesEquivFrom tp0 tp1 tp2 tp3 ↔ LocalesEquivFrom tp0' tp1 tp2 tp3) := by
  intro Heq
  have := (locales_of_list_equiv _ _ _ _).mp (locales_equiv_from_refl tp2 Heq)
  simp only [locales_of_list_equiv, this]

/-- Rocq `locales_equiv_prefix_from tp0 tp1 tp2`: the threads of `tp1` have the same locales as
the corresponding threads of a prefix of `tp2`. -/
@[rocq_alias trillium.locales_equiv_prefix_from]
def LocalesEquivPrefixFrom (tp0 tp1 tp2 : List Expr) : Prop :=
  LocalesEquivFrom tp0 tp0 tp1 (tp2.take tp1.length)

/-- Rocq notation `locales_equiv_prefix tp1 tp2`. -/
abbrev LocalesEquivPrefix (tp1 tp2 : List Expr) : Prop := LocalesEquivPrefixFrom [] tp1 tp2

@[rocq_alias trillium.locales_equiv_from_length]
theorem locales_equiv_from_length {tp0 tp0' tp1 tp2 : List Expr} :
    LocalesEquivFrom tp0 tp0' tp1 tp2 → tp1.length = tp2.length := by
  intro h
  simpa using h.length_eq

@[rocq_alias trillium.locales_equiv_prefix_from_length]
theorem locales_equiv_prefix_from_length {tp0 tp1 tp2 : List Expr} :
    LocalesEquivPrefixFrom tp0 tp1 tp2 → tp1.length ≤ tp2.length := by
  intro h
  have := locales_equiv_from_length h
  simp at this
  omega

@[rocq_alias trillium.locales_equiv_prefix_from_trans]
theorem locales_equiv_prefix_from_trans {tp0 tp1 tp2 tp3 : List Expr} :
    LocalesEquivPrefixFrom tp0 tp1 tp2 → LocalesEquivPrefixFrom tp0 tp2 tp3 →
    LocalesEquivPrefixFrom tp0 tp1 tp3 := by
  intro h1 h2
  have Hle := locales_equiv_prefix_from_length h1
  refine locales_equiv_from_transitive (locales_equiv_refl _) (locales_equiv_refl _) h1 ?_
  have := locales_equiv_from_take tp1.length h2
  rwa [List.take_take, Nat.min_eq_left Hle] at this

@[rocq_alias trillium.locales_equiv_prefix_trans]
theorem locales_equiv_prefix_trans {tp1 tp2 tp3 : List Expr} :
    LocalesEquivPrefix tp1 tp2 → LocalesEquivPrefix tp2 tp3 → LocalesEquivPrefix tp1 tp3 :=
  locales_equiv_prefix_from_trans

@[rocq_alias trillium.locales_equiv_prefix_from_drop]
theorem locales_equiv_prefix_from_drop {tp0 tp1 tp2 : List Expr} :
    LocalesEquivPrefixFrom tp0 tp1 tp2 →
    LocalesEquivFrom tp0 tp0 tp2 (tp1 ++ tp2.drop tp1.length) := by
  intro Heq
  have Hcomm := locales_equiv_from_comm Heq
  conv => lhs; rw [← List.take_append_drop tp1.length tp2]
  refine locales_equiv_from_app Hcomm (locales_equiv_from_refl _ ?_)
  exact locales_equiv_from_app (t0 := []) (t0' := []) (locales_equiv_refl tp0) Hcomm

@[rocq_alias trillium.locales_equiv_from_drop]
theorem locales_equiv_from_drop {t0 t1 t2 t2' : List Expr} :
    LocalesEquivPrefixFrom t0 t1 t2 → LocalesEquivPrefixFrom t0 t1 t2' →
    LocalesEquivFrom t0 t0 t2 t2' →
    LocalesEquivFrom (t0 ++ t1) (t0 ++ t1) (t2.drop t1.length) (t2'.drop t1.length) := by
  intro Hprefix1 Hprefix2 Hequiv
  apply locales_equiv_from_impl
  · simp [locales_equiv_from_length Hequiv]
  have Hprefix1 := locales_equiv_from_comm (locales_equiv_prefix_from_drop Hprefix1)
  have Hprefix2 := locales_equiv_prefix_from_drop Hprefix2
  have H := locales_equiv_from_transitive (locales_equiv_refl _) (locales_equiv_refl _)
    Hprefix1 Hequiv
  exact locales_equiv_from_transitive (locales_equiv_refl _) (locales_equiv_refl _) H Hprefix2

-- Rocq `fmap_fmap` is Lean core's `List.map_map`.
attribute [rocq_alias trillium.fmap_fmap] List.map_map

@[rocq_alias trillium.locales_equiv_prefix_from_drop_alt]
theorem locales_equiv_prefix_from_drop_alt {tp0 tp1 tp2 : List Expr} :
    LocalesEquivPrefixFrom tp0 tp1 tp2 →
    (prefixesFrom (tp0 ++ tp1) (tp2.drop tp1.length)).map (fun p => localeOf p.1 p.2) =
      ((prefixesFrom tp0 tp2).map (fun p => localeOf p.1 p.2)).drop tp1.length := by
  intro Hprefix
  have := (locales_of_list_equiv _ _ _ _).mp (locales_equiv_prefix_from_drop Hprefix)
  simp only [localesOfListFrom] at this
  rw [this, prefixesFrom_append, List.map_append, List.drop_left' (by simp)]

@[rocq_alias trillium.locales_equiv_prefix_drop_alt]
theorem locales_equiv_prefix_drop_alt {tp0 tp1 : List Expr} :
    LocalesEquivPrefix tp0 tp1 →
    (prefixesFrom tp0 (tp1.drop tp0.length)).map (fun p => localeOf p.1 p.2) =
      ((prefixes tp1).map (fun p => localeOf p.1 p.2)).drop tp0.length :=
  locales_equiv_prefix_from_drop_alt (tp0 := [])

end locales_helpers

/-! ## Locales of steps and executions -/

section locale_steps

variable {Expr Val Ectx State Locale : Type _} [Language Expr Val Ectx State Locale]

@[rocq_alias trillium.locale_step_equiv]
theorem locale_step_equiv {c c' : List Expr × State} {oζ : Option Locale} :
    LocaleStep c oζ c' → LocalesEquiv c.1 (c'.1.take c.1.length) := by
  rintro (⟨t1, t2, Hstep⟩ | ⟨t, _⟩)
  · rename_i e1 _ e2 _ efs
    simp only
    rw [show t1 ++ e2 :: (t2 ++ efs) = (t1 ++ e2 :: t2) ++ efs by simp,
      show (t1 ++ e1 :: t2).length = (t1 ++ e2 :: t2).length by simp, List.take_left]
    exact locales_equiv_middle (locale_step_preserve t1 Hstep)
  · simp only [List.take_length]
    exact locales_equiv_refl t

@[rocq_alias trillium.locale_valid_exec]
theorem locale_valid_exec {ex : ExecutionTrace Expr} {tp1 tp2 : List Expr} {σ1 σ2 : State} :
    ValidExec ex → ex.StartsIn (tp1, σ1) → ex.EndsIn (tp2, σ2) →
    LocalesEquiv tp1 (tp2.take tp1.length) := by
  induction ex generalizing σ1 σ2 tp1 tp2 with
  | singleton c =>
    intro _ h1 h2
    cases h1.symm.trans h2
    simp only [List.take_length]
    exact locales_equiv_refl tp1
  | extend ex oζ c' IH =>
    intro Hval Hstarts Hends
    obtain ⟨Hval', ⟨tp', σ'⟩, Hend, Hstep⟩ := Hval.extend_inv
    cases Hends
    refine locales_equiv_transitive (IH Hval' Hstarts Hend) ?_
    have Hequiv := locales_equiv_take tp1.length (locale_step_equiv Hstep)
    have Hle : tp1.length ≤ tp'.length := valid_exec_length Hval' Hstarts Hend
    simp only [List.take_take, Nat.min_eq_left Hle] at Hequiv
    exact Hequiv

@[rocq_alias trillium.locales_of_list_step_incl]
theorem localesOfList_step_incl {σ1 σ2 : State} {oζ : Option Locale} {tp1 tp2 : List Expr} :
    LocaleStep (tp1, σ1) oζ (tp2, σ2) → localesOfList tp1 ⊆ localesOfList tp2 := by
  intro H
  cases H with
  | atomic t1 t2 Hstep =>
    rename_i e1 e2 efs
    have := (locales_of_list_equiv _ _ _ _).mp
      (locales_equiv_middle (t2 := t2) (locale_step_preserve t1 Hstep))
    have h1 : localesOfList (t1 ++ e2 :: (t2 ++ efs)) =
        localesOfList (t1 ++ e2 :: t2) ++ localesOfListFrom (t1 ++ e2 :: t2) efs := by
      rw [show t1 ++ e2 :: (t2 ++ efs) = (t1 ++ e2 :: t2) ++ efs by simp]
      simp only [localesOfList, localesOfListFrom, prefixesFrom_append, List.map_append,
        List.nil_append]
    rw [h1, localesOfList, this]
    exact List.subset_append_left _ _
  | state => exact List.Subset.refl _

end locale_steps

/-! ## Finding the thread of a locale -/

section from_locale

variable {Expr State Locale : Type _} [LanguageCore Expr State Locale] [DecidableEq Locale]

/-- The first thread of `tp` (after the threads `tp0`) with locale `ζ`. -/
@[rocq_alias trillium.from_locale_from]
def fromLocaleFrom (tp0 : List Expr) : List Expr → Locale → Option Expr
  | [], _ => none
  | e :: tp', ζ => if localeOf tp0 e = ζ then some e else fromLocaleFrom (tp0 ++ [e]) tp' ζ

/-- The thread of `tp` with locale `ζ`. -/
@[rocq_alias trillium.from_locale]
def fromLocale (tp : List Expr) (ζ : Locale) : Option Expr := fromLocaleFrom [] tp ζ

@[rocq_alias trillium.from_locale_from_Some_app]
theorem fromLocaleFrom_some_append {tp0 tp : List Expr} (tp' : List Expr) {ζ : Locale}
    {e : Expr} :
    fromLocaleFrom tp0 tp ζ = some e → fromLocaleFrom tp0 (tp ++ tp') ζ = some e := by
  induction tp generalizing tp0 with
  | nil => intro h; cases h
  | cons e' tp IH =>
    simp only [fromLocaleFrom, List.cons_append]
    split
    · exact id
    · exact IH

@[rocq_alias trillium.from_locale_from_is_Some_app]
theorem fromLocaleFrom_isSome_append {tp0 tp : List Expr} (tp' : List Expr) {ζ : Locale} :
    (fromLocaleFrom tp0 tp ζ).isSome → (fromLocaleFrom tp0 (tp ++ tp') ζ).isSome := by
  intro h
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp h
  rw [fromLocaleFrom_some_append tp' he]
  rfl

@[rocq_alias trillium.from_locale_from_equiv]
theorem fromLocaleFrom_equiv {tp0 tp0' tp tp' : List Expr} {ζ : Locale} :
    LocalesEquiv tp0 tp0' → LocalesEquivFrom tp0 tp0' tp tp' →
    (fromLocaleFrom tp0 tp ζ).isSome → (fromLocaleFrom tp0' tp' ζ).isSome := by
  induction tp generalizing tp0 tp0' tp' with
  | nil => intro _ _ h; exact absurd h Bool.false_ne_true
  | cons e tp IH =>
    intro Heq0 Heq Hs
    cases tp' with
    | nil => cases Heq
    | cons e' tp' =>
      cases Heq with
      | cons Hlocs Heq =>
      simp only at Hlocs
      simp only [fromLocaleFrom] at Hs ⊢
      by_cases h : localeOf tp0 e = ζ
      · simp only [← Hlocs, h, ↓reduceIte, Option.isSome_some]
      · have h' : ¬ localeOf tp0' e' = ζ := Hlocs ▸ h
        simp only [h, h', ↓reduceIte] at Hs ⊢
        exact IH (locales_equiv_snoc (t0 := []) (t0' := []) .nil Heq0 Hlocs) Heq Hs

@[rocq_alias trillium.from_locale_from_Some]
theorem fromLocaleFrom_some {tp0 tp1 tp : List Expr} {e : Expr} :
    (tp, e) ∈ prefixesFrom tp0 tp1 → fromLocaleFrom tp0 tp1 (localeOf tp e) = some e := by
  induction tp1 generalizing tp0 with
  | nil => simp
  | cons e1 tp1 IH =>
    intro Hin
    simp only [prefixesFrom_cons, List.mem_cons, Prod.mk.injEq] at Hin
    rcases Hin with ⟨rfl, rfl⟩ | Hin
    · simp [fromLocaleFrom]
    · simp only [fromLocaleFrom]
      simp only [LanguageCore.locale_injective tp0 e1 tp1 tp e Hin, ↓reduceIte]
      exact IH Hin

@[rocq_alias trillium.locales_of_list_from_locale_from]
theorem mem_localesOfListFrom_of_fromLocaleFrom {tp0 tp1 : List Expr} {ζ : Locale} :
    (fromLocaleFrom tp0 tp1 ζ).isSome → ζ ∈ localesOfListFrom tp0 tp1 := by
  induction tp1 generalizing tp0 with
  | nil => simp [fromLocaleFrom]
  | cons e1 tp1 IH =>
    intro h
    rw [localesOfListFrom_cons, List.mem_cons]
    simp only [fromLocaleFrom] at h
    by_cases h' : localeOf tp0 e1 = ζ
    · exact .inl h'.symm
    · simp only [h', ↓reduceIte] at h
      exact .inr (IH h)

end from_locale

section from_locale_step

variable {Expr Val Ectx State Locale : Type _} [Language Expr Val Ectx State Locale]
  [DecidableEq Locale]

@[rocq_alias trillium.from_locale_step]
theorem fromLocale_step {tp1 tp2 : List Expr} {ζ : Locale} {oζ : Option Locale}
    {σ1 σ2 : State} :
    LocaleStep (tp1, σ1) oζ (tp2, σ2) → (fromLocale tp1 ζ).isSome → (fromLocale tp2 ζ).isSome := by
  intro Hstep
  cases Hstep with
  | atomic t1 t2 Hstep =>
    rename_i e1 e2 efs
    intro HiS
    rw [show t1 ++ e2 :: (t2 ++ efs) = (t1 ++ e2 :: t2) ++ efs by simp]
    apply fromLocaleFrom_isSome_append
    exact fromLocaleFrom_equiv .nil (locales_equiv_middle (locale_step_preserve t1 Hstep)) HiS
  | state => exact id

end from_locale_step

/-! ## Pure adequacy notions -/

/-- A relation between traces is finitary if every extension of a trace on the left is related
to finitely many extensions of a trace on the right. -/
@[rocq_alias trillium.rel_finitary]
def RelFinitary {A B C D : Type _} (ξ : FiniteTrace A B → FiniteTrace C D → Prop) : Prop :=
  ∀ (ex : FiniteTrace A B) (atr : FiniteTrace C D) (c' : A) (oζ : B),
    SmallerCard {p : C × D // ξ (ex :tr[oζ]: c') (atr :tr[p.2]: p.1)} ℕ

/-- Rocq's `EqDecision C, EqDecision D` assumptions are not needed. -/
@[rocq_alias trillium.rel_finitary_impl]
theorem RelFinitary.of_imp {A B C D : Type _} {ξ ξ' : FiniteTrace A B → FiniteTrace C D → Prop}
    (Himpl : ∀ ex aux, ξ ex aux → ξ' ex aux) : RelFinitary ξ' → RelFinitary ξ := by
  intro Hξ' ex aux c' oζ
  apply finite_smaller_card_nat
  have := smaller_card_nat_finite (Hξ' ex aux c' oζ)
  exact Finite.of_injective
    (fun x => (⟨x.1, Himpl _ _ x.2⟩ : {p : C × D // ξ' (ex :tr[oζ]: c') (aux :tr[p.2]: p.1)}))
    (fun x y h => Subtype.ext (by simpa using congrArg Subtype.val h))

section adequate

variable {Expr Val Ectx State Locale : Type _} [Language Expr Val Ectx State Locale]

/-- Adequacy of a thread pool `es` in state `σ1`, with postconditions `φs` for the threads:
the result of every thread satisfies its postcondition, and (if `s = NotStuck`) no thread gets
stuck. -/
@[rocq_alias trillium.adequate_multiple]
structure AdequateMultiple (s : Iris.Stuckness) (es : List Expr) (σ1 : State)
    (φs : List (Val → State → Prop)) : Prop where
  adequate_result (ex : ExecutionTrace Expr) (t2 : List Expr) (σ2 : State) (i : Nat) (v : Val) :
    i < es.length → i < φs.length → ValidExec ex → ex.StartsIn (es, σ1) →
    ex.EndsIn (t2, σ2) → t2[i]?.bind toVal = some v → (φs[i]?).elim False (fun φ => φ v σ2)
  adequate_not_stuck (ex : ExecutionTrace Expr) (t2 : List Expr) (σ2 : State) (e2 : Expr) :
    s = .NotStuck → ValidExec ex → ex.StartsIn (es, σ1) → ex.EndsIn (t2, σ2) →
    e2 ∈ t2 → NotStuck e2 σ2

@[rocq_alias trillium.adequate]
def Adequate (s : Iris.Stuckness) (e : Expr) (σ1 : State) (φ : Val → State → Prop) : Prop :=
  AdequateMultiple s [e] σ1 [φ]

@[rocq_alias trillium.adequate_multiple_alt]
theorem adequateMultiple_alt {s : Iris.Stuckness} {es : List Expr} {σ1 : State}
    {φs : List (Val → State → Prop)} :
    AdequateMultiple s es σ1 φs ↔ ∀ (ex : ExecutionTrace Expr) t2 σ2,
      ValidExec ex → ex.StartsIn (es, σ1) → ex.EndsIn (t2, σ2) →
      (∀ i v, i < es.length → i < φs.length → t2[i]?.bind toVal = some v →
        (φs[i]?).elim False (fun φ => φ v σ2)) ∧
      (∀ e2, s = .NotStuck → e2 ∈ t2 → NotStuck e2 σ2) := by
  constructor
  · rintro ⟨h1, h2⟩ ex t2 σ2 hv hs he
    exact ⟨fun i v hi1 hi2 h => h1 ex t2 σ2 i v hi1 hi2 hv hs he h,
      fun e2 hs' hin => h2 ex t2 σ2 e2 hs' hv hs he hin⟩
  · intro h
    exact ⟨fun ex t2 σ2 i v hi1 hi2 hv hs he hr => (h ex t2 σ2 hv hs he).1 i v hi1 hi2 hr,
      fun ex t2 σ2 e2 hs' hv hs he hin => (h ex t2 σ2 hv hs he).2 e2 hs' hin⟩

@[rocq_alias trillium.adequate_multiple_tp_safe]
theorem AdequateMultiple.tp_safe {es : List Expr} {ex : ExecutionTrace Expr} {t2 : List Expr}
    {σ1 σ2 : State} {φs : List (Val → State → Prop)} :
    AdequateMultiple .NotStuck es σ1 φs → ValidExec ex → ex.StartsIn (es, σ1) →
    ex.EndsIn (t2, σ2) →
    (∀ e ∈ t2, (toVal e).isSome) ∨ ∃ t3 σ3, Step (t2, σ2) (t3, σ3) := by
  intro Had Hv Hs He
  by_cases Ht2 : ∀ e ∈ t2, (toVal e).isSome
  · exact .inl Ht2
  · right
    obtain ⟨e2, H⟩ := Classical.not_forall.mp Ht2
    obtain ⟨Hin, He2⟩ := not_imp.mp H
    rcases Had.adequate_not_stuck ex t2 σ2 e2 rfl Hv Hs He Hin with h | ⟨e3, σ3, efs, h⟩
    · exact absurd h He2
    · obtain ⟨t2', t2'', rfl⟩ := List.append_of_mem Hin
      exact ⟨t2' ++ e3 :: (t2'' ++ efs), σ3, .atomic _ _ h⟩

/-- The relation established by the weakest-precondition adequacy theorem. -/
@[rocq_alias trillium.wp_adequacy_relation]
def WpAdequacyRelation (M : Model) (s : Iris.Stuckness) (φs : List (Val → Prop))
    (ex : ExecutionTrace Expr) (_atr : AuxiliaryTrace M) : Prop :=
  ∀ c, ex.EndsIn c →
    (∀ i v, i < φs.length → c.1[i]?.bind toVal = some v → (φs[i]?).elim False (fun φ => φ v)) ∧
    (∀ e2, s = .NotStuck → e2 ∈ c.1 → NotStuck e2 c.2)

@[rocq_alias trillium.wp_adequacy_relation_adequacy_multiple]
theorem wpAdequacyRelation_adequateMultiple {M : Model} {s : Iris.Stuckness} {es : List Expr}
    {σ : State} {δ : M.mstate} {φs : List (Val → Prop)}
    {ξ : ExecutionTrace Expr → AuxiliaryTrace M → Prop} :
    (∀ ex aux, ξ ex aux → WpAdequacyRelation M s φs ex aux) →
    ContinuedSimulation ξ {tr[(es, σ)]} {tr[δ]} →
    AdequateMultiple s es σ (φs.map fun φ v _ => φ v) := by
  intro Himpl Hsm
  refine adequateMultiple_alt.mpr fun ex t2 σ2 Hex Hexstr Hexend => ?_
  obtain ⟨atr, -, Hatr⟩ := simulation_does_continue Hsm ex Hexstr Hex
  obtain ⟨Hsafe, Hstuck⟩ := Himpl _ _ Hatr.rel (t2, σ2) Hexend
  refine ⟨fun i v _ Hlen2 Ht2 => ?_, Hstuck⟩
  rw [List.length_map] at Hlen2
  have := Hsafe i v Hlen2 Ht2
  rw [List.getElem?_eq_getElem Hlen2] at this
  rw [List.getElem?_map, List.getElem?_eq_getElem Hlen2]
  simpa using this

end adequate

end Trillium
