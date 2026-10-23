/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.Fairis.Lifting
import Trillium.HeapLang.Tactics
import Trillium.HeapLang.Notation
import Trillium.Fairness.UtilsRelations

/-!
# Proof-mode support for Fairis HeapLang proofs

Port of `fairis/proofmode.v`: the tactic lemmas `tac_wp_*` for Trillium's weakest preconditions
of HeapLang with a live model, in which every step of the thread consumes one unit of fuel
from a `ζ ↦M fs` (`hasFuels ζ fs`) hypothesis, and the tactics built on them.

## Representation

* Rocq's tactic lemmas are stated on Rocq proof-mode environments (`envs_entails Δ …`,
  `envs_lookup i Δ = Some (false, P)`, `envs_delete`, `MaybeIntoLaterNEnvs`, `envs_snoc`). As in
  iris-lean's `Iris.HeapLang.ProofMode`, they are stated here on entailments `Δ ⊢ …`, where
  looking up and deleting a spatial hypothesis `P` is `Δ ⊣⊢ Δother ∗ P`, `MaybeIntoLaterNEnvs n`
  is `Δother ⊢ ▷^[n] Δ'`, and `envs_snoc` is `Δ' ∗ P`. Side conditions that are only about the
  well-formedness of Rocq environments (`i ≠ j`, `envs_lookup i Δ'other2 = None`) disappear,
  and so do the Rocq lemmas `maybe_into_latersN_envs_dom`, `maybe_into_latersN_envs_wf`,
  `envs_delete_wf`.
* Rocq's `WP e @ tid; E {{ Φ }}` (not stuck) is generalised to an arbitrary stuckness `s`
  (`WP e @ s; tid; E {{ Φ }}`); the Rocq statements are the instances `s = NotStuck`.
* `(λ m, m - n) <$> fs` is `fs.map fun _ m => m - n`.

## Tactics

The Rocq `Ltac`s are ported as Lean tactics working in iris-lean's proof mode
(`ProofModeM`), adapted from iris-lean's `Iris.HeapLang.ProofMode`:

| Rocq | Lean |
|---|---|
| `wp_expr_eval t`, `wp_expr_simpl` | `wp_expr_simp` |
| `wp_value_head` | `wp_value_head` |
| `wp_finish` | `wp_finish` |
| `wp_pure e` (`wp_pure _`) | `wp_pure e` (`wp_pure`), `e` in `tl(…)` syntax |
| `wp_pures` | `wp_pures` |
| `wp_rec`, `wp_lam` | `wp_rec`, `wp_lam` |
| `wp_if`, `wp_if_true`, `wp_if_false`, `wp_unop`, `wp_binop`, `wp_op`, `wp_let`, `wp_seq`, `wp_proj`, `wp_case`, `wp_match`, `wp_inj`, `wp_pair`, `wp_closure` | same names |
| `wp_bind e` | `wp_bind e` |
| `wp_load` | `wp_load` |
| `wp_store` | `wp_store` |
| `solve_fuel_positive` | `solve_fuel_positive` |
| `simpl_has_fuels` | `simpl_has_fuels` (simp set `fuel_map_simps`) |

Every pure step and every heap step taken by these tactics consumes one unit of fuel from the
(first) spatial hypothesis `tid ↦M fs` for the thread `tid` of the WP; the side conditions
`fs ≠ ∅` and `∀ (ρ : M.fmrole) (f : Nat), fs[ρ]? = some f → n ≤ f` are discharged automatically when `fs` is built
from `GMap.singleton`/`insert` and the fuel bounds follow by `omega` from the context;
otherwise they are left as goals. The commented-out parts of the Rocq file (`wp_apply`,
`wp_alloc`, `wp_cmpxchg`, `wp_faa`, …) have no counterpart; the corresponding steps are taken
with the lemmas of `Trillium/Fairis/Lifting.lean` and `Trillium/HeapLang/SswpLogic.lean`
(`wp_step_fuel`, `wp_step_model_singlerole`, `wp_alloc`, `wp_cmpxchg_suc`, …) and `iapply`.
-/

set_option linter.unusedSectionVars false

namespace Trillium.Fairis

open Iris Iris.BI Iris.Std Iris.ProofMode
open Trillium Trillium.HeapLang Trillium.Fairness Trillium.Language
open Iris.HeapLang (Loc HeapF)

/-! ## Fuel maps -/

section maps

variable {K : Type _} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]

theorem GMap.map_insert {V W : Type _} (m : GMap K V) (k : K) (v : V) (f : K → V → W) :
    (m.insert k v).map f = (m.map f).insert k (f k v) := by
  apply Std.ExtTreeMap.ext_getElem?
  intro k'
  simp only [Std.ExtTreeMap.getElem?_map, Std.ExtTreeMap.getElem?_insert]
  split
  · next h => rw [Std.LawfulEqOrd.eq_of_compare h]; rfl
  · rfl

theorem GMap.map_empty {V W : Type _} (f : K → V → W) : (∅ : GMap K V).map f = ∅ := by
  apply Std.ExtTreeMap.ext_getElem?
  intro k'
  simp

theorem GMap.map_singleton {V W : Type _} (k : K) (v : V) (f : K → V → W) :
    (GMap.singleton k v).map f = GMap.singleton k (f k v) := by
  rw [GMap.singleton, GMap.map_insert, GMap.map_empty, GMap.singleton]

theorem GMap.singleton_ne_empty {V : Type _} (k : K) (v : V) : GMap.singleton k v ≠ ∅ := by
  intro h
  have := congrArg (fun m : GMap K V => m[k]?) h
  simp [GMap.singleton] at this

theorem GMap.insert_ne_empty {V : Type _} (m : GMap K V) (k : K) (v : V) : m.insert k v ≠ ∅ := by
  intro h
  have := congrArg (fun m : GMap K V => m[k]?) h
  simp at this

/-- Rocq `maps_gt_n`. -/
@[rocq_alias trillium.fairis.maps_gt_n]
theorem maps_gt_n (fs : GMap K Nat) (n : Nat) :
    (∀ (ρ : K) (f : Nat), fs[ρ]? = some f → n ≤ f) →
    fs = (fs.map fun _ m => m - n).map fun _ m => n + m := by
  intro Hgt
  apply Std.ExtTreeMap.ext_getElem?
  intro ρ
  simp only [Std.ExtTreeMap.getElem?_map]
  cases h : fs[ρ]? with
  | none => rfl
  | some f =>
    have := Hgt ρ f h
    simp only [Option.map_some, Option.some.injEq]
    omega

end maps

/-! ## Tactic lemmas -/

section lemmas

variable {M : FairModel} {LM : LiveModel BaseLocale M} {GF : BundledGFunctors} [HeapGS LM GF]

@[rocq_alias trillium.fairis.tac_wp_expr_eval]
theorem tac_wp_expr_eval {Δ : IProp GF} {s : Stuckness} {tid : BaseLocale} {E : CoPset}
    {Φ : Val → IProp GF} {e e' : Expr} (heq : e = e')
    (h : Δ ⊢ WP e' @ s; tid; E {{ Φ }}) : Δ ⊢ WP e @ s; tid; E {{ Φ }} := by
  subst heq; exact h

/-- `tac_wp_pure_helper`, by induction on the pure steps. -/
theorem tac_wp_pure_helper_iterate (s : Stuckness) (tid : BaseLocale) (E : CoPset)
    (K : List ECtxItem) (Φ : Val → IProp GF) :
    ∀ (n : Nat) (e1 e2 : Expr) (fs : GMap M.fmrole Nat), fs ≠ ∅ →
    Relation.Iterate (PureStep (Λ := heapLang)) n e1 e2 →
    ⊢ (▷^[n] (hasFuels (GF := GF) tid fs -∗ WP (fill K e2) @ s; tid; E {{ Φ }})) -∗
      hasFuels tid (fs.map fun _ m => n + m) -∗ WP (fill K e1) @ s; tid; E {{ Φ }}
  | 0, e1, e2, fs, _, Hpe => by
    rw [(nsteps_0 _ _ _).1 Hpe]
    change ⊢ iprop((hasFuels (GF := GF) tid fs -∗ WP (fill K e2) @ s; tid; E {{ Φ }}) -∗
      hasFuelsPlus 0 tid fs -∗ WP (fill K e2) @ s; tid; E {{ Φ }})
    iintro H Hf
    iapply H
    iapply (has_fuel_fuels_plus_0 (GF := GF) tid fs).1 $$ Hf
  | n + 1, e1, e2, fs, Hne, Hpe => by
    obtain ⟨y, Hstep, Hrest⟩ := (relCompose_nsteps_next' _ n e1 e2).2 Hpe
    have Hne' : (fs.map fun _ m => n + m) ≠ ∅ := by
      rw [Ne, Std.ExtTreeMap.map_eq_empty_iff]; exact Hne
    have Hpe1 : PureExec True 1 (fill K e1) (fill K y) :=
      ⟨fun _ => Relation.Iterate.once (pure_step_ctx K Hstep)⟩
    iintro H Hf
    have hsplit := (has_fuels_plus_split_S (GF := GF) n tid fs).1
    unfold hasFuelsPlus at hsplit
    ihave Hf := hsplit $$ Hf
    iapply wp_step_fuel s tid E (fill K e1) _ Φ Hne' $$ [Hf]
    · inext; iexact Hf
    iapply sswp_pure_step s E (fill K e1) (fill K y) True _ Hpe1 trivial
    inext
    iintro Hf
    iapply tac_wp_pure_helper_iterate s tid E K Φ n y e2 fs Hne Hrest $$ H Hf

@[rocq_alias trillium.fairis.tac_wp_pure_helper]
theorem tac_wp_pure_helper (s : Stuckness) (tid : BaseLocale) (E : CoPset) (K : List ECtxItem)
    (e1 e2 : Expr) (fs : GMap M.fmrole Nat) (φ : Prop) (n : Nat) (Φ : Val → IProp GF) :
    fs ≠ ∅ → PureExec φ n e1 e2 → φ →
    ⊢ (▷^[n] (hasFuels (GF := GF) tid fs -∗ WP (fill K e2) @ s; tid; E {{ Φ }})) -∗
      hasFuelsPlus n tid fs -∗ WP (fill K e1) @ s; tid; E {{ Φ }} := fun Hne HPE Hφ =>
  tac_wp_pure_helper_iterate s tid E K Φ n e1 e2 fs Hne (HPE.pure_exec Hφ)

@[rocq_alias trillium.fairis.equiv_wand]
theorem equiv_wand {PROP : Type _} [BI PROP] (P Q : PROP) : P = Q → ⊢ P -∗ Q := fun h =>
  wand_intro (emp_sep.1.trans (BI.equiv_iff.1 h).1)

@[rocq_alias trillium.fairis.has_fuels_gt_n]
theorem has_fuels_gt_n (fs : GMap M.fmrole Nat) (n : Nat) (tid : BaseLocale) :
    (∀ (ρ : M.fmrole) (f : Nat), fs[ρ]? = some f → n ≤ f) →
    hasFuels (GF := GF) tid fs ⊣⊢
      hasFuels tid ((fs.map fun _ m => m - n).map fun _ m => n + m) := by
  intro H
  rw [← maps_gt_n fs n H]
  exact .rfl

@[rocq_alias trillium.fairis.has_fuels_gt_1]
theorem has_fuels_gt_1 (fs : GMap M.fmrole Nat) (tid : BaseLocale) :
    (∀ (ρ : M.fmrole) (f : Nat), fs[ρ]? = some f → 1 ≤ f) →
    hasFuels (GF := GF) tid fs ⊣⊢ hasFuelsS tid (fs.map fun _ m => m - 1) := by
  intro H
  refine (has_fuels_gt_n fs 1 tid H).trans ?_
  unfold hasFuelsS
  have : (fun (_ : M.fmrole) (m : Nat) => 1 + m) = fun _ f => f + 1 := by
    funext _ m; omega
  rw [this]
  exact .rfl

@[rocq_alias trillium.fairis.tac_wp_pure_helper_2]
theorem tac_wp_pure_helper_2 (s : Stuckness) (tid : BaseLocale) (E : CoPset)
    (K : List ECtxItem) (e1 e2 : Expr) (fs : GMap M.fmrole Nat) (φ : Prop) (n : Nat)
    (Φ : Val → IProp GF) :
    (∀ (ρ : M.fmrole) (f : Nat), fs[ρ]? = some f → n ≤ f) → fs ≠ ∅ → PureExec φ n e1 e2 → φ →
    ⊢ (▷^[n] (hasFuels (GF := GF) tid (fs.map fun _ m => m - n) -∗
        WP (fill K e2) @ s; tid; E {{ Φ }})) -∗
      hasFuels tid fs -∗ WP (fill K e1) @ s; tid; E {{ Φ }} := by
  intro Hfs Hne Hpe Hφ
  have Hne' : (fs.map fun _ m => m - n) ≠ ∅ := by
    rw [Ne, Std.ExtTreeMap.map_eq_empty_iff]; exact Hne
  iintro H Hf
  ihave Hf := (has_fuels_gt_n (GF := GF) fs n tid Hfs).1 $$ Hf
  have h := tac_wp_pure_helper (GF := GF) s tid E K e1 e2 _ φ n Φ Hne' Hpe Hφ
  unfold hasFuelsPlus at h
  iapply h $$ H Hf

#rocq_ignore trillium.fairis.maybe_into_latersN_envs_dom
  "Lemma about Rocq proof-mode environments (`envs`); iris-lean's proof mode represents contexts as `Hyps` and the tactic lemmas are stated on entailments"
#rocq_ignore trillium.fairis.maybe_into_latersN_envs_wf
  "Lemma about the well-formedness of Rocq proof-mode environments (`envs_wf`); not needed with iris-lean's `Hyps`"
#rocq_ignore trillium.fairis.envs_delete_wf
  "Lemma about the well-formedness of Rocq proof-mode environments (`envs_wf`); not needed with iris-lean's `Hyps`"

/-- Rocq `tac_wp_pure`: take the `n` pure steps from `e1` to `e2` in the evaluation context `K`,
consuming `n` units of fuel of every role of `tid ↦M fs`. `hsplit` looks up (and removes) the
fuel hypothesis, `hlater` strips `n` laters from the remaining context. -/
@[rocq_alias trillium.fairis.tac_wp_pure]
theorem tac_wp_pure {Δ Δother Δ' : IProp GF} {s : Stuckness} {tid : BaseLocale} {E : CoPset}
    {K : List ECtxItem} {e1 e2 : Expr} {φ : Prop} {n : Nat} {Φ : Val → IProp GF}
    {fs : GMap M.fmrole Nat}
    (hfs : ∀ (ρ : M.fmrole) (f : Nat), fs[ρ]? = some f → n ≤ f) (hne : fs ≠ ∅) (hpe : PureExec φ n e1 e2) (hφ : φ)
    (hsplit : Δ ⊣⊢ Δother ∗ hasFuels tid fs)
    (hlater : Δother ⊢ ▷^[n] Δ')
    (hcont : Δ' ∗ hasFuels tid (fs.map fun _ m => m - n) ⊢ WP (fill K e2) @ s; tid; E {{ Φ }}) :
    Δ ⊢ WP (fill K e1) @ s; tid; E {{ Φ }} := by
  refine hsplit.1.trans ?_
  refine (sep_mono (hlater.trans (laterN_mono n (wand_intro hcont))) .rfl).trans ?_
  exact wand_elim (wand_entails (tac_wp_pure_helper_2 s tid E K e1 e2 fs φ n Φ hfs hne hpe hφ))

@[rocq_alias trillium.fairis.tac_wp_value_nofupd]
theorem tac_wp_value_nofupd {Δ : IProp GF} {s : Stuckness} {tid : BaseLocale} {E : CoPset}
    {Φ : Val → IProp GF} {v : Val} (h : Δ ⊢ Φ v) :
    Δ ⊢ WP (Expr.val v) @ s; tid; E {{ Φ }} :=
  h.trans wp_value'

@[rocq_alias trillium.fairis.tac_wp_value]
theorem tac_wp_value {Δ : IProp GF} {s : Stuckness} {tid : BaseLocale} {E : CoPset}
    {Φ : Val → IProp GF} {v : Val} (h : Δ ⊢ |={E}=> Φ v) :
    Δ ⊢ WP (Expr.val v) @ s; tid; E {{ Φ }} :=
  h.trans wp_value_fupd'

@[rocq_alias trillium.fairis.tac_wp_bind]
theorem tac_wp_bind (K : List ECtxItem) {Δ : IProp GF} {s : Stuckness} {tid : BaseLocale}
    {E : CoPset} {Φ : Val → IProp GF} {e : Expr}
    (h : Δ ⊢ WP e @ s; tid; E {{ v, WP (fill K (Expr.val v)) @ s; tid; E {{ Φ }} }}) :
    Δ ⊢ WP (fill K e) @ s; tid; E {{ Φ }} :=
  h.trans (wp_bind K)

/-! ### Heap -/

/-- Rocq `tac_wp_load`: load from `l` (with `l ↦{q} v` in the context after stripping a later),
consuming one unit of fuel of every role of `tid ↦M fs`. -/
@[rocq_alias trillium.fairis.tac_wp_load]
theorem tac_wp_load {Δ Δother Δ' Δ'' : IProp GF} {s : Stuckness} {tid : BaseLocale}
    {E : CoPset} {K : List ECtxItem} {fs : GMap M.fmrole Nat} {l : Loc} {q : Qp} {v : Val}
    {Φ : Val → IProp GF}
    (hfs : ∀ (ρ : M.fmrole) (f : Nat), fs[ρ]? = some f → 1 ≤ f) (hne : fs ≠ ∅)
    (hsplit : Δ ⊣⊢ Δother ∗ hasFuels tid fs)
    (hlater : Δother ⊢ ▷ Δ')
    (hsplit' : Δ' ⊣⊢ Δ'' ∗ l ↦{.own q} v)
    (hcont : Δ' ∗ hasFuels tid (fs.map fun _ m => m - 1) ⊢
      WP (fill K (Expr.val v)) @ s; tid; E {{ Φ }}) :
    Δ ⊢ WP (fill K (Expr.load (.val (.lit (.loc l))))) @ s; tid; E {{ Φ }} := by
  have Hne' : (fs.map fun _ m => m - 1) ≠ ∅ := by
    rw [Ne, Std.ExtTreeMap.map_eq_empty_iff]; exact hne
  refine hsplit.1.trans ?_
  refine (sep_mono (hlater.trans (later_mono hsplit'.1)) (has_fuels_gt_1 fs tid hfs).1).trans ?_
  refine Entails.trans ?_ (wp_bind K)
  iintro ⟨⟨HΔ, Hl⟩, Hf⟩
  iapply wp_step_fuel s tid E _ _ _ Hne' $$ [Hf]
  · inext; iexact Hf
  iapply wp_load s E l q v $$ Hl
  inext
  iintro Hl Hf
  iapply wp_value'
  iapply hcont
  isplitr [Hf]
  · iapply hsplit'.2
    iframe
  · iexact Hf

/-- Rocq `tac_wp_store`: store `v'` to `l` (with `l ↦ v` in the context after stripping a later),
consuming one unit of fuel of every role of `tid ↦M fs`. -/
@[rocq_alias trillium.fairis.tac_wp_store]
theorem tac_wp_store {Δ Δother Δ' Δ'' : IProp GF} {s : Stuckness} {tid : BaseLocale}
    {E : CoPset} {K : List ECtxItem} {fs : GMap M.fmrole Nat} {l : Loc} {v v' : Val}
    {Φ : Val → IProp GF}
    (hfs : ∀ (ρ : M.fmrole) (f : Nat), fs[ρ]? = some f → 1 ≤ f) (hne : fs ≠ ∅)
    (hsplit : Δ ⊣⊢ Δother ∗ hasFuels tid fs)
    (hlater : Δother ⊢ ▷ Δ')
    (hsplit' : Δ' ⊣⊢ Δ'' ∗ l ↦ v)
    (hcont : (Δ'' ∗ l ↦ v') ∗ hasFuels tid (fs.map fun _ m => m - 1) ⊢
      WP (fill K (Expr.val (.lit .unit))) @ s; tid; E {{ Φ }}) :
    Δ ⊢ WP (fill K (Expr.store (.val (.lit (.loc l))) (.val v'))) @ s; tid; E {{ Φ }} := by
  have Hne' : (fs.map fun _ m => m - 1) ≠ ∅ := by
    rw [Ne, Std.ExtTreeMap.map_eq_empty_iff]; exact hne
  refine hsplit.1.trans ?_
  refine (sep_mono (hlater.trans (later_mono hsplit'.1)) (has_fuels_gt_1 fs tid hfs).1).trans ?_
  refine Entails.trans ?_ (wp_bind K)
  iintro ⟨⟨HΔ, Hl⟩, Hf⟩
  iapply wp_step_fuel s tid E _ _ _ Hne' $$ [Hf]
  · inext; iexact Hf
  iapply wp_store s E l v v' $$ Hl
  inext
  iintro Hl Hf
  iapply wp_value'
  iapply hcont
  iframe

/-! ### Auxiliary lemmas for the tactics -/

theorem tac_wp_post_eq {Δ : IProp GF} {s : Stuckness} {tid : BaseLocale} {E : CoPset}
    {e : Expr} {Φ Φ' : Val → IProp GF} (heq : Φ = Φ')
    (h : Δ ⊢ WP e @ s; tid; E {{ Φ' }}) : Δ ⊢ WP e @ s; tid; E {{ Φ }} := by
  subst heq; exact h

theorem tac_fuel_cont {Δ' Δn Q : IProp GF} {tid : BaseLocale} {fs fs' : GMap M.fmrole Nat}
    (heq : fs = fs') (hadd : Δ' ∗ hasFuels tid fs' ⊣⊢ Δn) (h : Δn ⊢ Q) :
    Δ' ∗ hasFuels tid fs ⊢ Q := by
  subst heq; exact hadd.1.trans h

theorem tac_fuel_cont_store {Δ Q : IProp GF} {tid : BaseLocale} {fs fs' : GMap M.fmrole Nat}
    (heq : fs = fs') (h : Δ ∗ hasFuels tid fs' ⊢ Q) : Δ ∗ hasFuels tid fs ⊢ Q := by
  subst heq; exact h

theorem tac_add_cont {PROP : Type _} [BI PROP] {Δ' P Δn Q : PROP} (hadd : Δ' ∗ P ⊣⊢ Δn)
    (h : Δn ⊢ Q) : Δ' ∗ P ⊢ Q :=
  hadd.1.trans h

theorem tac_store_cont {PROP : Type _} [BI PROP] {Δ'' P Δ1 F Δ2 Q : PROP}
    (hadd1 : Δ'' ∗ P ⊣⊢ Δ1) (hadd2 : Δ1 ∗ F ⊣⊢ Δ2) (h : Δ2 ⊢ Q) : (Δ'' ∗ P) ∗ F ⊢ Q :=
  (sep_mono hadd1.1 .rfl).trans (hadd2.1.trans h)

end lemmas

/-! ## Tactics -/

/-- Rocq `solve_fuel_positive`: prove `∀ ρ f, fs[ρ]? = some f → n ≤ f` for a fuel map `fs` built
from `GMap.singleton`, `insert` and `∅`, using `omega` (with the hypotheses of the context) for the
fuel bounds. -/
macro "solve_fuel_positive" : tactic => `(tactic| (
  intro ρ f h
  simp only [GMap.singleton, Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_empty,
    Std.ExtTreeMap.getElem?_map, Option.map_some, Option.map_none] at h
  repeat' (split at h)
  all_goals first
    | (cases h; done)
    | (simp only [Option.some.injEq] at h; subst h; omega)
    | omega))

/-- Rocq `simpl_has_fuels`: normalise the fuel maps `fs.map f` in the goal and the proof-mode
context (`GMap.map_singleton`, `GMap.map_insert`, …). -/
macro "simpl_has_fuels" : tactic => `(tactic| (
  simp only [GMap.map_singleton, GMap.map_insert, GMap.map_empty, Std.ExtTreeMap.map_map,
    Nat.sub_sub, Nat.sub_zero]))

namespace FairisTac

open Lean hiding Expr
open Lean.Elab Lean.Elab.Tactic Lean.Meta Qq

/-- The declarations used by `wp_expr_simp` to compute substitutions, evaluation-context
fillings and the results of unary/binary operators (Rocq `simpl`). -/
def wpExprSimpDecls : Array Name := #[
  ``Expr.subst, ``Expr.substStr, ``ECtxItem.fill, ``EctxiLanguage.fill_nil,
  ``EctxiLanguage.fill_cons, ``fillItem_eq, ``binOpEval, ``unOpEval,
  ``Iris.HeapLang.BinOp.evalInt, ``Iris.HeapLang.BinOp.evalBool,
  ``Option.getD_some, ``Option.map_some, ``Option.map_eq_map, ``Option.map_none,
  ``ne_eq, ``not_false_eq_true, ``not_true_eq_false, ``Iris.HeapLang.Binder.named.injEq,
  `and_self, `and_true, `true_and, `and_false, `false_and, ``ite_true, ``ite_false,
  ``id_eq]

/-- The declarations used to normalise fuel maps (Rocq `simpl_has_fuels`). -/
def fuelSimpDecls : Array Name := #[
  ``GMap.map_singleton, ``GMap.map_insert, ``GMap.map_empty, ``Std.ExtTreeMap.map_map,
  ``Nat.sub_sub, ``Nat.sub_zero]

/-- Simplify `e` with the given declarations (theorems are used as rewrite rules, definitions
are unfolded) and the default simprocs; returns the result and a proof of `e = e'`. -/
def simpEq (decls : Array Name) (e : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let mut thms : SimpTheorems := {}
  for n in decls do
    match ← getConstInfo n with
    | .thmInfo _ => thms ← thms.addConst n
    | _ => thms ← thms.addDeclToUnfold n
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← Meta.simp e ctx (simprocs := #[← Simp.getSimprocs])
  -- annotate the proof with its type: for definitional simplifications `getProof'` is `rfl : e = e`
  return (r.expr, ← mkExpectedTypeHint (← r.getProof' e) (← mkEq e r.expr))

/-- Replace the last argument of the application `e` by `v`. -/
def replaceLastArg (e v : Lean.Expr) : Lean.Expr := mkApp e.appFn! v

/-- The components of a Fairis WP goal `WP e @ s; tid; E {{ Φ }}`. -/
structure WpGoal where
  s : Lean.Expr
  E : Lean.Expr
  tid : Lean.Expr
  e : Q(Expr)
  Φ : Lean.Expr

/-- Recognise a Trillium WP `Trillium.Wp.wp s E tid e Φ`. -/
def parseWp? (goal : Lean.Expr) : MetaM (Option WpGoal) := do
  let goal := (← instantiateMVars goal).consumeMData
  match goal.getAppFnArgs with
  | (``Trillium.Wp.wp, #[_, _, _, _, _, _, s, E, tid, e, Φ]) =>
    return some { s, E, tid, e, Φ }
  | _ => return none

/-- An instantiated lemma: its arguments by binder name, the proof term and its conclusion. -/
structure InstLemma where
  args : Std.HashMap Name Lean.Expr
  mvars : Array Lean.Expr
  pf : Lean.Expr
  concl : Lean.Expr

/-- Instantiate all arguments of the lemma `n` with metavariables. -/
def instLemma (n : Name) : MetaM InstLemma := do
  let c ← mkConstWithFreshMVarLevels n
  let ty ← inferType c
  let (mvars, _, concl) ← forallMetaTelescope ty
  let mut args : Std.HashMap Name Lean.Expr := {}
  let mut t := ty
  for m in mvars do
    match t with
    | .forallE nm _ b _ => args := args.insert nm m; t := b
    | _ => break
  return { args, mvars, pf := mkAppN c mvars, concl }

/-- The argument `n` of an instantiated lemma. -/
def InstLemma.arg (L : InstLemma) (n : Name) : MetaM Lean.Expr := do
  let some m := L.args[n]? | throwError "internal error: lemma has no argument {n}"
  return m

/-- Assign the argument `n` of `L` to `v` (checking types). -/
def InstLemma.assign (L : InstLemma) (n : Name) (v : Lean.Expr) : MetaM Unit := do
  let m ← L.arg n
  unless ← isDefEq (← inferType m) (← inferType v) do
    throwError "type mismatch for argument {n}:{indentExpr (← inferType v)}\n\
      expected{indentExpr (← instantiateMVars (← inferType m))}"
  unless ← isDefEq m v do
    throwError "internal error: cannot assign argument {n}"

/-- Unify the conclusion of `L` with `target`. -/
def InstLemma.unify (L : InstLemma) (target : Lean.Expr) : MetaM Unit := do
  unless ← isDefEq L.concl target do
    throwError "cannot unify{indentExpr (← instantiateMVars L.concl)}\nwith{indentExpr target}"

/-- The type of the argument `n` of `L`, instantiated. -/
def InstLemma.argType (L : InstLemma) (n : Name) : MetaM Lean.Expr := do
  instantiateMVars (← inferType (← L.arg n))

/-- Synthesise the remaining instance arguments of `L` and return its proof. -/
def InstLemma.proof (L : InstLemma) : MetaM Lean.Expr := do
  for m in L.mvars do
    let m ← instantiateMVars m
    if m.isMVar then
      let ty ← inferType m
      if (← isClass? ty).isSome then
        let inst ← synthInstance ty
        unless ← isDefEq m inst do throwError "internal error: instance mismatch"
  instantiateMVars L.pf

/-- The right-hand side `X` of an entailment `Δ ⊢ X`. -/
def entailsRhs (ty : Lean.Expr) : Lean.Expr := ty.consumeMData.appArg!.headBeta

/-- Try to solve the goal `m` with the tactic `tac`; if it fails, either throw or add the goal
`m` to the proof mode goals. -/
def solveSideGoal (m : Lean.Expr) (tac : TSyntax `tactic) (failOnUnsolved : Bool)
    (what : String) : ProofModeM Unit := do
  let m ← instantiateMVars m
  unless m.isMVar do return
  let gs ← (observing? <| evalTacticAt tac m.mvarId!) <&> (·.getD [m.mvarId!])
  if !gs.isEmpty then
    if failOnUnsolved then
      throwIPMError "failed to solve side condition ({what}){indentExpr (← inferType m)}"
    else
      for g in gs do addMVarGoal g

/-- The tactic used for the side condition `fs ≠ ∅`. -/
def fuelNonEmptyTac : MetaM (TSyntax `tactic) :=
  `(tactic| first
    | exact GMap.singleton_ne_empty _ _
    | exact GMap.insert_ne_empty _ _ _
    | assumption
    | (simp only [GMap.singleton, Ne, Std.ExtTreeMap.map_eq_empty_iff]; done)
    | (simp only [Ne, Std.ExtTreeMap.map_eq_empty_iff]; first
        | exact GMap.singleton_ne_empty _ _
        | exact GMap.insert_ne_empty _ _ _
        | assumption))

/-- The tactic used for the side condition `∀ ρ f, fs[ρ]? = some f → n ≤ f`. -/
def fuelPositiveTac : MetaM (TSyntax `tactic) := `(tactic| solve_fuel_positive)

/-- Discharge the side condition argument `n` of `L`. -/
def InstLemma.side (L : InstLemma) (n : Name) (tac : TSyntax `tactic) (failOnUnsolved : Bool)
    (what : String) : ProofModeM Unit := do
  solveSideGoal (← L.arg n) tac failOnUnsolved what

section

variable {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)}

/-- Rocq `wp_value_head`/`wp_finish`: on a goal `WP e @ s; tid; E {{ Φ }}` in context `hyps`,
simplify `e`, and if it is a value `v`, turn the goal into `|={E}=> Φ v` (or into `Φ v` if that
is already an update or a WP). Returns the proof of the original goal. On other goals, just
adds the goal. -/
def iWpFinish {ehyps : Q($prop)} (hyps : Hyps bi ehyps) (goal : Lean.Expr) :
    ProofModeM Lean.Expr := do
  let some g ← parseWp? goal | addBIGoal hyps goal
  let target ← mkAppM ``Iris.BI.BIBase.Entails #[ehyps, goal]
  let (e', heq) ← simpEq wpExprSimpDecls g.e
  let L ← instLemma ``tac_wp_expr_eval
  L.assign `heq heq
  L.unify target
  let goal' := entailsRhs (← L.argType `h)
  let pf' ← (do
    match e'.consumeMData with
    | .app (.const ``Expr.val _) v =>
      let post := (mkApp g.Φ v).headBeta
      let noFupd := post.isAppOf ``Iris.FUpd.fupd || post.isAppOf ``Trillium.Wp.wp
      let L' ← instLemma (if noFupd then ``tac_wp_value_nofupd else ``tac_wp_value)
      L'.unify (← mkAppM ``Iris.BI.BIBase.Entails #[ehyps, goal'])
      let pfh ← addBIGoal hyps (entailsRhs (← L'.argType `h))
      L'.assign `h pfh
      L'.proof
    | _ => addBIGoal hyps goal')
  L.assign `h pf'
  L.proof

/-- Remove the first spatial hypothesis `tid ↦M fs` from `hyps`. Returns its name, its
`IVarId`, its type and the removal certificate. -/
def removeFuelHyp {ehyps : Q($prop)} (hyps : Hyps bi ehyps) (tid : Lean.Expr) :
    ProofModeM ((Name × IVarId × Lean.Expr) × RemoveHyp bi ehyps) := do
  let some res ← hyps.removeG false fun name ivar p ty => do
      if isTrue p then return none
      let ty' := (← instantiateMVars ty).consumeMData
      unless ty'.isAppOf ``hasFuels do return none
      let args := ty'.getAppArgs
      unless ← isDefEq args[args.size - 2]! tid do return none
      return some (name, ivar, ty')
    | throwIPMError "cannot find a fuel hypothesis {tid} ↦M _"
  return res

/-- Add the fuel hypothesis `hasFuels tid fs'` (with `fs'` the normalisation of the fuel map of
`fuelTy`) under the name `name` to `hyps`, and prove the continuation goal `hcontTy` of the form
`Δ' ∗ hasFuels tid fs ⊢ WP …` with `wp_finish`. -/
def fuelCont {eL : Q($prop)} (hypsL : Hyps bi eL) (name : Name) (ivar : IVarId)
    (hcontTy : Lean.Expr) : ProofModeM Lean.Expr := do
  let hcontTy := hcontTy.consumeMData
  let goal := hcontTy.appArg!
  let lhs := hcontTy.appFn!.appArg!.consumeMData
  let fuelTy := lhs.appArg!.consumeMData
  let fsMap := fuelTy.appArg!
  let (fs', heqfs) ← simpEq fuelSimpDecls fsMap
  have fuelTy' : Q($prop) := replaceLastArg fuelTy fs'
  let ⟨_, hypsN, pfAdd⟩ := hypsL.add bi name ivar q(false) fuelTy'
  let pfCont ← iWpFinish hypsN goal
  mkAppM ``tac_fuel_cont #[heqfs, pfAdd, pfCont]

/-- The pure-step core of `wp_pure`: `choose e₁` returns `(φ, n, e₂, inst)` with
`inst : PureExec φ n e₁ e₂`, or fails. -/
def iWpPure {ehyps : Q($prop)} (hyps : Hyps bi ehyps) (goal : Lean.Expr)
    (failOnUnsolved : Bool)
    (choose : Q(Expr) → ProofModeM (Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr)) :
    ProofModeM Lean.Expr := do
  let some g ← parseWp? goal | throwIPMError "the goal is not a Fairis WP"
  let target ← mkAppM ``Iris.BI.BIBase.Entails #[ehyps, goal]
  let some {result := (φ, _, _, inst), K, e' := e1} ←
      findECtx (m := ProofModeM) g.e fun _ e1 => choose e1
    | throwIPMError "cannot find a pure redex"
  let ((name, ivar, _), rem) ← removeFuelHyp hyps g.tid
  let L ← instLemma ``tac_wp_pure
  L.assign `hpe inst
  L.assign `K K
  L.assign `e1 e1
  L.assign `hsplit rem.pf
  let n ← instantiateMVars (← L.arg `n)
  let M : Lean.Expr := mkAppN (.const ``modality_laterN [u]) #[prop, n, bi]
  let ⟨_, hypsL, pfLater⟩ ← iModAction (bi1 := bi) rem.hyps' M
  L.assign `hlater pfLater
  L.unify target
  let hφ ← iSolveSidecondition (← instantiateMVars φ) (failOnUnsolved := failOnUnsolved)
  L.assign `hφ hφ
  L.side `hne (← fuelNonEmptyTac) failOnUnsolved "fuel map non-empty"
  L.side `hfs (← fuelPositiveTac) failOnUnsolved "enough fuel"
  L.assign `hcont (← fuelCont hypsL name ivar (← L.argType `hcont))
  L.proof

/-- Find any pure step for `e₁` (Rocq `wp_pure _`). -/
def findAnyPureExec (e₁ : Q(Expr)) :
    ProofModeM (Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr) := do
  let φ ← mkFreshExprMVarQ q(Prop)
  let n ← mkFreshExprMVarQ q(Nat)
  let e₂ ← mkFreshExprMVarQ q(Expr)
  let some inst ← ProofModeM.trySynthInstanceQ q(PureExec $φ $n $e₁ $e₂) | failure
  return (φ, n, e₂, inst)

/-- Run `k` on the current proof-mode goal. -/
def runWp (tacName : Name)
    (k : ∀ {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)},
      Hyps bi ehyps → Lean.Expr → ProofModeM Lean.Expr) : TacticM Unit :=
  ProofModeM.runTactic tacName fun mvar {hyps, goal, ..} => do
    let pf ← k hyps goal
    mvar.assign pf

end

/-- Strip the WP-redex search to the `load`/`store` redex and look up the points-to. -/
def iWpHeap {u : Level} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (goal : Lean.Expr) (store : Bool) : ProofModeM Lean.Expr := do
  let some g ← parseWp? goal | throwIPMError "the goal is not a Fairis WP"
  let target ← mkAppM ``Iris.BI.BIBase.Entails #[ehyps, goal]
  let some {result := (l, v'), K, ..} ← findECtx (m := ProofModeM) g.e fun _ e1 => do
      if store then
        let ~q(Expr.store (Expr.val (Val.lit (Iris.HeapLang.BaseLit.loc $l))) (Expr.val $v')) := e1 | failure
        return ((l : Lean.Expr), (v' : Lean.Expr))
      else
        let ~q(Expr.load (Expr.val (Val.lit (Iris.HeapLang.BaseLit.loc $l)))) := e1 | failure
        return ((l : Lean.Expr), (l : Lean.Expr))
    | throwIPMError (if store then "cannot find a `store` redex" else "cannot find a `load` redex")
  let ((name, ivar, _), rem) ← removeFuelHyp hyps g.tid
  let L ← instLemma (if store then ``tac_wp_store else ``tac_wp_load)
  L.assign `K K
  L.assign `l l
  if store then L.assign `v' v'
  L.assign `hsplit rem.pf
  let M : Lean.Expr := mkAppN (.const ``modality_laterN [u]) #[prop, q(1), bi]
  let ⟨_, hypsL, pfLater⟩ ← iModAction (bi1 := bi) rem.hyps' M
  L.assign `hlater pfLater
  -- look up the points-to for `l`
  let some ((pname, pivar, pty), remP) ← hypsL.removeG false fun name ivar p ty => do
      if isTrue p then return none
      let ty' := (← instantiateMVars ty).consumeMData
      unless ty'.isAppOf ``Iris.pointsTo do return none
      let args := ty'.getAppArgs
      unless ← isDefEq args[args.size - 3]! l do return none
      if store then
        unless ← isDefEq args[args.size - 2]! q(Iris.DFrac.own 1) do return none
      return some (name, ivar, ty')
    | throwIPMError "cannot find a points-to hypothesis for {l}"
  L.assign `hsplit' remP.pf
  L.unify target
  L.side `hne (← fuelNonEmptyTac) false "fuel map non-empty"
  L.side `hfs (← fuelPositiveTac) false "enough fuel"
  let hcontTy ← L.argType `hcont
  if store then
    -- add `l ↦ v'` (under the old name) to the context without the old points-to
    have ptyNew : Q($prop) := replaceLastArg pty v'
    let ⟨_, hyps1, pfAdd1⟩ := remP.hyps'.add bi pname pivar q(false) ptyNew
    let hcontTy := hcontTy.consumeMData
    let goal := hcontTy.appArg!
    let fuelTy := hcontTy.appFn!.appArg!.consumeMData.appArg!.consumeMData
    let (fs', heqfs) ← simpEq fuelSimpDecls fuelTy.appArg!
    have fuelTy' : Q($prop) := replaceLastArg fuelTy fs'
    let ⟨_, hyps2, pfAdd2⟩ := hyps1.add bi name ivar q(false) fuelTy'
    let pfCont ← iWpFinish hyps2 goal
    -- rewrite the fuel map, then combine
    let pfCont' ← mkAppM ``tac_store_cont #[pfAdd1, pfAdd2, pfCont]
    let pfCont'' ← mkAppM ``tac_fuel_cont_store #[heqfs, pfCont']
    L.assign `hcont pfCont''
  else
    L.assign `hcont (← fuelCont hypsL name ivar hcontTy)
  L.proof

end FairisTac

open Lean Elab Tactic Meta FairisTac in
/-- Rocq `wp_expr_eval simpl`/`wp_expr_simpl`: simplify the expression of the WP goal
(substitutions, evaluation contexts, operators). -/
elab "wp_expr_simp" : tactic =>
  runWp `wp_expr_simp fun {_ _ _ ehyps} hyps goal => do
    let some g ← parseWp? goal | throwIPMError "the goal is not a Fairis WP"
    let target ← mkAppM ``Iris.BI.BIBase.Entails #[ehyps, goal]
    let (_, heq) ← simpEq wpExprSimpDecls g.e
    let L ← instLemma ``tac_wp_expr_eval
    L.assign `heq heq
    L.unify target
    L.assign `h (← addBIGoal hyps (entailsRhs (← L.argType `h)))
    L.proof

open Lean Elab Tactic Meta FairisTac in
/-- Rocq `wp_finish`: simplify the expression and, if it is a value, eliminate the WP. -/
elab "wp_finish" : tactic =>
  runWp `wp_finish fun hyps goal => iWpFinish hyps goal

open Lean Elab Tactic Meta FairisTac in
/-- Rocq `wp_value_head`: eliminate a WP of a value. -/
elab "wp_value_head" : tactic =>
  runWp `wp_value_head fun hyps goal => do
    let some g ← parseWp? goal | throwIPMError "the goal is not a Fairis WP"
    unless g.e.consumeMData.isAppOf ``Expr.val do throwIPMError "the expression is not a value"
    iWpFinish hyps goal

open Lean Elab Tactic Meta FairisTac Qq in
/-- Rocq `wp_pure e`: take a pure step of a redex matching `e` (`tl(…)` syntax, `_` for holes)
in the WP goal, consuming one unit of fuel per step from the thread's `tid ↦M fs` hypothesis.
`wp_pure` is `wp_pure _`. With `+!failOnUnsolved`, fails instead of leaving side conditions. -/
elab "wp_pure" flag:("+!failOnUnsolved")? colGt ppSpace focus:tl_exp:10 : tactic =>
  runWp `wp_pure fun hyps goal => do
    let focus ← Term.elabTermEnsuringType (← `(tl($focus))) q(Trillium.HeapLang.Expr)
    iWpPure hyps goal flag.isSome fun e₁ => do
      guard <| ← isDefEq e₁ focus
      findAnyPureExec e₁

macro "wp_pure" : tactic => `(tactic| wp_pure _)
macro "wp_pure" "+!failOnUnsolved" : tactic => `(tactic| wp_pure +!failOnUnsolved _)

/-- Rocq `wp_pures`: take all pure steps (whose side conditions can be discharged), then
`wp_finish`. -/
macro "wp_pures" : tactic =>
  `(tactic| first
    | (wp_pure +!failOnUnsolved; repeat wp_pure +!failOnUnsolved)
    | wp_finish)

open Lean Elab Tactic Meta FairisTac Qq in
/-- Rocq `wp_rec`: beta-reduce the innermost application whose head is a (possibly hidden
behind a definition) recursive function. -/
elab "wp_rec" : tactic =>
  runWp `wp_rec fun hyps goal => do
    iWpPure hyps goal false fun e₁ => do
      let ~q(Expr.app (Expr.val $f) (Expr.val $a)) := e₁ | failure
      let f'' ← whnf f
      have f' : Q(Val) := f''
      let ~q(Val.rec_ $fb $xb $body) := f' | failure
      have : $f =Q Val.rec_ $fb $xb $body := ⟨⟩
      let h : Q(AsRecV $f $fb $xb $body) := q(⟨rfl⟩)
      let inst : Q(PureExec True 1 (Expr.app (Expr.val $f) (Expr.val $a))
        ((Expr.subst $fb $f $body).subst $xb $a)) := q(@pure_beta $fb $xb $body $f $a $h)
      return (q(True), q(1), q((Expr.subst $fb $f $body).subst $xb $a), inst)

macro "wp_lam" : tactic => `(tactic| wp_rec)
macro "wp_if" : tactic => `(tactic| wp_pure (if _ then _ else _))
macro "wp_if_true" : tactic => `(tactic| wp_pure (if #true then _ else _))
macro "wp_if_false" : tactic => `(tactic| wp_pure (if #false then _ else _))
macro "wp_unop" : tactic => `(tactic| wp_pure (&(Trillium.HeapLang.Expr.unop _ _)))
macro "wp_binop" : tactic => `(tactic| wp_pure (&(Trillium.HeapLang.Expr.binop _ _ _)))
macro "wp_op" : tactic => `(tactic| first | wp_unop | wp_binop)
macro "wp_let" : tactic =>
  `(tactic| (wp_pure (&(Trillium.HeapLang.Expr.rec_ .anon (.named _) _)); wp_lam))
macro "wp_seq" : tactic =>
  `(tactic| (wp_pure (&(Trillium.HeapLang.Expr.rec_ .anon .anon _)); wp_lam))
macro "wp_proj" : tactic => `(tactic| first | wp_pure (fst(_)) | wp_pure (snd(_)))
macro "wp_case" : tactic => `(tactic| wp_pure (&(Trillium.HeapLang.Expr.case _ _ _)))
macro "wp_inj" : tactic => `(tactic| first | wp_pure (injl(_)) | wp_pure (injr(_)))
macro "wp_pair" : tactic => `(tactic| wp_pure ((_, _)))
macro "wp_closure" : tactic => `(tactic| wp_pure (&(Trillium.HeapLang.Expr.rec_ _ _ _)))
macro "wp_match" : tactic => `(tactic| (wp_case; wp_pure (&(Trillium.HeapLang.Expr.rec_ _ _ _)); wp_lam))

open Lean Elab Tactic Meta FairisTac Qq in
/-- Rocq `wp_bind e`: focus on the subexpression matching `e` (`tl(…)` syntax) by applying
`wp_bind` with the corresponding evaluation context. -/
elab "wp_bind" colGt ppSpace focus:tl_exp:10 : tactic =>
  runWp `wp_bind fun {_ _ _ ehyps} hyps goal => do
    let some g ← parseWp? goal | throwIPMError "the goal is not a Fairis WP"
    let focus ← Term.elabTermEnsuringType (← `(tl($focus))) q(Trillium.HeapLang.Expr)
    let some {K, e' := e, ..} ← findECtx (m := ProofModeM) g.e fun _ e => do
        guard <| ← isDefEq e focus
      | throwIPMError "cannot find {focus} in {g.e}"
    let K ← instantiateMVars K
    if K.isAppOf ``List.nil then return ← addBIGoal hyps goal
    let target ← mkAppM ``Iris.BI.BIBase.Entails #[ehyps, goal]
    let L ← instLemma ``tac_wp_bind
    L.assign `K K
    L.assign `e e
    L.unify target
    let hTy := entailsRhs (← L.argType `h)
    let some g' ← parseWp? hTy | throwIPMError "internal error"
    let (Φ', heq) ← simpEq wpExprSimpDecls g'.Φ
    let L' ← instLemma ``tac_wp_post_eq
    L'.assign `heq heq
    L'.unify (← mkAppM ``Iris.BI.BIBase.Entails #[ehyps, hTy])
    L'.assign `h (← addBIGoal hyps (entailsRhs (← L'.argType `h)))
    let _ := Φ'
    L.assign `h (← L'.proof)
    L.proof

open Lean Elab Tactic Meta FairisTac in
/-- Rocq `wp_load`: after `wp_pures`, load from `l` using a hypothesis `l ↦{q} v` (behind a
later), consuming one unit of fuel from the thread's `tid ↦M fs` hypothesis. -/
elab "wp_load" : tactic => do
  evalTactic (← `(tactic| wp_pures))
  runWp `wp_load fun hyps goal => iWpHeap hyps goal false

open Lean Elab Tactic Meta FairisTac in
/-- Rocq `wp_store`: after `wp_pures`, store to `l` using a hypothesis `l ↦ v` (behind a
later), consuming one unit of fuel from the thread's `tid ↦M fs` hypothesis. -/
elab "wp_store" : tactic => do
  evalTactic (← `(tactic| wp_pures))
  runWp `wp_store fun hyps goal => iWpHeap hyps goal true


/-! ## Tests -/

section tests

variable {M : FairModel} {LM : LiveModel BaseLocale M} {GF : BundledGFunctors} [HeapGS LM GF]

example (tid : BaseLocale) (ρ : M.fmrole) (f : Nat) (hf : f > 20) (l : Loc)
    (Φ : Val → IProp GF) :
    ⊢ (tid ↦M GMap.singleton ρ f) -∗ l ↦ Val.lit (.int 0) -∗
      ((tid ↦M GMap.singleton ρ (f - 8)) -∗ l ↦ Val.lit (.int 1) -∗ Φ (.lit (.int 1))) -∗
      WP tl(let x := !#l; #l ← x + #1; !#l) @[tid] ⊤ {{ v, Φ v }} := by
  iintro Hf Hl HΦ
  wp_load
  wp_pures
  wp_store
  wp_load
  iapply HΦ $$ Hf Hl

example (tid : BaseLocale) (ρ : M.fmrole) (f : Nat) (hf : f > 20) (l : Loc)
    (Φ : Val → IProp GF) :
    ⊢ (tid ↦M GMap.singleton ρ f) -∗ l ↦ Val.lit (.int 0) -∗
      ((tid ↦M GMap.singleton ρ (f - 7)) -∗ l ↦ Val.lit (.int 1) -∗ Φ (.lit (.int 2))) -∗
      WP tl(if #true then (v(&(tl_val(λ n, n ← !n + #1))) #l; #2) else #3) @[tid] ⊤
        {{ v, Φ v }} := by
  iintro Hf Hl HΦ
  wp_if_true
  wp_bind (_ #l)
  wp_lam
  wp_load
  wp_store
  wp_pures
  iapply HΦ $$ Hf Hl

end tests

end Trillium.Fairis
