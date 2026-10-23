/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Iris.BI.Lib.Fixpoint
import Iris.BI.Lib.FixpointBanach
import Trillium.Prelude.IrisExtraction
import Trillium.ProgramLogic.AdequacyLocales
import Trillium.ProgramLogic.WeakestPre

/-!
# Adequacy of Trillium's weakest preconditions

Port of the program-logic part of `trillium/program_logic/adequacy.v` (the pure thread-pool and
locale lemmas are in `Trillium/ProgramLogic/AdequacyLocales.lean`).

## Main definitions

* `wptpFrom t0 s t Φs` / `wptp s t Φs` (Rocq notations `wptp_from` / `wptp`): weakest
  preconditions for all threads of the thread pool `t` (started after the threads `t0`),
  with postconditions `Φs`.
* `postsOf t Φs` (Rocq notation `posts_of`): the postconditions of the threads of `t` that have
  terminated.
* `newPosts t t'` (Rocq notation `newposts`): the fork postconditions of the threads `t'` has in
  addition to `t`.
* `configWp`: configuration steps preserve the state interpretation.
* `gsim GF M s ξ` (Rocq `Gsim Σ M s ξ`): the guarded simulation, the guarded fixpoint of
  `gsimPre`.
* `fupdToBupd` (Rocq `fupd_to_bupd`).
* `relAlwaysHolds`, `relAlwaysHoldsWithTraceInv`, `relAlwaysHolds0`, `curPosts`.

## Main results

* `wp_strong_adequacy_multiple_helper`: a weakest precondition proof gives the guarded
  simulation `gsim`.
* `simulation_correspondence_multiple`: for a finitary relation, `⊢ gsim … ` gives the
  meta-level `ContinuedSimulation`.
* `wp_strong_adequacy`, `wp_strong_adequacy_multiple`, `adequacy_xi`, `sim_and_adequacy_xi`, …

## Representation

* Rocq's `let _ : irisG Λ M Σ := IrisG _ _ _ Hinv stateI fork_post in …` is
  `letI _ : IrisG Expr M GF := { stateInterp := stateI, forkPost := forkPost }; …` (the
  `InvGS_gen .hasNoLC GF` field is found by instance resolution from the bound `Hinv`).
* stdpp's `omap f (zip_with pair t Φs)` is `(t.zip Φs).filterMap f`.
* As in Rocq, fancy updates are eliminated into the plain goal `gsim …` with the
  `fupdToBupd` token (`fupdToBupd_elim`, `fupdToBupd_fupd_step_fupdN`), whose soundness is
  derived from iris-lean's `fupd_soundness_no_lc_unfold`. The Löb induction of
  `wp_strong_adequacy_multiple_helper` is the separate lemma `wp_strong_adequacy_loop`.
* Rocq's unused assumptions `invGpreS Σ` (in `simulation_correspondence*`) and
  `EqDecision (mlabel M), EqDecision M` (in `adequacy_*xi`) are dropped.
-/

namespace Trillium

open Iris Iris.BI Iris.Std Iris.ProofMode Iris.OFE FiniteTrace Language
open Iris.ProgramLogic (ToVal EvContext EvContextOps)

variable {Expr Val Ectx State Locale : Type _} [Language Expr Val Ectx State Locale]
variable {GF : BundledGFunctors} {M : Model}

/-! ## Thread pools and their postconditions -/

section defs

variable [IrisG Expr M GF]

/-- Rocq notation `wptp_from t0 s t Φs`: weakest preconditions for all threads of `t`, where the
thread `e` with prefix `tp` (relative to `t0`) has locale `localeOf tp e`. -/
abbrev wptpFrom (t0 : List Expr) (s : Stuckness) (t : List Expr) (Φs : List (Val → IProp GF)) :
    IProp GF :=
  iprop([∗list] p;Φ ∈ prefixesFrom t0 t;Φs, WP p.2 @ s; (localeOf p.1 p.2); ⊤ {{ Φ }})

/-- Rocq notation `wptp s t Φs`. -/
abbrev wptp (s : Stuckness) (t : List Expr) (Φs : List (Val → IProp GF)) : IProp GF :=
  wptpFrom [] s t Φs

end defs

/-- Rocq notation `posts_of t Φs`: the postconditions of the terminated threads of `t`. -/
abbrev postsOf (t : List Expr) (Φs : List (Val → IProp GF)) : IProp GF :=
  iprop([∗list] vΦ ∈ (t.zip Φs).filterMap
      (fun x : Expr × (Val → IProp GF) => (toVal x.1).map fun v => (v, x.2)),
    vΦ.2 vΦ.1)

/-- Rocq notation `newelems t t'`: the threads `t'` has in addition to its prefix `t`. -/
abbrev newElems (t t' : List Expr) : List Expr := t'.drop t.length

section defs

variable [IrisG Expr M GF]

/-- Rocq notation `newposts t t'`: the fork postconditions of the new threads of `t'`. -/
abbrev newPosts (t t' : List Expr) : List (Val → IProp GF) :=
  (prefixesFrom t (newElems t t')).map fun p => forkPost (localeOf p.1 p.2)

/-- Configuration steps (that do not involve any thread) preserve the state interpretation. -/
@[rocq_alias trillium.config_wp]
def configWp : IProp GF :=
  iprop(□ ∀ (ex : ExecutionTrace Expr) (atr : AuxiliaryTrace M) (c1 : List Expr × State)
      (σ2 : State),
    ⌜ValidExec ex⌝ → ⌜ex.EndsIn c1⌝ → ⌜LanguageCore.configStep (Expr := Expr) c1.2 σ2⌝ →
    stateInterp ex atr ={⊤,∅}=∗ |={∅}▷=>^[ex.length + 1] |={∅,⊤}=>
      ∃ (δ2 : M.mstate) (ℓ : M.mlabel),
        stateInterp (ex :tr[none]: (c1.1, σ2)) (atr :tr[ℓ]: δ2))

@[rocq_alias trillium.config_wp_persistent]
instance configWp_persistent : Persistent (configWp (GF := GF)) := by
  unfold configWp; infer_instance

/-- Rocq `cur_posts tp e0 Φ0`: the postconditions of the terminated threads of `tp`, the main
thread `e0` having postcondition `Φ0`. -/
@[rocq_alias trillium.cur_posts]
def curPosts (tp : List Expr) (e0 : Expr) (Φ0 : Val → IProp GF) : IProp GF :=
  postsOf tp (Φ0 :: (prefixesFrom [e0] (tp.drop 1)).map fun p => forkPost (localeOf p.1 p.2))

/-- The relation `ξ` holds for all reachable traces, given a trace invariant `traceInv` that
is maintained along the execution. -/
@[rocq_alias trillium.rel_always_holds_with_trace_inv]
def relAlwaysHoldsWithTraceInv (s : Stuckness)
    (traceInv : ExecutionTrace Expr → AuxiliaryTrace M → IProp GF) (Φs : List (Val → IProp GF))
    (ξ : ExecutionTrace Expr → AuxiliaryTrace M → Prop) (c1 : List Expr × State)
    (c2 : M.mstate) : IProp GF :=
  iprop(∀ (ex : ExecutionTrace Expr) (atr : AuxiliaryTrace M) (c : List Expr × State),
    ⌜ValidSystemTrace ex atr⌝ -∗
    ⌜ex.StartsIn c1⌝ -∗
    ⌜atr.StartsIn c2⌝ -∗
    ⌜ex.EndsIn c⌝ -∗
    ⌜∀ ex' atr' oζ ℓ, ex.Contract oζ ex' → atr.Contract ℓ atr' → ξ ex' atr'⌝ -∗
    ⌜∀ e2, s = .NotStuck → e2 ∈ c.1 → NotStuck e2 c.2⌝ -∗
    ⌜LocalesEquiv c1.1 (c.1.take c1.1.length)⌝ -∗
    stateInterp ex atr -∗
    postsOf c.1 (Φs ++ newPosts c1.1 c.1) -∗
    □ (stateInterp ex atr ∗
        (∀ ex' atr' oζ ℓ, ⌜ex.Contract oζ ex'⌝ → ⌜atr.Contract ℓ atr'⌝ → traceInv ex' atr')
        ={⊤}=∗ stateInterp ex atr ∗ traceInv ex atr) ∗
    ((∀ ex' atr' oζ ℓ, ⌜ex.Contract oζ ex'⌝ → ⌜atr.Contract ℓ atr'⌝ → traceInv ex' atr')
      ={⊤,∅}=∗ ⌜ξ ex atr⌝))

/-- The relation `ξ` holds for all reachable traces. -/
@[rocq_alias trillium.rel_always_holds]
def relAlwaysHolds (s : Stuckness) (Φs : List (Val → IProp GF))
    (ξ : ExecutionTrace Expr → AuxiliaryTrace M → Prop) (c1 : List Expr × State)
    (c2 : M.mstate) : IProp GF :=
  iprop(∀ (ex : ExecutionTrace Expr) (atr : AuxiliaryTrace M) (c : List Expr × State),
    ⌜ValidSystemTrace ex atr⌝ -∗
    ⌜ex.StartsIn c1⌝ -∗
    ⌜atr.StartsIn c2⌝ -∗
    ⌜ex.EndsIn c⌝ -∗
    ⌜∀ ex' atr' oζ ℓ, ex.Contract oζ ex' → atr.Contract ℓ atr' → ξ ex' atr'⌝ -∗
    ⌜∀ e2, s = .NotStuck → e2 ∈ c.1 → NotStuck e2 c.2⌝ -∗
    ⌜LocalesEquiv c1.1 (c.1.take c1.1.length)⌝ -∗
    stateInterp ex atr -∗
    postsOf c.1 (Φs ++ newPosts c1.1 c.1) -∗
    |={⊤,∅}=> ⌜ξ ex atr⌝)

/-- The relation `ξ` holds for all reachable traces of a single-threaded program `e1`, the state
interpretation being `stateI`. -/
@[rocq_alias trillium.rel_always_holds0]
def relAlwaysHolds0 (ξ : ExecutionTrace Expr → AuxiliaryTrace M → Prop) (s : Stuckness)
    (stateI : ExecutionTrace Expr → AuxiliaryTrace M → IProp GF) (Φ0 : Val → IProp GF)
    (e1 : Expr) (σ1 : State) (δ1 : M.mstate) : IProp GF :=
  iprop(∀ (ex : ExecutionTrace Expr) (atr : AuxiliaryTrace M) (c : List Expr × State),
    ⌜ValidSystemTrace ex atr⌝ -∗
    ⌜ex.StartsIn ([e1], σ1)⌝ -∗
    ⌜atr.StartsIn δ1⌝ -∗
    ⌜ex.EndsIn c⌝ -∗
    ⌜∀ ex' atr' oζ ℓ, ex.Contract oζ ex' → atr.Contract ℓ atr' → ξ ex' atr'⌝ -∗
    ⌜∀ e2, s = .NotStuck → e2 ∈ c.1 → NotStuck e2 c.2⌝ -∗
    ⌜LocalesEquiv [e1] (c.1.take [e1].length)⌝ -∗
    stateI ex atr -∗
    curPosts c.1 e1 Φ0 ={⊤,∅}=∗ ⌜ξ ex atr⌝)

end defs

/-! ## The guarded simulation -/

section gsim

variable (GF M) in
/-- One unfolding of the guarded simulation (Rocq `Gsim_pre`). The stuckness `s` is not used
(as in Rocq). -/
@[rocq_alias trillium.Gsim_pre]
def gsimPre (_s : Stuckness) (ξ : ExecutionTrace Expr → AuxiliaryTrace M → Prop)
    (gsim : ExecutionTrace Expr → AuxiliaryTrace M → IProp GF) :
    ExecutionTrace Expr → AuxiliaryTrace M → IProp GF :=
  fun ex atr => iprop(▷ (⌜ξ ex atr⌝ ∧
    ∀ (c : List Expr × State) (oζ : Option Locale) (c' : List Expr × State),
      ⌜ex.EndsIn c⌝ → ⌜LocaleStep c oζ c'⌝ →
      ▷ ▷^[ex.length + 1] ∃ (δ' : M.mstate) (ℓ : M.mlabel),
        gsim (ex :tr[oζ]: c') (atr :tr[ℓ]: δ')))

@[rocq_alias trillium.Gsim_pre_contractive]
instance gsimPre_contractive (s : Stuckness) (ξ : ExecutionTrace Expr → AuxiliaryTrace M → Prop) :
    OFE.Contractive (gsimPre GF M s ξ) where
  distLater_dist := by
    intro n g g' Hg ex atr
    refine (BILaterContractive.toContractive (PROP := IProp GF)).distLater_dist fun m hm => ?_
    refine BI.and_ne.ne .rfl ?_
    refine BI.forall_ne fun c => BI.forall_ne fun oζ => BI.forall_ne fun c' => ?_
    refine BI.imp_ne.ne .rfl <| BI.imp_ne.ne .rfl ?_
    refine BI.later_ne.ne <| (laterN_ne _).ne ?_
    exact BI.exists_ne fun δ' => BI.exists_ne fun ℓ => Hg m hm _ _

variable (GF M) in
/-- The guarded simulation (Rocq `Gsim Σ M s ξ`): every step of the execution can be matched,
after some laters, by a step of the auxiliary trace, and `ξ` holds all along. -/
@[rocq_alias trillium.Gsim]
def gsim (s : Stuckness) (ξ : ExecutionTrace Expr → AuxiliaryTrace M → Prop) :
    ExecutionTrace Expr → AuxiliaryTrace M → IProp GF :=
  fixpoint (gsimPre GF M s ξ)

theorem gsim_unfold {s : Stuckness} {ξ : ExecutionTrace Expr → AuxiliaryTrace M → Prop}
    (ex : ExecutionTrace Expr) (atr : AuxiliaryTrace M) :
    gsim GF M s ξ ex atr = gsimPre GF M s ξ (gsim GF M s ξ) ex atr :=
  congrFun (congrFun (fixpoint_unfold (gsimPre GF M s ξ).toContractiveHom) ex) atr

@[rocq_alias trillium.is_except_0_wptp]
instance gsim_isExcept0 {s : Stuckness} {ξ : ExecutionTrace Expr → AuxiliaryTrace M → Prop}
    {ex : ExecutionTrace Expr} {atr : AuxiliaryTrace M} : IsExcept0 (gsim GF M s ξ ex atr) where
  is_except0 := by
    rw [gsim_unfold]
    exact except0_later

@[rocq_alias trillium.Gsim_plain]
instance gsim_plain {s : Stuckness} {ξ : ExecutionTrace Expr → AuxiliaryTrace M → Prop}
    {ex : ExecutionTrace Expr} {atr : AuxiliaryTrace M} : Plain (gsim GF M s ξ ex atr) := by
  have H : ∀ ex atr, Plain ((gsimPre GF M s ξ).toContractiveHom.fixpoint ex atr) := by
    refine ContractiveHom.fixpoint_ind (gsimPre GF M s ξ).toContractiveHom
      (fun f => ∀ ex atr, Plain (f ex atr)) ?_ (fun _ _ => iprop(emp)) (fun _ _ => inferInstance)
      ?_ ?_
    · intro A B h hA
      subst h
      exact hA
    · intro f hf ex atr
      have : ∀ ex atr, Plain (f ex atr) := hf
      show Plain (gsimPre GF M s ξ f ex atr)
      unfold gsimPre
      infer_instance
    · refine LimitPreserving.forall _ fun ex => LimitPreserving.forall _ fun atr => ?_
      exact limitPreserving_plain (fun f : ExecutionTrace Expr → AuxiliaryTrace M → IProp GF => f ex atr)
        (Φne := ⟨fun _ _ _ h => h ex atr⟩)
  exact H ex atr

end gsim

/-! ## Helper lemmas for adequacy -/

section helpers

variable [IrisG Expr M GF]

/-- Postconditions of forked threads only depend on the locales of the threads. -/
@[rocq_alias trillium.locales_of_list_from_fork_post]
theorem map_forkPost_eq_of_map_localeOf_eq (xs ys : List (List Expr × Expr)) :
    xs.map (fun p => localeOf p.1 p.2) = ys.map (fun p => localeOf p.1 p.2) →
    xs.map (fun p => forkPost (GF := GF) (localeOf p.1 p.2)) =
      ys.map (fun p => forkPost (GF := GF) (localeOf p.1 p.2)) := by
  intro h
  have := congrArg (List.map (forkPost (GF := GF))) h
  simpa only [List.map_map, Function.comp_def] using this

@[rocq_alias trillium.wp_take_step]
theorem wp_take_step {s : Stuckness} {Φ : Val → IProp GF} {ex : ExecutionTrace Expr}
    {atr : AuxiliaryTrace M} {tp1 tp2 : List Expr} {e1 e2 : Expr} {σ1 σ2 : State}
    {efs : List Expr} {ζ : Locale}
    (Hex : ValidExec ex) (Hstp : primStep e1 σ1 e2 σ2 efs)
    (Hei : ex.EndsIn (tp1 ++ e1 :: tp2, σ1)) (Hlocale : localeOf tp1 e1 = ζ) :
    ⊢ stateInterp ex atr -∗ WP e1 @ s; ζ; ⊤ {{ Φ }} ={⊤,∅}=∗
      |={∅}▷=>^[ex.length + 1] |={∅,⊤}=>
      ∃ (δ' : M.mstate) (ℓ : M.mlabel),
        stateInterp (ex :tr[some ζ]: (tp1 ++ e2 :: (tp2 ++ efs), σ2)) (atr :tr[ℓ]: δ') ∗
        WP e2 @ s; ζ; ⊤ {{ Φ }} ∗
        [∗list] i ↦ ef ∈ efs,
          WP ef @ s; (localeOf (tp1 ++ e1 :: (tp2 ++ efs.take i)) ef); ⊤
            {{ forkPost (localeOf (tp1 ++ e1 :: (tp2 ++ efs.take i)) ef) }} := by
  rw [wp_unfold.to_eq]
  simp only [wp.pre, Language.val_stuck Hstp]
  have Hloc : localeOf tp1 (fill (EvContextOps.empty : Ectx) e1) = ζ := by
    rw [EvContext.fill_empty, Hlocale]
  have Hends : ex.EndsIn (tp1 ++ fill (EvContextOps.empty : Ectx) e1 :: tp2, σ1) := by
    rw [EvContext.fill_empty]; exact Hei
  iintro HSI Hwp
  imod Hwp $$ %ex %atr %EvContextOps.empty %tp1 %tp2 %σ1 %Hex %Hloc %Hends HSI with ⟨-, Hwp⟩
  imodintro
  ihave Hwp := Hwp $$ %e2 %σ2 %efs %Hstp
  simp only [EvContext.fill_empty]
  iexact Hwp

@[rocq_alias trillium.wp_not_stuck]
theorem wp_not_stuck {ex : ExecutionTrace Expr} {atr : AuxiliaryTrace M} {K : Ectx}
    {tp1 tp2 : List Expr} {σ : State} {e : Expr} {s : Stuckness} {Φ : Val → IProp GF}
    {ζ : Locale} (Hex : ValidExec ex) (Hends : ex.EndsIn (tp1 ++ fill K e :: tp2, σ))
    (Hlocale : localeOf tp1 e = ζ) :
    ⊢ stateInterp ex atr -∗ WP e @ s; ζ; ⊤ {{ Φ }} ={⊤}=∗
      stateInterp ex atr ∗ WP e @ s; ζ; ⊤ {{ Φ }} ∗
      ⌜s = .NotStuck → NotStuck e ex.last.2⌝ := by
  iintro HSI Hwp
  imod fupd_keep_plain_sep (E' := ∅) (P := iprop(⌜s = .NotStuck → NotStuck e ex.last.2⌝))
    (R := iprop(stateInterp ex atr ∗ WP e @ s; ζ; ⊤ {{ Φ }})) $$ [] [HSI Hwp]
    with ⟨%H, HSI, Hwp⟩
  · iintro ⟨HSI, Hwp⟩
    ieval (rewrite [wp_unfold.to_eq]) at Hwp
    cases hv : toVal e with
    | some v =>
      simp only [wp.pre, hv]
      iapply fupd_mask_intro_discard LawfulSet.empty_subset
      ipureintro
      intro _
      exact .inl (by simp [hv])
    | none =>
      simp only [wp.pre, hv]
      have Hloc : localeOf tp1 (fill K e) = ζ := by rw [Language.locale_fill, Hlocale]
      imod Hwp $$ %ex %atr %K %tp1 %tp2 %σ %Hex %Hloc %Hends HSI with ⟨%Hred, -⟩
      imodintro
      ipureintro
      intro hs
      subst hs
      rw [Hends.last_eq]
      exact .inr Hred
  · iframe
  imodintro
  iframe
  ipureintro
  exact H

@[rocq_alias trillium.wptp_from_same_locales]
theorem wptpFrom_same_locales {t0' t0 : List Expr} {s : Stuckness} {tp : List Expr}
    {Φs : List (Val → IProp GF)} :
    LocalesEquiv t0 t0' → wptpFrom t0' s tp Φs ⊢ wptpFrom t0 s tp Φs := by
  induction tp generalizing Φs t0 t0' with
  | nil => intro _; exact .rfl
  | cons e tp IH =>
    intro H
    cases Φs with
    | nil => exact .rfl
    | cons Φ Φs =>
      have h := LanguageCore.locale_equiv t0 t0' e H
      refine sep_mono ?_ (IH ?_)
      · show WP e @ s; (localeOf t0' e); ⊤ {{ Φ }} ⊢ WP e @ s; (localeOf t0 e); ⊤ {{ Φ }}
        rw [h]
      · exact locales_equiv_from_app (t0 := []) (t0' := []) H (.cons (by simpa using h) .nil)

@[rocq_alias trillium.wptp_not_stuck]
theorem wptp_not_stuck {ex : ExecutionTrace Expr} {atr : AuxiliaryTrace M} {σ : State}
    {tp t0 t0' trest : List Expr} {s : Stuckness} {Φs : List (Val → IProp GF)}
    (Hsame : LocalesEquiv t0 t0') (Hexvalid : ValidExec ex)
    (Hex : ex.EndsIn (t0 ++ tp ++ trest, σ)) :
    ⊢ stateInterp ex atr -∗ wptpFrom t0' s tp Φs ={⊤}=∗
      stateInterp ex atr ∗ wptpFrom t0 s tp Φs ∗
      ⌜∀ e, e ∈ tp → s = .NotStuck → NotStuck e ex.last.2⌝ := by
  iintro HSI Ht
  ihave Ht := wptpFrom_same_locales Hsame $$ Ht
  imod fupd_keep_plain_sep (E' := ⊤)
    (P := iprop(⌜∀ e, e ∈ tp → s = .NotStuck → NotStuck e ex.last.2⌝))
    (R := iprop(stateInterp ex atr ∗ wptpFrom t0 s tp Φs)) $$ [] [HSI Ht]
    with ⟨%H, HSI, Ht⟩
  · iintro ⟨HSI, Ht⟩
    iapply BIFUpdate.mono pure_forall.mpr
    iapply (fupd_pure_forall ⊤ ⊤ _ LawfulSet.subset_refl).mpr
    iintro %e
    by_cases He : e ∈ tp
    · obtain ⟨t1, t2, rfl⟩ := List.append_of_mem He
      ieval (unfold wptpFrom; rewrite [prefixesFrom_append, prefixesFrom_cons]) at Ht
      icases BigSepL2.bigSepL2_app_inv_left $$ Ht with ⟨%Φs1, %Φs2', %-, -, Ht2⟩
      icases BigSepL2.bigSepL2_cons_inv_left.mp $$ Ht2 with ⟨%Φ, %Φs2, %-, He, -⟩
      have Hends : ex.EndsIn ((t0 ++ t1) ++ fill (EvContextOps.empty : Ectx) e :: (t2 ++ trest), σ) := by
        rw [EvContext.fill_empty]; simpa using Hex
      imod wp_not_stuck Hexvalid Hends rfl $$ HSI He with ⟨-, -, %H⟩
      imodintro
      ipureintro
      exact fun _ => H
    · iapply fupd_intro
      ipureintro
      exact fun h => absurd h He
  · iframe
  imodintro
  iframe
  ipureintro
  exact H

@[rocq_alias trillium.wptp_not_stuck_same]
theorem wptp_not_stuck_same {ex : ExecutionTrace Expr} {atr : AuxiliaryTrace M} {σ : State}
    {tp t0 trest : List Expr} {s : Stuckness} {Φs : List (Val → IProp GF)}
    (Hexvalid : ValidExec ex) (Hex : ex.EndsIn (t0 ++ tp ++ trest, σ)) :
    ⊢ stateInterp ex atr -∗ wptpFrom t0 s tp Φs ={⊤}=∗
      stateInterp ex atr ∗ wptpFrom t0 s tp Φs ∗
      ⌜∀ e, e ∈ tp → s = .NotStuck → NotStuck e ex.last.2⌝ :=
  wptp_not_stuck (locales_equiv_refl t0) Hexvalid Hex

@[rocq_alias trillium.wp_of_val_post]
theorem wp_of_val_post {e : Expr} {s : Stuckness} {Φ : Val → IProp GF} {ζ : Locale} :
    ⊢ WP e @ s; ζ; ⊤ {{ Φ }} ={⊤}=∗
      (toVal e).elim iprop(True) (fun v => iprop(|~{⊤}~| Φ v)) ∗
      ((toVal e).elim iprop(True) (fun v => iprop(|~{⊤}~| Φ v)) -∗ WP e @ s; ζ; ⊤ {{ Φ }}) := by
  iintro Hwp
  cases hv : toVal e with
  | some v =>
    simp only [Option.elim]
    ieval (rewrite [wp_unfold.to_eq]) at Hwp
    simp only [wp.pre, hv]
    imodintro
    iframe
    iintro H
    ieval (rewrite [wp_unfold.to_eq])
    simp only [wp.pre, hv]
    iexact H
  | none =>
    simp only [Option.elim]
    imodintro
    isplitr
    · itrivial
    · iintro -
      iexact Hwp

@[rocq_alias trillium.wptp_app]
theorem wptp_app {s : Stuckness} {t0 t1 t0t1 : List Expr} {Φs1 : List (Val → IProp GF)}
    {t2 : List Expr} {Φs2 : List (Val → IProp GF)} (Ht : t0t1 = t0 ++ t1) :
    ⊢ wptpFrom t0 s t1 Φs1 -∗ wptpFrom t0t1 s t2 Φs2 -∗ wptpFrom t0 s (t1 ++ t2) (Φs1 ++ Φs2) := by
  subst Ht
  iintro H1 H2
  ihave %Hlen := BigSepL2.bigSepL2_length $$ H1
  unfold wptpFrom
  rw [prefixesFrom_append]
  iapply (BigSepL2.bigSepL2_append (.inl Hlen)).mpr
  iframe

@[rocq_alias trillium.wptp_cons_r]
theorem wptp_cons_r {s : Stuckness} {e : Expr} {Φ : Val → IProp GF} {Φs : List (Val → IProp GF)}
    {t0 t1 : List Expr} :
    ⊢ WP e @ s; (localeOf (t0 ++ t1) e); ⊤ {{ Φ }} -∗ wptpFrom t0 s t1 Φs -∗
      wptpFrom t0 s (t1 ++ [e]) (Φs ++ [Φ]) := by
  iintro H1 H2
  unfold wptpFrom
  rw [prefixesFrom_append, prefixesFrom_cons, prefixesFrom_nil]
  iapply BigSepL2.bigSepL2_snoc.mpr
  iframe

@[rocq_alias trillium.wptp_cons_l]
theorem wptp_cons_l {s : Stuckness} {e : Expr} {Φ : Val → IProp GF} {t : List Expr}
    {Φs : List (Val → IProp GF)} {t0 : List Expr} :
    ⊢ WP e @ s; (localeOf t0 e); ⊤ {{ Φ }} -∗ wptpFrom (t0 ++ [e]) s t Φs -∗
      wptpFrom t0 s (e :: t) (Φ :: Φs) := by
  iintro H1 H2
  unfold wptpFrom
  rw [prefixesFrom_cons]
  iapply BigSepL2.bigSepL2_cons.mpr
  iframe

@[rocq_alias trillium.wptp_of_val_post]
theorem wptp_of_val_post {t : List Expr} {s : Stuckness} {Φs : List (Val → IProp GF)}
    {t0 : List Expr} :
    ⊢ wptpFrom t0 s t Φs -∗ |~{⊤}~| postsOf t Φs ∗ (postsOf t Φs -∗ wptpFrom t0 s t Φs) := by
  induction t generalizing Φs t0 with
  | nil =>
    iintro Ht
    imodintro
    isplitr
    · iempintro
    · iintro -
      iexact Ht
  | cons e t IH =>
    iintro Ht
    ieval (unfold wptpFrom; rewrite [prefixesFrom_cons]) at Ht
    icases BigSepL2.bigSepL2_cons_inv_left.mp $$ Ht with ⟨%Φ, %Φs', %rfl, He, Ht⟩
    imod wp_of_val_post $$ He with ⟨Hpost, Hback⟩
    imod IH $$ Ht with ⟨Ht, Htback⟩
    cases hv : toVal e with
    | some v =>
      simp only [postsOf, List.zip_cons_cons, List.filterMap_cons, hv, Option.map_some,
        Option.elim]
      imod Hpost
      imodintro
      iframe
      iintro ⟨Hpost, Htpost⟩
      iapply wptp_cons_l $$ [Hpost Hback] [Htpost Htback]
      · iapply Hback
        imodintro
        iexact Hpost
      · iapply Htback $$ Htpost
    | none =>
      simp only [postsOf, List.zip_cons_cons, List.filterMap_cons, hv, Option.map_none,
        Option.elim]
      imodintro
      iframe
      iintro Hefspost
      iapply wptp_cons_l $$ [Hback] [Hefspost Htback]
      · iapply Hback
        itrivial
      · iapply Htback $$ Hefspost

@[rocq_alias trillium.forkposts_locales_equiv]
theorem forkposts_locales_equiv {t0 t0' t1 t1' : List Expr} :
    LocalesEquivFrom t0 t0' t1 t1' →
    (prefixesFrom t0 t1).map (fun p => forkPost (GF := GF) (localeOf p.1 p.2)) =
      (prefixesFrom t0' t1').map (fun p => forkPost (GF := GF) (localeOf p.1 p.2)) :=
  fun H => map_forkPost_eq_of_map_localeOf_eq _ _ ((locales_of_list_equiv _ _ _ _).mp H)

@[rocq_alias trillium.newposts_locales_equiv_helper]
theorem newposts_locales_equiv_helper {t0 t0' t1 t1' t : List Expr} :
    t1.length = t1'.length → LocalesEquiv t0 t0' →
    (prefixesFrom t0 (newElems t1 t)).map (fun p => forkPost (GF := GF) (localeOf p.1 p.2)) =
      (prefixesFrom t0' (newElems t1' t)).map
        (fun p => forkPost (GF := GF) (localeOf p.1 p.2)) := by
  intro Hlen H
  simp only [newElems, Hlen]
  exact forkposts_locales_equiv (locales_equiv_from_refl _ H)

@[rocq_alias trillium.newposts_locales_equiv]
theorem newposts_locales_equiv {t0 t0' t : List Expr} :
    LocalesEquiv t0 t0' → newPosts (GF := GF) t0 t = newPosts t0' t :=
  fun H => newposts_locales_equiv_helper (locales_equiv_from_length H) H

@[rocq_alias trillium.newposts_same_empty, simp]
theorem newposts_same_empty {t : List Expr} : newPosts (GF := GF) t t = [] := by
  simp [newPosts, newElems]

@[rocq_alias trillium.new_threads_wptp_from]
theorem new_threads_wptp_from {s : Stuckness} {t efs : List Expr} :
    ([∗list] i ↦ ef ∈ efs,
      WP ef @ s; (localeOf (t ++ efs.take i) ef); ⊤
        {{ forkPost (localeOf (t ++ efs.take i) ef) }}) ⊣⊢
    wptpFrom t s efs (newPosts (GF := GF) t (t ++ efs)) := by
  simp only [newPosts, newElems, List.drop_left]
  induction efs generalizing t with
  | nil => exact .rfl
  | cons ef efs IH =>
    unfold wptpFrom
    simp only [prefixesFrom_cons, List.map_cons]
    refine sep_congr ?_ ?_
    · simp only [List.take_zero, List.append_nil]
      exact .rfl
    · have := IH (t := t ++ [ef])
      simp only [List.take_succ_cons, List.append_assoc, List.singleton_append] at this ⊢
      exact this

@[rocq_alias trillium.take_step]
theorem take_step {s : Stuckness} {Φs : List (Val → IProp GF)} {ex : ExecutionTrace Expr}
    {atr : AuxiliaryTrace M} {c c' : List Expr × State} {oζ : Option Locale}
    (Hexvalid : ValidExec ex) (Hexe : ex.EndsIn c) (Hstep : LocaleStep c oζ c') :
    ⊢ configWp -∗ stateInterp ex atr -∗ wptp s c.1 Φs ={⊤,∅}=∗
      |={∅}▷=>^[ex.length + 1] |={∅,⊤}=>
      ⌜∀ e2, s = .NotStuck → e2 ∈ c'.1 → NotStuck e2 c'.2⌝ ∗
      ∃ (δ' : M.mstate) (ℓ : M.mlabel),
        stateInterp (ex :tr[oζ]: c') (atr :tr[ℓ]: δ') ∗
        postsOf c'.1 (Φs ++ newPosts c.1 c'.1) ∗
        (postsOf c'.1 (Φs ++ newPosts c.1 c'.1) -∗ wptp s c'.1 (Φs ++ newPosts c.1 c'.1)) := by
  unfold configWp
  cases Hstep with
  | @atomic e1 σ1 e2 σ2 efs t1 t2 Hpstep =>
    dsimp only
    iintro #Hcfg HSI Hc1
    have Hpres := Language.locale_step_preserve t1 Hpstep
    ieval (unfold wptp wptpFrom; rewrite [prefixesFrom_append, prefixesFrom_cons, List.nil_append]) at Hc1
    icases BigSepL2.bigSepL2_app_inv_left $$ Hc1 with ⟨%Φs1, %Φs2', %rfl, Ht1, Het2⟩
    icases BigSepL2.bigSepL2_cons_inv_left.mp $$ Het2 with ⟨%Φ, %Φs2, %rfl, He, Ht2⟩
    imod wp_take_step Hexvalid Hpstep Hexe rfl $$ HSI He with He
    imodintro
    iapply step_fupdN_wand $$ He
    iintro He
    imod He with ⟨%δ', %ℓ, HSI, He2, Hefs⟩
    have Hloc : ∀ i, localeOf (t1 ++ e1 :: (t2 ++ efs.take i)) =
        localeOf ((t1 ++ e2 :: t2) ++ efs.take i) := by
      intro i
      funext ef
      have := locales_equiv_middle (t2 := t2 ++ efs.take i) Hpres
      simpa using LanguageCore.locale_equiv _ _ ef this
    ieval (simp only [Hloc]) at Hefs
    ihave Hefs := (new_threads_wptp_from (GF := GF)).mp $$ Hefs
    have Hvalid' : ValidExec (ex :tr[some (localeOf t1 e1)]: (t1 ++ e2 :: (t2 ++ efs), σ2)) :=
      Hexvalid.extend Hexe (.atomic t1 t2 Hpstep)
    imod wptp_not_stuck_same (σ := σ2) (trest := []) Hvalid' (by simp) $$ HSI Hefs
      with ⟨HSI, Hefs, %Hns1⟩
    imod wptp_not_stuck_same (σ := σ2) (t0 := []) (trest := e2 :: (t2 ++ efs)) Hvalid'
      (by simp) $$ HSI Ht1 with ⟨HSI, Ht1, %Hns2⟩
    imod wptp_not_stuck (σ := σ2) (t0 := t1 ++ [e2]) (trest := efs)
      (locales_equiv_from_app (t0 := []) (t0' := []) (locales_equiv_refl t1)
        (.cons (by simpa using Hpres.symm) .nil)) Hvalid' (by simp) $$ HSI Ht2
      with ⟨HSI, Ht2, %Hns3⟩
    have Hends2 : (ex :tr[some (localeOf t1 e1)]: (t1 ++ e2 :: (t2 ++ efs), σ2)).EndsIn
        (t1 ++ fill (EvContextOps.empty : Ectx) e2 :: (t2 ++ efs), σ2) := by
      rw [EvContext.fill_empty]; rfl
    imod wp_not_stuck Hvalid' Hends2 Hpres.symm $$ HSI He2 with ⟨HSI, He2, %Hns4⟩
    ihave Ht2efs := wptp_app (t0t1 := t1 ++ e2 :: t2) (by simp) $$ Ht2 Hefs
    ieval (rewrite [Hpres]) at He2
    ihave He2t2efs := wptp_cons_l $$ He2 Ht2efs
    ihave Hc2 := wptp_app (t0 := []) (by simp) $$ Ht1 He2t2efs
    ihave Hc2 := wptp_of_val_post $$ Hc2
    imod preStep_elim $$ HSI Hc2 with ⟨HSI, Hc2posts, Hc2back⟩
    have Hnp : Φs1 ++ Φ :: (Φs2 ++ newPosts (t1 ++ e2 :: t2) ((t1 ++ e2 :: t2) ++ efs)) =
        (Φs1 ++ Φ :: Φs2) ++ newPosts (GF := GF) (t1 ++ e1 :: t2) (t1 ++ e2 :: (t2 ++ efs)) := by
      rw [newposts_locales_equiv (t0 := t1 ++ e1 :: t2) (t0' := t1 ++ e2 :: t2)
        (locales_equiv_middle Hpres)]
      simp
    have Htp : t1 ++ (e2 :: (t2 ++ efs)) = t1 ++ e2 :: (t2 ++ efs) := rfl
    ieval (rewrite [Hnp]) at Hc2posts Hc2back
    imodintro
    isplitr
    · ipureintro
      intro e hs hin
      simp only [List.mem_append, List.mem_cons] at hin
      simp only [last] at Hns1 Hns2 Hns3 Hns4
      rcases hin with hin | rfl | hin | hin
      · exact Hns2 e hin hs
      · simpa using Hns4 hs
      · exact Hns3 e hin hs
      · exact Hns1 e hin hs
    iexists δ', ℓ
    simp only [List.append_assoc, List.cons_append] at *
    iframe
  | @state σ1 σ2 t Hcfgstep =>
    dsimp only
    iintro #Hcfg HSI Hc1
    ihave Hcfg := Hcfg $$ %ex %atr %(t, σ1) %σ2 %Hexvalid %Hexe %Hcfgstep HSI
    imod Hcfg
    imodintro
    iapply step_fupdN_wand $$ Hcfg
    iintro Hcfg
    imod Hcfg with ⟨%δ2, %ℓ, HSI⟩
    have Hvalid' : ValidExec (ex :tr[none]: (t, σ2)) := Hexvalid.extend Hexe (.state t Hcfgstep)
    imod wptp_not_stuck (σ := σ2) (t0 := []) (t0' := []) (trest := []) .nil Hvalid' (by simp)
      $$ HSI Hc1 with ⟨HSI, Hc1, %Hns⟩
    ihave Hc1 := wptp_of_val_post $$ Hc1
    imod preStep_elim $$ HSI Hc1 with ⟨HSI, Hc1posts, Hc1back⟩
    imodintro
    isplitr
    · ipureintro
      intro e hs hin
      exact Hns e hin hs
    iexists δ2, ℓ
    simp only [newposts_same_empty, List.append_nil]
    iframe

omit [IrisG Expr M GF] in
/-- `prefixesFrom` commutes with `take`. (Helper, not in Rocq.) -/
theorem prefixesFrom_take {A : Type _} (t l : List A) (n : Nat) :
    prefixesFrom t (l.take n) = (prefixesFrom t l).take n := by
  induction l generalizing t n with
  | nil => simp [prefixesFrom_nil]
  | cons x l IH =>
    cases n with
    | zero => simp [prefixesFrom_nil]
    | succ n => simp [prefixesFrom_cons, IH]

/-- The fork postconditions of the threads created in two consecutive pieces of an execution.
(Helper; inlined in the Rocq proof of `wp_strong_adequacy_multiple_helper`.) -/
theorem newPosts_append {es tp tp' : List Expr} (Htake : LocalesEquiv es (tp.take es.length))
    (Hlen : es.length ≤ tp.length) (Hstep : LocalesEquiv tp (tp'.take tp.length)) :
    newPosts (GF := GF) es tp ++ newPosts tp tp' = newPosts es tp' := by
  have Hlen' : tp.length ≤ tp'.length := by
    have := locales_equiv_from_length Hstep
    simp only [List.length_take] at this
    omega
  simp only [newPosts, newElems, ← List.map_append]
  apply map_forkPost_eq_of_map_localeOf_eq
  rw [List.map_append, locales_equiv_prefix_drop_alt Htake, locales_equiv_prefix_drop_alt Hstep,
    locales_equiv_prefix_drop_alt (locales_equiv_prefix_trans Htake Hstep)]
  have h1 : (prefixes tp).map (fun p => localeOf p.1 p.2) =
      ((prefixes tp').map (fun p => localeOf p.1 p.2)).take tp.length := by
    have := (locales_of_list_equiv _ _ _ _).mp Hstep
    simp only [localesOfListFrom] at this
    rw [this, prefixesFrom_take, List.map_take]
  rw [h1]
  generalize hL : (prefixes tp').map (fun p => localeOf p.1 p.2) = L
  have hLlen : L.length = tp'.length := by simp [← hL]
  conv_rhs => rw [← List.take_append_drop (tp.length - es.length) (L.drop es.length)]
  rw [List.drop_take, List.drop_drop]
  congr 2
  omega

end helpers

/-! ## Eliminating fancy updates into plain goals -/

section fupdToBupd

/-- Masks form a discrete OFE (needed for the greatest fixpoint below). -/
local instance : OFE CoPset := OFE.ofDiscrete _

variable {hlc : HasLC} [InvGS_gen hlc GF]

/-- One unfolding of `fupdToBupd` (Rocq `fupd_to_bupd_aux`). -/
@[rocq_alias trillium.fupd_to_bupd_aux]
def fupdToBupdAux (rec : CoPset → IProp GF) (E1 : CoPset) : IProp GF :=
  iprop(∀ (P : IProp GF) (E2 : CoPset), (|={E1,E2}=> (rec E2 -∗ P)) ==∗ ◇ P)

/-- `fupdToBupd E` is a token that allows eliminating fancy updates (starting at mask `E`) into
basic updates whose result is guarded by `◇` (Rocq `fupd_to_bupd`). -/
@[rocq_alias trillium.fupd_to_bupd]
def fupdToBupd : CoPset → IProp GF :=
  bi_greatest_fixpoint (fupdToBupdAux (GF := GF))

@[rocq_alias trillium.fupd_to_bupd_aux_bi_mono]
instance fupdToBupdAux_biMono : BIMonoPred (fupdToBupdAux (GF := GF)) where
  mono_pred {Φ Ψ} _ _ := by
    unfold fupdToBupdAux
    iintro #H %E1 HE %P %E2 HP
    iapply HE
    imod HP
    imodintro
    iintro HΨ
    iapply HP
    iapply H $$ HΨ
  mono_pred_ne := ⟨fun {_ _ _} h => by cases h; exact .rfl⟩

@[rocq_alias trillium.fupd_to_bupd_unfold]
theorem fupdToBupd_unfold (E : CoPset) :
    fupdToBupd (GF := GF) E = fupdToBupdAux fupdToBupd E :=
  greatest_fixpoint_unfold _

omit [InvGS_gen hlc GF] in
@[rocq_alias trillium.fupd_to_bupd_soundness_no_lc]
theorem fupd_to_bupd_soundness_no_lc [InvGpreS GF] (Q : IProp GF)
    (Hfupd : ∀ (_ : InvGS_gen .hasNoLC GF), fupdToBupd ⊤ ⊢ Q) : ⊢ |==> Q := by
  istart
  imod fupd_soundness_no_lc_unfold (GF := GF) 0 ⊤ with ⟨%Hinv, %ω, -, Hω, #H⟩
  imodintro
  iapply Hfupd Hinv
  have : NonExpansive ω := ⟨fun {_ _ _} h => by cases h; exact .rfl⟩
  unfold fupdToBupd
  iapply greatest_fixpoint_coiter (F := fupdToBupdAux (GF := GF)) ω $$ [] %⊤ Hω
  unfold fupdToBupdAux
  iintro !> %E1 Hω %P %E2 HP
  imod H $$ %E1 %E2 %_ HP Hω with H'
  imodintro
  imod H' with ⟨Hω, HP⟩
  imodintro
  iapply HP $$ Hω

omit [InvGS_gen hlc GF] in
@[rocq_alias trillium.fupd_to_bupd_soundness_no_lc']
theorem fupd_to_bupd_soundness_no_lc' [InvGpreS GF] (Q : IProp GF) [Plain Q]
    (Hfupd : ∀ (_ : InvGS_gen .hasNoLC GF), fupdToBupd ⊤ ⊢ Q) : ⊢ Q :=
  (fupd_to_bupd_soundness_no_lc Q Hfupd).trans bupd_elim

/-- Eliminate a fancy update into a plain goal using the `fupdToBupd` token. (Helper, inlined in
Rocq.) -/
theorem fupdToBupd_elim {E1 E2 : CoPset} {P : IProp GF} [Plain P] [IsExcept0 P] :
    fupdToBupd E1 ⊢ (|={E1,E2}=> (fupdToBupd E2 -∗ P)) -∗ P := by
  rw [fupdToBupd_unfold]
  unfold fupdToBupdAux
  iintro H Hupd
  iapply is_except0
  iapply (bupd_elim (P := iprop(◇ P)))
  iapply H $$ %P %E2 Hupd

private instance isExcept0_laterN {P : IProp GF} [IsExcept0 P] (n : Nat) :
    IsExcept0 iprop(▷^[n] P) := by
  cases n with
  | zero => assumption
  | succ n => exact isExcept0_later _

/-- Eliminate `n` steps of fancy updates into a plain goal. (Helper, inlined in Rocq.) -/
theorem fupdToBupd_step_fupdN {E : CoPset} {P : IProp GF} [Plain P] [IsExcept0 P] (n : Nat) :
    fupdToBupd ∅ ⊢ (|={∅}▷=>^[n] |={∅,E}=> (fupdToBupd E -∗ P)) -∗ ▷^[n] P := by
  induction n with
  | zero =>
    simp only [step_fupdN]
    iintro F H
    iapply fupdToBupd_elim $$ F H
  | succ n IH =>
    simp only [step_fupdN]
    iintro F H
    iapply fupdToBupd_elim (E2 := ∅) $$ F
    imod H
    imodintro
    iintro F
    iapply (laterN_succ_left n).mpr
    inext
    iapply fupdToBupd_elim (E2 := ∅) $$ F
    imod H
    imodintro
    iintro F
    iapply IH $$ F H

/-- Eliminate a fancy update followed by `n` steps into a plain goal. (Helper, inlined in Rocq.) -/
theorem fupdToBupd_fupd_step_fupdN {E : CoPset} {P : IProp GF} [Plain P] [IsExcept0 P] (n : Nat) :
    fupdToBupd E ⊢ (|={E,∅}=> |={∅}▷=>^[n] |={∅,E}=> (fupdToBupd E -∗ P)) -∗ ▷^[n] P := by
  iintro F H
  iapply fupdToBupd_elim (E2 := ∅) $$ F
  imod H
  imodintro
  iintro F
  iapply fupdToBupd_step_fupdN $$ F H

end fupdToBupd

/-! ## Adequacy: from weakest preconditions to the guarded simulation -/

section adequacy_loop

variable [IrisG Expr M GF]

/-- The Löb induction at the heart of `wp_strong_adequacy_multiple_helper`. (Inlined in Rocq.) -/
theorem wp_strong_adequacy_loop (s : Stuckness) (ξ : ExecutionTrace Expr → AuxiliaryTrace M → Prop)
    (es : List Expr) (σ : State) (δ : M.mstate)
    (traceInv : ExecutionTrace Expr → AuxiliaryTrace M → IProp GF) (Φs : List (Val → IProp GF)) :
    ⊢ configWp -∗ ∀ (ex : ExecutionTrace Expr) (atr : AuxiliaryTrace M) (c1 : List Expr × State),
      ⌜ValidSystemTrace ex atr ∧ ex.StartsIn (es, σ) ∧ ex.EndsIn c1 ∧ atr.StartsIn δ ∧
        (∀ ex' atr' oζ ℓ, ex.Contract oζ ex' → atr.Contract ℓ atr' → ξ ex' atr') ∧
        LocalesEquiv es (c1.1.take es.length) ∧ es.length ≤ c1.1.length⌝ -∗
      relAlwaysHoldsWithTraceInv s traceInv Φs ξ (es, σ) δ -∗
      stateInterp ex atr -∗
      (∀ ex' atr' oζ ℓ, ⌜ex.Contract oζ ex'⌝ → ⌜atr.Contract ℓ atr'⌝ → traceInv ex' atr') -∗
      wptp s c1.1 (Φs ++ newPosts es c1.1) -∗
      |={⊤}=> (fupdToBupd ⊤ -∗ gsim GF M s ξ ex atr) := by
  iintro #Hcfg
  iloeb as IH
  iintro %ex %atr %c1 %Hextras Hstep HSI HTI Htp
  obtain ⟨Hv, Hex, Hc1, Hatr, Hξ, Htake, Htakelen⟩ := Hextras
  obtain ⟨tp, σ1'⟩ := c1
  dsimp only at Htake Htakelen ⊢
  have Hexv := Hv.validExec
  imod wptp_not_stuck (t0 := []) (t0' := []) (trest := []) .nil Hexv (by simpa using Hc1)
    $$ HSI Htp with ⟨HSI, Htp, %Hnstk⟩
  rw [Hc1.last_eq] at Hnstk
  ihave Htp := wptp_of_val_post $$ Htp
  imod preStep_elim $$ HSI Htp with ⟨HSI, Hpost, Hback⟩
  imod fupd_keep_plain_sep (E' := ∅) (P := iprop(⌜ξ ex atr⌝))
    (R := iprop(relAlwaysHoldsWithTraceInv s traceInv Φs ξ (es, σ) δ ∗ stateInterp ex atr ∗
      postsOf tp (Φs ++ newPosts es tp) ∗
      (∀ ex' atr' oζ ℓ, ⌜ex.Contract oζ ex'⌝ → ⌜atr.Contract ℓ atr'⌝ → traceInv ex' atr')))
    $$ [] [Hstep HSI Hpost HTI] with ⟨%Hξ', Hstep, HSI, Hpost, HTI⟩
  · iintro ⟨Hstep, HSI, Hpost, HTI⟩
    iunfold relAlwaysHoldsWithTraceInv at Hstep
    ihave H := Hstep $$ %ex %atr %(tp, σ1') %Hv %Hex %Hatr %Hc1 %Hξ
      %(fun e hs hin => Hnstk e hin hs) %Htake HSI Hpost
    icases H with ⟨-, Hξ⟩
    iapply Hξ $$ HTI
  · iframe
  ihave #Hext : iprop(□ (stateInterp ex atr ∗
      (∀ ex' atr' oζ ℓ, ⌜ex.Contract oζ ex'⌝ → ⌜atr.Contract ℓ atr'⌝ → traceInv ex' atr')
      ={⊤}=∗ stateInterp ex atr ∗ traceInv ex atr)) $$ [Hstep HSI Hpost]
  · iunfold relAlwaysHoldsWithTraceInv at Hstep
    ihave H := Hstep $$ %ex %atr %(tp, σ1') %Hv %Hex %Hatr %Hc1 %Hξ
      %(fun e hs hin => Hnstk e hin hs) %Htake HSI Hpost
    icases H with ⟨#H, -⟩
    imodintro
    iexact H
  imod Hext $$ [HSI HTI] with ⟨HSI, HTI⟩
  · iframe
  ihave Htp := Hback $$ Hpost
  imodintro
  iintro F
  ieval (rewrite [gsim_unfold])
  iunfold gsimPre
  inext
  isplit
  · ipureintro
    exact Hξ'
  iintro %c %oζ %c' %Hc %Hstep'
  obtain rfl := EndsIn.inj Hc Hc1
  ihave Hstp := take_step (Φs := Φs ++ newPosts es tp) Hexv Hc1 Hstep' $$ Hcfg HSI Htp
  iapply ((laterN_succ_right _).mpr.trans (laterN_succ_left _).mp)
  iapply fupdToBupd_fupd_step_fupdN $$ F
  imod Hstp
  imodintro
  iapply step_fupdN_wand $$ Hstp
  iintro R
  imod R with ⟨%Hnstk', %δ', %ℓ, HSI, Hpost, Hback⟩
  imodintro
  iintro F
  have Hlocales : (Φs ++ newPosts es tp) ++ newPosts tp c'.1 = Φs ++ newPosts es c'.1 := by
    rw [List.append_assoc, newPosts_append Htake Htakelen (locale_step_equiv Hstep')]
  ieval (rewrite [Hlocales]) at Hpost Hback
  ihave Htp := Hback $$ Hpost
  have Htake' : LocalesEquiv es (c'.1.take es.length) := by
    have h := locales_equiv_take es.length (locale_step_equiv Hstep')
    simp only [List.take_take, Nat.min_eq_left Htakelen] at h
    exact locales_equiv_transitive Htake h
  have Hextras' : ValidSystemTrace (ex :tr[oζ]: c') (atr :tr[ℓ]: δ') ∧
      (ex :tr[oζ]: c').StartsIn (es, σ) ∧ (ex :tr[oζ]: c').EndsIn c' ∧
      (atr :tr[ℓ]: δ').StartsIn δ ∧
      (∀ ex' atr' oζ' ℓ', (ex :tr[oζ]: c').Contract oζ' ex' → (atr :tr[ℓ]: δ').Contract ℓ' atr' →
        ξ ex' atr') ∧
      LocalesEquiv es (c'.1.take es.length) ∧ es.length ≤ c'.1.length := by
    refine ⟨Hv.extend Hc1 Hstep', StartsIn.extend _ _ Hex, extend_endsIn _ _ _,
      StartsIn.extend _ _ Hatr, ?_, Htake', Htakelen.trans (step_tp_length Hstep')⟩
    intro ex' atr' oζ' ℓ' h1 h2
    obtain ⟨rfl, -⟩ := contract_extend h1
    obtain ⟨rfl, -⟩ := contract_extend h2
    exact Hξ'
  iapply fupdToBupd_elim (E2 := ⊤) $$ F
  imod IH $$ %(ex :tr[oζ]: c') %(atr :tr[ℓ]: δ') %c' %Hextras' Hstep HSI [HTI] Htp with H
  · iintro %ex' %atr' %oζ' %ℓ' %h1 %h2
    obtain ⟨rfl, -⟩ := contract_extend h1
    obtain ⟨rfl, -⟩ := contract_extend h2
    iexact HTI
  imodintro
  iintro F
  inext
  iexists δ', ℓ
  iapply H $$ F

end adequacy_loop

/-! ## Adequacy theorems -/

section adequacy

/-- A weakest-precondition proof of a thread pool `es`, together with a proof that `ξ` always
holds, gives the guarded simulation `gsim`. Rocq's `rel_always_holds_with_trace_inv` is
inlined in the hypothesis there. The hypothesis `length es ≥ 1` is not used (as in Rocq). -/
@[rocq_alias trillium.wp_strong_adequacy_multiple_helper]
theorem wp_strong_adequacy_multiple_helper [InvGpreS GF] (s : Stuckness)
    (ξ : ExecutionTrace Expr → AuxiliaryTrace M → Prop) (es : List Expr) (σ : State)
    (δ : M.mstate) (_Hes : es.length ≥ 1)
    (Hwp : ∀ [InvGS_gen .hasNoLC GF],
      ⊢ |={⊤}=> ∃ (stateI : ExecutionTrace Expr → AuxiliaryTrace M → IProp GF)
          (traceInv : ExecutionTrace Expr → AuxiliaryTrace M → IProp GF)
          (Φs : List (Val → IProp GF)) (forkPost : Locale → Val → IProp GF),
        letI _ : IrisG Expr M GF := { stateInterp := stateI, forkPost := forkPost }
        iprop(configWp ∗ stateI {tr[(es, σ)]} {tr[δ]} ∗ wptp s es Φs ∗
          relAlwaysHoldsWithTraceInv s traceInv Φs ξ (es, σ) δ)) :
    ⊢ gsim GF M s ξ {tr[(es, σ)]} {tr[δ]} := by
  apply fupd_to_bupd_soundness_no_lc'
  intro Hinv
  iintro F
  iapply fupdToBupd_elim (E2 := ⊤) $$ F
  imod Hwp with ⟨%stateI, %traceInv, %Φs, %fp, Hcfg, HSI, Hwp, Hstep⟩
  let _ : IrisG Expr M GF := { stateInterp := stateI, forkPost := fp }
  have Hextras : ValidSystemTrace (M := M) ({tr[(es, σ)]} : ExecutionTrace Expr) {tr[δ]} ∧
      ({tr[(es, σ)]} : ExecutionTrace Expr).StartsIn (es, σ) ∧
      ({tr[(es, σ)]} : ExecutionTrace Expr).EndsIn (es, σ) ∧
      ({tr[δ]} : AuxiliaryTrace M).StartsIn δ ∧
      (∀ ex' atr' oζ ℓ, ({tr[(es, σ)]} : ExecutionTrace Expr).Contract oζ ex' →
        ({tr[δ]} : AuxiliaryTrace M).Contract ℓ atr' → ξ ex' atr') ∧
      LocalesEquiv es ((es, σ).1.take es.length) ∧ es.length ≤ (es, σ).1.length := by
    refine ⟨.singletons _ _, rfl, rfl, rfl, ?_, ?_, le_rfl⟩
    · intro _ _ _ _ h
      exact absurd h (not_contract_singleton _ _ _)
    · simp
  iapply wp_strong_adequacy_loop s ξ es σ δ traceInv Φs $$ Hcfg %{tr[(es, σ)]} %{tr[δ]} %(es, σ)
    %Hextras Hstep HSI [] [Hwp]
  · iintro %ex' %atr' %oζ %ℓ %h
    exact absurd h (not_contract_singleton _ _ _)
  · simp only [newposts_same_empty, List.append_nil]
    iexact Hwp

/-- `wp_strong_adequacy_multiple_helper` for a single thread. -/
@[rocq_alias trillium.wp_strong_adequacy_helper]
theorem wp_strong_adequacy_helper [InvGpreS GF] (s : Stuckness)
    (ξ : ExecutionTrace Expr → AuxiliaryTrace M → Prop) (e1 : Expr) (σ1 : State) (δ : M.mstate)
    (Hwp : ∀ [InvGS_gen .hasNoLC GF],
      ⊢ |={⊤}=> ∃ (stateI : ExecutionTrace Expr → AuxiliaryTrace M → IProp GF)
          (traceInv : ExecutionTrace Expr → AuxiliaryTrace M → IProp GF)
          (Φ : Val → IProp GF) (forkPost : Locale → Val → IProp GF),
        letI _ : IrisG Expr M GF := { stateInterp := stateI, forkPost := forkPost }
        iprop(configWp ∗ stateI {tr[([e1], σ1)]} {tr[δ]} ∗
          WP e1 @ s; (localeOf [] e1); ⊤ {{ Φ }} ∗
          relAlwaysHoldsWithTraceInv s traceInv [Φ] ξ ([e1], σ1) δ)) :
    ⊢ gsim GF M s ξ {tr[([e1], σ1)]} {tr[δ]} := by
  refine wp_strong_adequacy_multiple_helper s ξ [e1] σ1 δ (by simp) ?_
  intro Hinv
  imod Hwp with ⟨%stateI, %traceInv, %Φ, %fp, Hcfg, HSI, Hwp, Hstep⟩
  imodintro
  iexists stateI, traceInv, [Φ], fp
  iframe
  let _ : IrisG Expr M GF := { stateInterp := stateI, forkPost := fp }
  iapply wptp_cons_l $$ Hwp
  iunfold wptpFrom
  rw [prefixesFrom_nil]
  iempintro

omit [Language Expr Val Ectx State Locale] in
private theorem laterN_soundness' {P : IProp GF} (n : Nat) : (⊢ ▷^[n] P) → ⊢ P := by
  induction n with
  | zero => exact id
  | succ n IH => exact fun H => IH ((extract_later _).mp H)

/-- The meta-level simulation correspondence follows from the guarded simulation, for a
finitary relation `ξ`. Rocq's unused `invGpreS Σ` assumption is dropped. -/
@[rocq_alias trillium.simulation_correspondence_multiple]
theorem simulation_correspondence_multiple (s : Stuckness)
    (ξ : ExecutionTrace Expr → AuxiliaryTrace M → Prop) (es : List Expr) (σ : State)
    (δ : M.mstate) (Hsc : RelFinitary ξ) (Hwptp : ⊢ gsim GF M s ξ {tr[(es, σ)]} {tr[δ]}) :
    ContinuedSimulation ξ {tr[(es, σ)]} {tr[δ]} := by
  refine GFX.coind (fun exatr => ⊢ gsim GF M s ξ exatr.1 exatr.2) ?_ Hwptp
  rintro ⟨ex, atr⟩ Hgsim
  dsimp only at Hgsim
  rw [gsim_unfold] at Hgsim
  unfold gsimPre at Hgsim
  rw [extract_later, extract_and, extract_pure] at Hgsim
  obtain ⟨Hvlt, Hgsim⟩ := Hgsim
  refine ⟨Hvlt, fun c c' oζ Hsmends Hstep => ?_⟩
  rw [extract_forall] at Hgsim
  have Hgsim := Hgsim c
  rw [extract_forall] at Hgsim
  have Hgsim := Hgsim oζ
  rw [extract_forall] at Hgsim
  have Hgsim := Hgsim c'
  have Hgsim := extract_impl _ _ Hgsim ((extract_pure _).mpr Hsmends)
  have Hgsim := extract_impl _ _ Hgsim ((extract_pure _).mpr Hstep)
  have Hgsim := laterN_soundness' (ex.length + 1) ((extract_later _).mp Hgsim)
  have H : ⊢ ▷ ∃ (δ' : M.mstate) (ℓ : M.mlabel),
      ⌜ξ (ex :tr[oζ]: c') (atr :tr[ℓ]: δ')⌝ ∧ gsim GF M s ξ (ex :tr[oζ]: c') (atr :tr[ℓ]: δ') := by
    refine Hgsim.trans ?_
    refine (exists_mono fun δ' => exists_mono fun ℓ => ?_).trans
      ((exists_mono fun δ' => later_exists_mp).trans later_exists_mp)
    refine (and_intro ?_ later_intro).trans later_and.mpr
    rw [gsim_unfold]
    exact later_mono and_elim_l
  have ⟨δ'', ℓ, H⟩ := (extract_exists_alt2 (fun δ' ℓ => ξ (ex :tr[oζ]: c') (atr :tr[ℓ]: δ'))
    (fun δ' ℓ => gsim GF M s ξ (ex :tr[oζ]: c') (atr :tr[ℓ]: δ')) (Hsc ex atr c' oζ)).mp
    ((extract_later _).mp H)
  exact ⟨δ'', ℓ, ((extract_and _ _).mp H).2⟩

/-- `simulation_correspondence_multiple` for a single thread. -/
@[rocq_alias trillium.simulation_correspondence]
theorem simulation_correspondence (s : Stuckness)
    (ξ : ExecutionTrace Expr → AuxiliaryTrace M → Prop) (e1 : Expr) (σ1 : State)
    (δ1 : M.mstate) (Hsc : RelFinitary ξ) (Hwptp : ⊢ gsim GF M s ξ {tr[([e1], σ1)]} {tr[δ1]}) :
    ContinuedSimulation ξ {tr[([e1], σ1)]} {tr[δ1]} :=
  simulation_correspondence_multiple s ξ [e1] σ1 δ1 Hsc Hwptp

@[rocq_alias trillium.wp_strong_adequacy_multiple_with_trace_inv]
theorem wp_strong_adequacy_multiple_with_trace_inv [InvGpreS GF] (s : Stuckness)
    (ξ : ExecutionTrace Expr → AuxiliaryTrace M → Prop) (es : List Expr) (σ : State)
    (δ : M.mstate) (Hlen : es.length ≥ 1) (Hsc : RelFinitary ξ)
    (Hwptp : ∀ [InvGS_gen .hasNoLC GF],
      ⊢ |={⊤}=> ∃ (stateI : ExecutionTrace Expr → AuxiliaryTrace M → IProp GF)
          (traceInv : ExecutionTrace Expr → AuxiliaryTrace M → IProp GF)
          (Φs : List (Val → IProp GF)) (forkPost : Locale → Val → IProp GF),
        letI _ : IrisG Expr M GF := { stateInterp := stateI, forkPost := forkPost }
        iprop(configWp ∗ stateI {tr[(es, σ)]} {tr[δ]} ∗ wptp s es Φs ∗
          relAlwaysHoldsWithTraceInv s traceInv Φs ξ (es, σ) δ)) :
    ContinuedSimulation ξ {tr[(es, σ)]} {tr[δ]} :=
  simulation_correspondence_multiple (GF := GF) s ξ es σ δ Hsc
    (wp_strong_adequacy_multiple_helper (GF := GF) s ξ es σ δ Hlen Hwptp)

@[rocq_alias trillium.wp_strong_adequacy_with_trace_inv]
theorem wp_strong_adequacy_with_trace_inv [InvGpreS GF] (s : Stuckness)
    (ξ : ExecutionTrace Expr → AuxiliaryTrace M → Prop) (e1 : Expr) (σ1 : State)
    (δ1 : M.mstate) (Hsc : RelFinitary ξ)
    (Hwptp : ∀ [InvGS_gen .hasNoLC GF],
      ⊢ |={⊤}=> ∃ (stateI : ExecutionTrace Expr → AuxiliaryTrace M → IProp GF)
          (traceInv : ExecutionTrace Expr → AuxiliaryTrace M → IProp GF)
          (Φ : Val → IProp GF) (forkPost : Locale → Val → IProp GF),
        letI _ : IrisG Expr M GF := { stateInterp := stateI, forkPost := forkPost }
        iprop(configWp ∗ stateI {tr[([e1], σ1)]} {tr[δ1]} ∗
          WP e1 @ s; (localeOf [] e1); ⊤ {{ Φ }} ∗
          relAlwaysHoldsWithTraceInv s traceInv [Φ] ξ ([e1], σ1) δ1)) :
    ContinuedSimulation ξ {tr[([e1], σ1)]} {tr[δ1]} :=
  simulation_correspondence (GF := GF) s ξ e1 σ1 δ1 Hsc
    (wp_strong_adequacy_helper (GF := GF) s ξ e1 σ1 δ1 Hwptp)

@[rocq_alias trillium.wp_strong_adequacy_multiple]
theorem wp_strong_adequacy_multiple [InvGpreS GF] (s : Stuckness)
    (ξ : ExecutionTrace Expr → AuxiliaryTrace M → Prop) (es : List Expr) (σ : State)
    (δ : M.mstate) (Hlen : es.length ≥ 1) (Hsc : RelFinitary ξ)
    (Hwptp : ∀ [InvGS_gen .hasNoLC GF],
      ⊢ |={⊤}=> ∃ (stateI : ExecutionTrace Expr → AuxiliaryTrace M → IProp GF)
          (Φs : List (Val → IProp GF)) (forkPost : Locale → Val → IProp GF),
        letI _ : IrisG Expr M GF := { stateInterp := stateI, forkPost := forkPost }
        iprop(configWp ∗ stateI {tr[(es, σ)]} {tr[δ]} ∗ wptp s es Φs ∗
          relAlwaysHolds s Φs ξ (es, σ) δ)) :
    ContinuedSimulation ξ {tr[(es, σ)]} {tr[δ]} := by
  refine wp_strong_adequacy_multiple_with_trace_inv (GF := GF) s ξ es σ δ Hlen Hsc ?_
  intro Hinv
  imod Hwptp with ⟨%stateI, %Φs, %fp, Hcfg, HSI, Hwp, Hstep⟩
  imodintro
  iexists stateI, (fun _ _ => iprop(True)), Φs, fp
  iframe Hcfg HSI Hwp
  iunfold relAlwaysHoldsWithTraceInv
  iunfold relAlwaysHolds at Hstep
  iintro %ex %atr %c %H1 %H2 %H3 %H4 %H5 %H6 %H7 HSI Hposts
  isplitr
  · imodintro
    iintro ⟨HSI, -⟩
    imodintro
    iframe
  · iintro -
    iapply Hstep $$ %ex %atr %c %H1 %H2 %H3 %H4 %H5 %H6 %H7 HSI Hposts

/-- The main adequacy theorem of Trillium: a weakest-precondition proof of `e1`, together with a
proof that `ξ` holds for all reachable traces, gives the meta-level continued simulation. -/
@[rocq_alias trillium.wp_strong_adequacy]
theorem wp_strong_adequacy [InvGpreS GF] (s : Stuckness)
    (ξ : ExecutionTrace Expr → AuxiliaryTrace M → Prop) (e1 : Expr) (σ1 : State)
    (δ1 : M.mstate) (Hsc : RelFinitary ξ)
    (Hwptp : ∀ [InvGS_gen .hasNoLC GF],
      ⊢ |={⊤}=> ∃ (stateI : ExecutionTrace Expr → AuxiliaryTrace M → IProp GF)
          (Φ : Val → IProp GF) (forkPost : Locale → Val → IProp GF),
        letI _ : IrisG Expr M GF := { stateInterp := stateI, forkPost := forkPost }
        iprop(configWp ∗ stateI {tr[([e1], σ1)]} {tr[δ1]} ∗
          WP e1 @ s; (localeOf [] e1); ⊤ {{ Φ }} ∗
          relAlwaysHolds0 ξ s stateI Φ e1 σ1 δ1)) :
    ContinuedSimulation ξ {tr[([e1], σ1)]} {tr[δ1]} := by
  refine wp_strong_adequacy_with_trace_inv (GF := GF) s ξ e1 σ1 δ1 Hsc ?_
  intro Hinv
  imod Hwptp with ⟨%stateI, %Φ, %fp, Hcfg, HSI, Hwp, Hstep⟩
  imodintro
  iexists stateI, (fun _ _ => iprop(True)), Φ, fp
  iframe Hcfg HSI Hwp
  iunfold relAlwaysHoldsWithTraceInv
  iunfold relAlwaysHolds0 at Hstep
  iintro %ex %atr %c %H1 %H2 %H3 %H4 %H5 %H6 %H7 HSI Hposts
  isplitr
  · imodintro
    iintro ⟨HSI, -⟩
    imodintro
    iframe
  · iintro -
    iapply Hstep $$ %ex %atr %c %H1 %H2 %H3 %H4 %H5 %H6 %H7 HSI [Hposts]
    iunfold curPosts
    ieval (simp only [newPosts, newElems, List.singleton_append, List.length_singleton]) at Hposts
    iexact Hposts

/-- Adequacy for a thread pool: the results of the threads satisfy the meta-level
postconditions `φs`, and (if `s = NotStuck`) no thread gets stuck. Rocq's unused
`EqDecision (mlabel M), EqDecision M` assumptions are dropped. -/
@[rocq_alias trillium.adequacy_multiple_xi]
theorem adequacy_multiple_xi [InvGpreS GF] (s : Stuckness)
    (ξ : ExecutionTrace Expr → AuxiliaryTrace M → Prop) (φs : List (Val → Prop))
    (es : List Expr) (σ1 : State) (δ1 : M.mstate) (Hlen : es.length ≥ 1) (Hsc : RelFinitary ξ)
    (Hwp : ∀ [InvGS_gen .hasNoLC GF],
      ⊢ |={⊤}=> ∃ (stateI : ExecutionTrace Expr → AuxiliaryTrace M → IProp GF)
          (traceInv : ExecutionTrace Expr → AuxiliaryTrace M → IProp GF)
          (Φs : List (Val → IProp GF)) (forkPost : Locale → Val → IProp GF),
        letI _ : IrisG Expr M GF := { stateInterp := stateI, forkPost := forkPost }
        iprop(⌜φs.length = Φs.length⌝ ∗ configWp ∗
          ([∗list] Φ;φ ∈ Φs;φs, ∀ v, Φ v -∗ ⌜φ v⌝) ∗
          stateI {tr[(es, σ1)]} {tr[δ1]} ∗ wptp s es Φs ∗
          relAlwaysHoldsWithTraceInv s traceInv Φs ξ (es, σ1) δ1)) :
    AdequateMultiple s es σ1 (φs.map fun φ v _ => φ v) := by
  let ξ' : ExecutionTrace Expr → AuxiliaryTrace M → Prop :=
    fun ex aux => ξ ex aux ∧ WpAdequacyRelation M s φs ex aux
  refine wpAdequacyRelation_adequateMultiple (ξ := ξ') (δ := δ1) (fun _ _ h => h.2) ?_
  refine wp_strong_adequacy_multiple_with_trace_inv (GF := GF) s ξ' es σ1 δ1 Hlen
    (RelFinitary.of_imp (fun _ _ h => h.1) Hsc) ?_
  intro Hinv
  imod Hwp with ⟨%stateI, %post, %Φs, %fp, %Hlen', #Hcfg, HΦs, HSI, Hwp, H⟩
  imodintro
  iexists stateI, post, Φs, fp
  iframe Hcfg HSI Hwp
  let _ : IrisG Expr M GF := { stateInterp := stateI, forkPost := fp }
  iunfold relAlwaysHoldsWithTraceInv
  iunfold relAlwaysHoldsWithTraceInv at H
  iintro %ex %atr %c %Hvlt %Hexs %Hatre %Hexe %Hψ %Hnst %Hlocale HSI Hposts
  ispecialize H $$ %ex %atr %c %Hvlt %Hexs %Hatre %Hexe
    %(fun ex' atr' oζ ℓ h1 h2 => (Hψ ex' atr' oζ ℓ h1 h2).1) %Hnst %Hlocale
  ihave %Hφ : iprop(⌜∀ i v, i < φs.length → c.1[i]?.bind toVal = some v →
      (φs[i]?).elim False (fun φ => φ v)⌝) $$ [Hposts HΦs]
  · by_cases hP : ∀ i v, i < φs.length → c.1[i]?.bind toVal = some v →
        (φs[i]?).elim False (fun φ => φ v)
    · ipureintro
      exact hP
    · simp only [Classical.not_forall] at hP
      obtain ⟨i, v, Hi, HSome, Hfalse⟩ := hP
      obtain ⟨e, HSome', Hv⟩ := Option.bind_eq_some_iff.mp HSome
      have hφ : φs[i]? = some φs[i] := List.getElem?_eq_getElem Hi
      have HiΦ : i < Φs.length := Hlen' ▸ Hi
      have hΦ : Φs[i]? = some Φs[i] := List.getElem?_eq_getElem HiΦ
      have hmem : (v, Φs[i]) ∈ (c.1.zip (Φs ++ newPosts es c.1)).filterMap
          (fun x : Expr × (Val → IProp GF) => (toVal x.1).map fun v => (v, x.2)) := by
        refine List.mem_filterMap.mpr ⟨(e, Φs[i]), ?_, by simp [Hv]⟩
        refine List.mem_of_getElem? (i := i) ?_
        rw [List.getElem?_zip_eq_some]
        exact ⟨HSome', by rw [List.getElem?_append_left HiΦ, hΦ]⟩
      ihave HΦv := BigSepL.bigSepL_mem hmem $$ Hposts
      ihave Himp := BigSepL2.bigSepL2_lookup hΦ hφ $$ HΦs
      ihave %hφv := Himp $$ %v HΦv
      ipureintro
      exact absurd (by rw [hφ]; exact hφv) Hfalse
  ihave H := H $$ HSI Hposts
  icases H with ⟨#Hext, Hfin⟩
  isplitr [Hfin]
  · imodintro
    iexact Hext
  · iintro HTI
    imod Hfin $$ HTI with %Hξ
    imodintro
    ipureintro
    refine ⟨Hξ, fun c' Hc' => ?_⟩
    obtain rfl := EndsIn.inj Hexe Hc'
    exact ⟨Hφ, Hnst⟩

/-- `adequacy_multiple_xi` for a single thread. -/
@[rocq_alias trillium.adequacy_xi]
theorem adequacy_xi [InvGpreS GF] (s : Stuckness)
    (ξ : ExecutionTrace Expr → AuxiliaryTrace M → Prop) (φ : Val → Prop)
    (e1 : Expr) (σ1 : State) (δ1 : M.mstate) (Hsc : RelFinitary ξ)
    (Hwptp : ∀ [InvGS_gen .hasNoLC GF],
      ⊢ |={⊤}=> ∃ (stateI : ExecutionTrace Expr → AuxiliaryTrace M → IProp GF)
          (traceInv : ExecutionTrace Expr → AuxiliaryTrace M → IProp GF)
          (Φ : Val → IProp GF) (forkPost : Locale → Val → IProp GF),
        letI _ : IrisG Expr M GF := { stateInterp := stateI, forkPost := forkPost }
        iprop(configWp ∗ (∀ v, Φ v -∗ ⌜φ v⌝) ∗
          stateI {tr[([e1], σ1)]} {tr[δ1]} ∗ WP e1 @ s; (localeOf [] e1); ⊤ {{ Φ }} ∗
          relAlwaysHoldsWithTraceInv s traceInv [Φ] ξ ([e1], σ1) δ1)) :
    Adequate s e1 σ1 (fun v _ => φ v) := by
  refine adequacy_multiple_xi (GF := GF) s ξ [φ] [e1] σ1 δ1 (by simp) Hsc ?_
  intro Hinv
  imod Hwptp with ⟨%stateI, %traceInv, %Φ, %fp, Hcfg, HΦ, HSI, Hwp, Hstep⟩
  imodintro
  iexists stateI, traceInv, [Φ], fp
  let _ : IrisG Expr M GF := { stateInterp := stateI, forkPost := fp }
  iframe Hcfg HSI Hstep
  isplitr
  · ipureintro
    rfl
  isplitl [HΦ]
  · iapply BigSepL2.bigSepL2_singleton.mpr
    iexact HΦ
  iapply wptp_cons_l $$ Hwp
  iunfold wptpFrom
  rw [prefixesFrom_nil]
  iempintro

@[rocq_alias trillium.sim_and_adequacy_multiple_xi]
theorem sim_and_adequacy_multiple_xi [InvGpreS GF] (s : Stuckness)
    (ξ : ExecutionTrace Expr → AuxiliaryTrace M → Prop) (φs : List (Val → Prop))
    (es : List Expr) (σ1 : State) (δ1 : M.mstate) (Hlen : es.length ≥ 1) (Hsc : RelFinitary ξ)
    (Hwp : ∀ [InvGS_gen .hasNoLC GF],
      ⊢ |={⊤}=> ∃ (stateI : ExecutionTrace Expr → AuxiliaryTrace M → IProp GF)
          (traceInv : ExecutionTrace Expr → AuxiliaryTrace M → IProp GF)
          (Φs : List (Val → IProp GF)) (forkPost : Locale → Val → IProp GF),
        letI _ : IrisG Expr M GF := { stateInterp := stateI, forkPost := forkPost }
        iprop(⌜φs.length = Φs.length⌝ ∗ configWp ∗
          ([∗list] Φ;φ ∈ Φs;φs, ∀ v, Φ v -∗ ⌜φ v⌝) ∗
          stateI {tr[(es, σ1)]} {tr[δ1]} ∗ wptp s es Φs ∗
          relAlwaysHoldsWithTraceInv s traceInv Φs ξ (es, σ1) δ1)) :
    ContinuedSimulation ξ {tr[(es, σ1)]} {tr[δ1]} ∧
      AdequateMultiple s es σ1 (φs.map fun φ v _ => φ v) := by
  refine ⟨?_, adequacy_multiple_xi (GF := GF) s ξ φs es σ1 δ1 Hlen Hsc Hwp⟩
  refine wp_strong_adequacy_multiple_with_trace_inv (GF := GF) s ξ es σ1 δ1 Hlen Hsc ?_
  intro Hinv
  imod Hwp with ⟨%stateI, %traceInv, %Φs, %fp, -, Hcfg, -, HSI, Hwp, H⟩
  imodintro
  iexists stateI, traceInv, Φs, fp
  iframe

@[rocq_alias trillium.sim_and_adequacy_xi]
theorem sim_and_adequacy_xi [InvGpreS GF] (s : Stuckness)
    (ξ : ExecutionTrace Expr → AuxiliaryTrace M → Prop) (φ : Val → Prop)
    (e1 : Expr) (σ1 : State) (δ1 : M.mstate) (Hsc : RelFinitary ξ)
    (Hwptp : ∀ [InvGS_gen .hasNoLC GF],
      ⊢ |={⊤}=> ∃ (stateI : ExecutionTrace Expr → AuxiliaryTrace M → IProp GF)
          (traceInv : ExecutionTrace Expr → AuxiliaryTrace M → IProp GF)
          (Φ : Val → IProp GF) (forkPost : Locale → Val → IProp GF),
        letI _ : IrisG Expr M GF := { stateInterp := stateI, forkPost := forkPost }
        iprop(configWp ∗ (∀ v, Φ v -∗ ⌜φ v⌝) ∗
          stateI {tr[([e1], σ1)]} {tr[δ1]} ∗ WP e1 @ s; (localeOf [] e1); ⊤ {{ Φ }} ∗
          relAlwaysHoldsWithTraceInv s traceInv [Φ] ξ ([e1], σ1) δ1)) :
    ContinuedSimulation ξ {tr[([e1], σ1)]} {tr[δ1]} ∧ Adequate s e1 σ1 (fun v _ => φ v) := by
  refine ⟨?_, adequacy_xi (GF := GF) s ξ φ e1 σ1 δ1 Hsc Hwptp⟩
  refine wp_strong_adequacy_with_trace_inv (GF := GF) s ξ e1 σ1 δ1 Hsc ?_
  intro Hinv
  imod Hwptp with ⟨%stateI, %traceInv, %Φ, %fp, Hcfg, -, HSI, Hwp, H⟩
  imodintro
  iexists stateI, traceInv, Φ, fp
  iframe

end adequacy

end Trillium
