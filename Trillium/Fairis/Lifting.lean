/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.Fairis.HeapLangLM
import Trillium.Fairis.ResourcesUpdates
import Trillium.HeapLang.LocalesHelpersHL
import Trillium.ProgramLogic.EctxLifting

/-!
# Fairis lifting lemmas

Port of `fairis/lifting.v`: the program-logic rules of Fairis for HeapLang with a live model,
relating the single-step weakest precondition `sswp` and Trillium's `wp` with the fuel and model
resources (`ζ ↦M fs`, `ζ ↦M++ fs`, `fragModelIs`, `fragFreeRolesAre`).

## Representation

* The context `LiveModel heap_lang M`, `heapGS Σ LM` is `{LM : LiveModel BaseLocale M}`,
  `[HeapGS LM GF]`.
* Rocq's `TCEq (to_val e) None` premises are plain hypotheses `toVal e = none`.
* stdpp's `{[ρ := f]} ∪ fs` is `GMap.singleton ρ f ∪ fs` (the union on `Std.ExtTreeMap` is
  right-biased, but all unions here are disjoint, and the statements are the ones of
  `update_model_step`), `S <$> fs` is `fs.map fun _ f => f + 1`, `delete ρ fs` is `fs.erase ρ`.
* The Rocq lemma `has_fuels_decr` of this file (a `pre_step` version of the homonymous lemma of
  `resources.v`) is `has_fuels_decr_preStep`.
-/

set_option linter.unusedSectionVars false

namespace Trillium.Fairis

open Iris Iris.BI Iris.Std Iris.ProofMode
open Trillium Trillium.HeapLang Trillium.Fairness Trillium.GMap Trillium.Language FiniteTrace
open Iris.HeapLang (HeapF)

section lifting

variable {M : FairModel} {LM : LiveModel BaseLocale M} {GF : BundledGFunctors} [HeapGS LM GF]

/-! Timelessness of the fairness resources (automatic in Rocq, where `Timeless` instances are found
by unfolding the definitions). -/

instance hasFuelsS_timeless (ζ : BaseLocale) (fs : GMap M.fmrole Nat) :
    Timeless (hasFuelsS (GF := GF) ζ fs) := by
  unfold hasFuelsS
  infer_instance

instance fragModelIs_timeless (s : M.fmstate) : Timeless (fragModelIs (GF := GF) s) := by
  unfold fragModelIs
  infer_instance

instance fragFreeRolesAre_timeless (fr : GSet M.fmrole) :
    Timeless (fragFreeRolesAre (GF := GF) fr) := by
  unfold fragFreeRolesAre
  infer_instance

@[rocq_alias trillium.fairis.lifting.has_fuels_decr]
theorem has_fuels_decr_preStep (E : CoPset) (tid : BaseLocale) (fs : GMap M.fmrole Nat) :
    ⊢ hasFuelsS (GF := GF) tid fs -∗ |~{E}~| tid ↦M fs := by
  unfold preStep
  iintro Hf %extr %atr Hsi
  rw [heapG_stateInterp_eq]
  icases Hsi with ⟨%Hvse, Hσ, Hm⟩
  imod model_state_interp_has_fuels_decr $$ Hm Hf with ⟨Hm, Hf⟩
  imodintro
  iframe
  ipureintro
  exact Hvse

@[rocq_alias trillium.fairis.has_fuels_dealloc]
theorem has_fuels_dealloc (E : CoPset) (tid : BaseLocale) (fs : GMap M.fmrole Nat)
    (ρ : M.fmrole) (δ : M.fmstate) :
    ρ ∉ M.liveRoles δ →
    ⊢ fragModelIs (GF := GF) δ -∗ (tid ↦M fs) -∗
      |~{E}~| fragModelIs δ ∗ (tid ↦M (fs.erase ρ)) := by
  intro Hnin
  unfold preStep
  iintro Hst Hf %extr %atr Hsi
  rw [heapG_stateInterp_eq]
  icases Hsi with ⟨%Hvse, Hσ, Hm⟩
  imod model_state_interp_has_fuels_dealloc _ _ _ _ _ _ Hnin $$ Hm Hst Hf with ⟨Hm, Hst, Hf⟩
  imodintro
  iframe
  ipureintro
  exact Hvse

/-- Rule from the Trillium article. -/
@[rocq_alias trillium.fairis.wp_role_dealloc]
theorem wp_role_dealloc (s : Stuckness) (tid : BaseLocale) (E : CoPset) (e : Expr)
    (fs : GMap M.fmrole Nat) (ρ : M.fmrole) (δ : M.fmstate) (Φ : Val → IProp GF) :
    ρ ∉ M.liveRoles δ →
    ⊢ fragModelIs (GF := GF) δ -∗ (tid ↦M fs) -∗
      (fragModelIs δ -∗ (tid ↦M (fs.erase ρ)) -∗ WP e @ s; tid; E {{ Φ }}) -∗
      WP e @ s; tid; E {{ Φ }} := by
  intro Hnin
  iintro HM Hfuels Hwp
  imod has_fuels_dealloc E tid fs ρ δ Hnin $$ HM Hfuels with ⟨HM, Hfuels⟩
  iapply Hwp $$ HM Hfuels

@[rocq_alias trillium.fairis.wp_step_fuel]
theorem wp_step_fuel (s : Stuckness) (tid : BaseLocale) (E : CoPset) (e : Expr)
    (fs : GMap M.fmrole Nat) (Φ : Val → IProp GF) :
    fs ≠ ∅ →
    ⊢ ▷ hasFuelsS (GF := GF) tid fs -∗
      sswp s E e (fun e' => iprop((tid ↦M fs) -∗ WP e' @ s; tid; E {{ Φ }})) -∗
      WP e @ s; tid; E {{ Φ }} := by
  intro Hne
  iintro >HfuelS Hwp
  cases Hval : e.toVal with
  | some v =>
    obtain rfl := of_to_val Hval
    rw [wp_unfold.to_eq]
    simp only [wp.pre, sswp, toVal_eq, to_of_val]
    imod has_fuels_decr_preStep E tid fs $$ HfuelS with Hfuel
    imod Hwp
    iapply wp_value_inv' (Expr := Expr) (v := v)
    iapply Hwp $$ Hfuel
  | none =>
    rw [wp_unfold.to_eq, sswp_eq_of_toVal_none Hval]
    simp only [wp.pre, toVal_eq, Hval]
    iintro %extr %atr %K %tp1 %tp2 %σ1 %Hvalid %Hloc %Hends
    have Hlast : extr.last = (tp1 ++ fill K e :: tp2, σ1) := endsIn_iff.1 Hends
    rw [heapG_stateInterp_eq, Hlast]
    iintro ⟨%Hvse, Hsi, Hmi⟩
    imod Hwp $$ %σ1 Hsi with ⟨%Hred, Hwp⟩
    imodintro
    isplitr
    · ipureintro; exact Hred
    iintro %e2 %σ2 %efs %Hstep
    dsimp only [step_fupdN]
    imod Hwp $$ %e2 %σ2 %efs %Hstep with Hwp
    iintro !> !>
    imod Hwp
    imodintro
    iapply step_fupdN_intro LawfulSet.subset_refl
    iapply BI.laterN_intro
    imod Hwp with ⟨Hsi, Hwp, %Hefs⟩
    subst Hefs
    have Hlstep : LocaleStep extr.last (some tid) (tp1 ++ fill K e2 :: (tp2 ++ []), σ2) := by
      rw [Hlast, ← Hloc]
      exact .atomic _ _ (fill_step K Hstep)
    have Hupd := update_fuel_step (GF := GF) extr atr _ fs tid Hne Hlstep
    rw [Hlast] at Hupd
    imod Hupd $$ HfuelS Hmi with ⟨%δ2, %Hvse2, Hfuel, Hmod⟩
    imodintro
    iexists δ2, FairLabel.silentStep tid
    rw [heapG_stateInterp_eq]
    simp only [FiniteTrace.last]
    iframe
    isplitr
    · ipureintro; exact Hvse2
    isplitl
    · iapply Hwp $$ Hfuel
    · iempintro

@[rocq_alias trillium.fairis.wp_step_model]
theorem wp_step_model (s : Stuckness) (tid : BaseLocale) (ρ : M.fmrole) (f1 : Nat)
    (fs : GMap M.fmrole Nat) (fr : GSet M.fmrole) (s1 s2 : M.fmstate) (E : CoPset) (e : Expr)
    (Φ : Val → IProp GF) :
    toVal e = none →
    M.fmtrans s1 (some ρ) s2 →
    M.liveRoles s2 ⊆ M.liveRoles s1 →
    ρ ∉ dom fs →
    ⊢ ▷ fragModelIs (GF := GF) s1 -∗
      ▷ (tid ↦M (GMap.singleton ρ f1 ∪ fs.map fun _ f => f + 1)) -∗
      ▷ fragFreeRolesAre fr -∗
      sswp s E e (fun e' => iprop(fragModelIs s2 -∗
        (tid ↦M (GMap.singleton ρ (LM.lmFl s2) ∪ fs)) -∗
        fragFreeRolesAre fr -∗
        WP e' @ s; tid; E {{ Φ }})) -∗
      WP e @ s; tid; E {{ Φ }} := by
  intro Hval Htrans Hlive Hdom
  iintro >Hst >Hfuel1 >Hfr Hwp
  have Hval' : e.toVal = none := by rwa [toVal_eq] at Hval
  rw [wp_unfold.to_eq, sswp_eq_of_toVal_none Hval']
  simp only [wp.pre, Hval]
  iintro %extr %atr %K %tp1 %tp2 %σ1 %Hvalid %Hloc %Hexend
  have Hlast : extr.last = (tp1 ++ fill K e :: tp2, σ1) := endsIn_iff.1 Hexend
  rw [heapG_stateInterp_eq, Hlast]
  iintro ⟨%Hvse, Hsi, Hmi⟩
  imod Hwp $$ %σ1 Hsi with ⟨%Hred, Hwp⟩
  imodintro
  isplitr
  · ipureintro; exact Hred
  iintro %e2 %σ2 %efs %Hstep
  dsimp only [step_fupdN]
  imod Hwp $$ %e2 %σ2 %efs %Hstep with Hwp
  iintro !> !>
  imod Hwp
  imodintro
  iapply step_fupdN_intro LawfulSet.subset_refl
  iapply BI.laterN_intro
  imod Hwp with ⟨Hσ, Hwp, %Hefs⟩
  subst Hefs
  ihave %Hmeq : ⌜atr.last.lsUnder = s1⌝ $$ [Hmi Hst]
  · iapply model_agree' $$ Hmi Hst
  have Hlstep : LocaleStep extr.last (some tid) (tp1 ++ fill K e2 :: (tp2 ++ []), σ2) := by
    rw [Hlast, ← Hloc]
    exact .atomic _ _ (fill_step K Hstep)
  have Hupd := update_model_step (GF := GF) extr atr _ s1 s2 fs ρ atr.last tid f1 Hlive Hdom rfl
    Hlstep Htrans
  rw [Hlast] at Hupd
  imod Hupd $$ Hfuel1 Hst Hmi with ⟨%δ2, %Hvse2, Hfuel, Hst, Hmod⟩
  imodintro
  iexists δ2, FairLabel.takeStep ρ tid
  rw [heapG_stateInterp_eq]
  simp only [FiniteTrace.last]
  iframe
  isplitr
  · ipureintro; exact Hvse2
  isplitl
  · iapply Hwp $$ Hst Hfuel Hfr
  · iempintro

@[rocq_alias trillium.fairis.wp_step_model_singlerole]
theorem wp_step_model_singlerole (s : Stuckness) (tid : BaseLocale) (ρ : M.fmrole) (f1 : Nat)
    (fr : GSet M.fmrole) (s1 s2 : M.fmstate) (E : CoPset) (e : Expr) (Φ : Val → IProp GF) :
    toVal e = none →
    M.fmtrans s1 (some ρ) s2 →
    M.liveRoles s2 ⊆ M.liveRoles s1 →
    ⊢ ▷ fragModelIs (GF := GF) s1 -∗ ▷ (tid ↦M GMap.singleton ρ f1) -∗ ▷ fragFreeRolesAre fr -∗
      sswp s E e (fun e' => iprop(fragModelIs s2 -∗
        (tid ↦M GMap.singleton ρ (LM.lmFl s2)) -∗
        fragFreeRolesAre fr -∗
        WP e' @ s; tid; E {{ Φ }})) -∗
      WP e @ s; tid; E {{ Φ }} := by
  intro Hval Htrans Hlive
  have Hunion : ∀ f : Nat, GMap.singleton ρ f ∪ (∅ : GMap M.fmrole Nat) = GMap.singleton ρ f := by
    intro f
    apply Std.ExtTreeMap.ext_getElem?
    intro k
    simp [Std.ExtTreeMap.getElem?_union]
  have Hempty : ((∅ : GMap M.fmrole Nat).map fun _ f => f + 1) = ∅ := by
    simp
  iintro >Hst >Hfuel1 >Hfr Hwp
  rw [← Hunion f1, ← Hempty]
  have Hdom : ρ ∉ dom (∅ : GMap M.fmrole Nat) := by
    simp [mem_dom]
  iapply wp_step_model s tid ρ f1 ∅ fr s1 s2 E e Φ Hval Htrans Hlive Hdom $$ Hst Hfuel1 Hfr
  iapply sswp_wand $$ [] Hwp
  iintro %e' Hwp Hst Hfuel1 Hfr
  rw [Hunion]
  iapply Hwp $$ Hst Hfuel1 Hfr

@[rocq_alias trillium.fairis.wp_role_fork]
theorem wp_role_fork (s : Stuckness) (tid : BaseLocale) (E : CoPset) (e : Expr)
    (Φ : Val → IProp GF) (R1 R2 : GMap M.fmrole Nat) (Hdisj : R1 ##ₘ R2) (Hnemp : R1 ∪ R2 ≠ ∅) :
    ⊢ hasFuelsS (GF := GF) tid (R1 ∪ R2) -∗
      (∀ tid' : BaseLocale, ▷ ((tid' ↦M R2) -∗ WP e @ s; tid'; ⊤ {{ _v, tid' ↦M ∅ }})) -∗
      ▷ ((tid ↦M R1) ={E}=∗ Φ (.lit .unit)) -∗
      WP (Expr.fork e) @ s; tid; E {{ Φ }} := by
  iintro Htid He HΦ
  iapply wp_lift_atomic_head_step rfl
  iintro %extr %auxtr %K %tp1 %tp2 %σ1 %Hvalex %Hexend %Hloc Hsi
  have Hlast : extr.last = (tp1 ++ fill K (Expr.fork e) :: tp2, σ1) := endsIn_iff.1 Hexend
  rw [heapG_stateInterp_eq, Hlast]
  icases Hsi with ⟨%Hvse, Hsi, Hmi⟩
  have Hstep : LocaleStep (tp1 ++ fill K (Expr.fork e) :: tp2, σ1) (some tid)
      (tp1 ++ fill K (Expr.val (.lit .unit)) :: (tp2 ++ [e]), σ1) := by
    rw [← Hloc]
    exact EctxLanguage.head_locale_step K tp1 tp2 (BaseStep.forkS e σ1)
  have Hforked : HasForked (tp1 ++ fill K (Expr.fork e) :: tp2)
      (tp1 ++ fill K (Expr.val (.lit .unit)) :: (tp2 ++ [e])) e :=
    ⟨tp1 ++ fill K (Expr.val (.lit .unit)) :: tp2, by simp,
      locales_equiv_of_length_eq (by simp)⟩
  imod update_fork_step (GF := GF) R1 R2 _ _ extr auxtr tid e σ1 σ1 Hnemp Hdisj Hlast Hstep
    Hforked $$ Htid Hmi with ⟨%δ2, %Hvse2, Hfuels1, Hfuels2, Hmi⟩
  ispecialize He $$ %(localeOf (tp1 ++ fill K (Expr.fork e) :: tp2) e)
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, _, _, BaseStep.forkS e σ1⟩
  inext
  iintro %e2 %σ2 %efs %Hhead
  cases Hhead
  imod HΦ $$ Hfuels1 with HΦ
  imodintro
  iexists δ2, FairLabel.silentStep tid
  rw [heapG_stateInterp_eq]
  simp only [FiniteTrace.last]
  iframe Hsi Hmi
  isplitr
  · ipureintro; exact Hvse2
  isplitl [HΦ]
  · simp only [toVal_eq, to_of_val, Option.elim]
    iexact HΦ
  iapply BigSepL.bigSepL_singleton.2
  simp only [List.take_zero, List.append_nil]
  iapply He $$ Hfuels2

end lifting

end Trillium.Fairis
