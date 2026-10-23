/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.ProgramLogic.WeakestPre

/-!
# Lifting lemmas

Port of `trillium/program_logic/lifting.v`.

The "lifting lemmas" in this file serve to lift the rules of the operational semantics to the
program logic.

Rocq's `from_option Φ False (to_val e)` is `(toVal e).elim iprop(False) Φ`. The Rocq statement
of `wp_lift_pure_stuck` uses the notation `WP e @ E ?{{ Φ }}`, which in Trillium's notation
means locale `E` and mask `⊤`; the Lean statement makes this explicit (`WP e @[ζ] ? {{ Φ }}`).
-/

namespace Trillium

open Iris Iris.BI Iris.Std Iris.ProofMode FiniteTrace Language
open Iris.ProgramLogic (ToVal EvContext EvContextOps)

variable {Expr Val Ectx State Locale : Type _} [Language Expr Val Ectx State Locale]
variable {M : Model} {GF : BundledGFunctors} [IrisG Expr M GF]
variable {s : Stuckness} {E E₁ E₂ : CoPset} {ζ : Locale} {e e₁ e₂ : Expr}
variable {Φ : Val → IProp GF}

@[rocq_alias trillium.wp_lift_step_fupdN]
theorem wp_lift_step_fupdN (He : toVal e₁ = none) :
    (∀ (extr : ExecutionTrace Expr) (atr : AuxiliaryTrace M) (K : Ectx) (tp1 tp2 : List Expr)
        (σ₁ : State),
      ⌜ValidExec extr⌝ -∗
      ⌜extr.EndsIn (tp1 ++ fill K e₁ :: tp2, σ₁)⌝ -∗
      ⌜localeOf tp1 (fill K e₁) = ζ⌝ -∗
      stateInterp extr atr ={E,∅}=∗
        ⌜reducibleIfNotStuck s e₁ σ₁⌝ ∗
        ∀ (e₂ : Expr) (σ₂ : State) (efs : List Expr),
          ⌜primStep e₁ σ₁ e₂ σ₂ efs⌝ ={∅}▷=∗^[extr.length + 1] |={∅,E}=>
          ∃ (δ₂ : M.mstate) (ℓ : M.mlabel),
            stateInterp (extr :tr[some ζ]: (tp1 ++ fill K e₂ :: (tp2 ++ efs), σ₂))
              (atr :tr[ℓ]: δ₂) ∗
            WP e₂ @ s; ζ; E {{ Φ }} ∗
            [∗list] i ↦ ef ∈ efs,
              WP ef @ s; (localeOf (tp1 ++ fill K e₁ :: (tp2 ++ efs.take i)) ef); ⊤
                {{ forkPost (localeOf (tp1 ++ fill K e₁ :: (tp2 ++ efs.take i)) ef) }}) ⊢
    WP e₁ @ s; ζ; E {{ Φ }} := by
  rw [wp_unfold.to_eq]
  simp only [wp.pre, He]
  iintro H %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hloc %Hends Hσ
  iapply H $$ %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hends %Hloc Hσ

@[rocq_alias trillium.wp_lift_step_fupd]
theorem wp_lift_step_fupd (He : toVal e₁ = none) :
    (∀ (extr : ExecutionTrace Expr) (atr : AuxiliaryTrace M) (K : Ectx) (tp1 tp2 : List Expr)
        (σ₁ : State),
      ⌜ValidExec extr⌝ -∗
      ⌜extr.EndsIn (tp1 ++ fill K e₁ :: tp2, σ₁)⌝ -∗
      ⌜localeOf tp1 (fill K e₁) = ζ⌝ -∗
      stateInterp extr atr ={E,∅}=∗
        ⌜reducibleIfNotStuck s e₁ σ₁⌝ ∗
        ∀ (e₂ : Expr) (σ₂ : State) (efs : List Expr),
          ⌜primStep e₁ σ₁ e₂ σ₂ efs⌝ ={∅}=∗ ▷ |={∅,E}=>
          ∃ (δ₂ : M.mstate) (ℓ : M.mlabel),
            stateInterp (extr :tr[some ζ]: (tp1 ++ fill K e₂ :: (tp2 ++ efs), σ₂))
              (atr :tr[ℓ]: δ₂) ∗
            WP e₂ @ s; ζ; E {{ Φ }} ∗
            [∗list] i ↦ ef ∈ efs,
              WP ef @ s; (localeOf (tp1 ++ fill K e₁ :: (tp2 ++ efs.take i)) ef); ⊤
                {{ forkPost (localeOf (tp1 ++ fill K e₁ :: (tp2 ++ efs.take i)) ef) }}) ⊢
    WP e₁ @ s; ζ; E {{ Φ }} := by
  iintro H
  iapply wp_lift_step_fupdN He
  iintro %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hends %Hloc Hσ
  imod H $$ %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hends %Hloc Hσ with ⟨$, H⟩
  iintro !> %e₂ %σ₂ %efs %Hstep
  dsimp only [step_fupdN]
  imod H $$ %e₂ %σ₂ %efs %Hstep with H
  iintro !> !>
  iapply step_fupdN_intro LawfulSet.subset_refl
  iapply BI.laterN_intro
  iexact H

@[rocq_alias trillium.wp_lift_stuck]
theorem wp_lift_stuck (He : toVal e = none) :
    (∀ (extr : ExecutionTrace Expr) (atr : AuxiliaryTrace M) (K : Ectx) (tp1 tp2 : List Expr)
        (σ : State),
      ⌜ValidExec extr⌝ -∗
      ⌜extr.EndsIn (tp1 ++ fill K e :: tp2, σ)⌝ -∗
      stateInterp extr atr ={E,∅}=∗ ⌜Language.Stuck e σ⌝) ⊢
    WP e @[ζ] E ? {{ Φ }} := by
  rw [wp_unfold.to_eq]
  simp only [wp.pre, He]
  iintro H %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hloc %Hends Hσ
  imod H $$ %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hends Hσ with %Hstuck
  imodintro
  isplit
  · ipureintro
    trivial
  · iintro %e₂ %σ₂ %efs %Hstep
    exact absurd Hstep (Hstuck.2 e₂ σ₂ efs)

/-! ## Derived lifting lemmas -/

@[rocq_alias trillium.wp_lift_step]
theorem wp_lift_step (He : toVal e₁ = none) :
    (∀ (extr : ExecutionTrace Expr) (atr : AuxiliaryTrace M) (K : Ectx) (tp1 tp2 : List Expr)
        (σ₁ : State),
      ⌜ValidExec extr⌝ -∗
      ⌜extr.EndsIn (tp1 ++ fill K e₁ :: tp2, σ₁)⌝ -∗
      ⌜localeOf tp1 (fill K e₁) = ζ⌝ -∗
      stateInterp extr atr ={E,∅}=∗
        ⌜reducibleIfNotStuck s e₁ σ₁⌝ ∗
        ▷ ∀ (e₂ : Expr) (σ₂ : State) (efs : List Expr),
          ⌜primStep e₁ σ₁ e₂ σ₂ efs⌝ ={∅,E}=∗
          ∃ (δ₂ : M.mstate) (ℓ : M.mlabel),
            stateInterp (extr :tr[some ζ]: (tp1 ++ fill K e₂ :: (tp2 ++ efs), σ₂))
              (atr :tr[ℓ]: δ₂) ∗
            WP e₂ @ s; ζ; E {{ Φ }} ∗
            [∗list] i ↦ ef ∈ efs,
              WP ef @ s; (localeOf (tp1 ++ fill K e₁ :: (tp2 ++ efs.take i)) ef); ⊤
                {{ forkPost (localeOf (tp1 ++ fill K e₁ :: (tp2 ++ efs.take i)) ef) }}) ⊢
    WP e₁ @ s; ζ; E {{ Φ }} := by
  iintro H
  iapply wp_lift_step_fupd He
  iintro %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hends %Hloc Hσ
  imod H $$ %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hends %Hloc Hσ with ⟨$, H⟩
  iintro !> %e₂ %σ₂ %efs %Hstep !> !>
  iapply H $$ %e₂ %σ₂ %efs %Hstep

@[rocq_alias trillium.wp_lift_pure_step_no_fork]
theorem wp_lift_pure_step_no_fork [AllowsPureStep M GF] [Inhabited State] (E' : CoPset)
    (Hsafe : ∀ σ₁ : State, match s with
      | .NotStuck => Language.Reducible e₁ σ₁
      | .MaybeStuck => toVal e₁ = none)
    (Hstep : ∀ (σ₁ : State) e₂ σ₂ efs, primStep e₁ σ₁ e₂ σ₂ efs → σ₂ = σ₁ ∧ efs = []) :
    (|={E}[E']▷=> ∀ e₂ efs (σ : State), ⌜primStep e₁ σ e₂ σ efs⌝ → WP e₂ @ s; ζ; E {{ Φ }}) ⊢
    WP e₁ @ s; ζ; E {{ Φ }} := by
  have He : toVal e₁ = none := by
    have h := Hsafe default
    cases s with
    | NotStuck => exact Language.reducible_not_val h
    | MaybeStuck => exact h
  iintro H
  iapply wp_lift_step He
  iintro %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hends %Hloc Hσ
  imod H
  imod fupd_mask_subseteq (E1 := E') (E2 := ∅) LawfulSet.empty_subset with Hclose
  imodintro
  isplit
  · ipureintro
    have h := Hsafe σ₁
    cases s with
    | NotStuck => exact h
    | MaybeStuck => trivial
  inext
  iintro %e₂ %σ₂ %efs %Hst
  obtain ⟨rfl, rfl⟩ := Hstep _ _ _ _ Hst
  imod Hclose with -
  imod H
  have Hls : LocaleStep (tp1 ++ fill K e₁ :: tp2, σ₂) (some ζ) (tp1 ++ fill K e₂ :: tp2, σ₂) := by
    simpa using localeStep_fill (tp2 := tp2) Hloc Hst
  imod allowsPureStep extr atr _ _ σ₂ atr.last (some ζ) Hvalid Hends rfl Hls $$ Hσ with Hσ
  imodintro
  iexists atr.last, pureLabel GF
  simp only [List.append_nil]
  iframe Hσ
  isplitl
  · ispecialize H $$ %e₂ %([] : List Expr) %σ₂
    iapply H
    ipureintro
    exact Hst
  · iempintro

/-- The Rocq statement uses `WP e @ E ?{{ Φ }}`, i.e. (in Trillium's notation) locale `E` and
mask `⊤`; here the locale is called `ζ`. -/
@[rocq_alias trillium.wp_lift_pure_stuck]
theorem wp_lift_pure_stuck [Inhabited State] (Hstuck : ∀ σ : State, Language.Stuck e σ) :
    ⊢ WP e @[ζ] ? {{ Φ }} := by
  have He : toVal e = none := (Hstuck default).1
  iapply wp_lift_stuck He
  iintro %extr %atr %K %tp1 %tp2 %σ %_ %_ _
  iapply fupd_mask_intro_discard LawfulSet.empty_subset
  ipureintro
  exact Hstuck σ

/-- Atomic steps don't need any mask-changing business here, one can use the generic lemmas
here. -/
@[rocq_alias trillium.wp_lift_atomic_step_fupd]
theorem wp_lift_atomic_step_fupd (He : toVal e₁ = none) :
    (∀ (extr : ExecutionTrace Expr) (atr : AuxiliaryTrace M) (K : Ectx) (tp1 tp2 : List Expr)
        (σ₁ : State),
      ⌜ValidExec extr⌝ -∗
      ⌜extr.EndsIn (tp1 ++ fill K e₁ :: tp2, σ₁)⌝ -∗
      ⌜localeOf tp1 e₁ = ζ⌝ -∗
      stateInterp extr atr ={E₁}=∗
        ⌜reducibleIfNotStuck s e₁ σ₁⌝ ∗
        ∀ (e₂ : Expr) (σ₂ : State) (efs : List Expr),
          ⌜primStep e₁ σ₁ e₂ σ₂ efs⌝ ={E₁}[E₂]▷=∗
          ∃ (δ₂ : M.mstate) (ℓ : M.mlabel),
            stateInterp (extr :tr[some ζ]: (tp1 ++ fill K e₂ :: (tp2 ++ efs), σ₂))
              (atr :tr[ℓ]: δ₂) ∗
            (toVal e₂).elim iprop(False) Φ ∗
            [∗list] i ↦ ef ∈ efs,
              WP ef @ s; (localeOf (tp1 ++ fill K e₁ :: (tp2 ++ efs.take i)) ef); ⊤
                {{ forkPost (localeOf (tp1 ++ fill K e₁ :: (tp2 ++ efs.take i)) ef) }}) ⊢
    WP e₁ @ s; ζ; E₁ {{ Φ }} := by
  iintro H
  iapply wp_lift_step_fupd He
  iintro %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hends %Hloc Hσ
  imod H $$ %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hends
    %(by rw [← Language.locale_fill e₁ K tp1]; exact Hloc) Hσ with ⟨$, H⟩
  imod fupd_mask_subseteq (E1 := E₁) (E2 := ∅) LawfulSet.empty_subset with Hclose
  iintro !> %e₂ %σ₂ %efs %Hstep
  imod Hclose with -
  imod H $$ %e₂ %σ₂ %efs %Hstep with H
  imod fupd_mask_subseteq (E1 := E₂) (E2 := ∅) LawfulSet.empty_subset with Hclose
  iintro !> !>
  imod Hclose with -
  imod H with ⟨%δ₂, %ℓ, Hσ, HQ, Hefs⟩
  match He₂ : toVal e₂ with
  | none =>
    isimp only [He₂, Option.elim] at HQ
    iexfalso
    iexact HQ
  | some v =>
    isimp only [He₂, Option.elim] at HQ
    imodintro
    iexists δ₂, ℓ
    iframe Hσ Hefs
    rw [← ToVal.coe_of_toVal_eq_some He₂]
    iapply wp_value' $$ HQ

@[rocq_alias trillium.wp_lift_atomic_step]
theorem wp_lift_atomic_step (He : toVal e₁ = none) :
    (∀ (extr : ExecutionTrace Expr) (atr : AuxiliaryTrace M) (K : Ectx) (tp1 tp2 : List Expr)
        (σ₁ : State),
      ⌜ValidExec extr⌝ -∗
      ⌜extr.EndsIn (tp1 ++ fill K e₁ :: tp2, σ₁)⌝ -∗
      ⌜localeOf tp1 e₁ = ζ⌝ -∗
      stateInterp extr atr ={E}=∗
        ⌜reducibleIfNotStuck s e₁ σ₁⌝ ∗
        ▷ ∀ (e₂ : Expr) (σ₂ : State) (efs : List Expr),
          ⌜primStep e₁ σ₁ e₂ σ₂ efs⌝ ={E}=∗
          ∃ (δ₂ : M.mstate) (ℓ : M.mlabel),
            stateInterp (extr :tr[some ζ]: (tp1 ++ fill K e₂ :: (tp2 ++ efs), σ₂))
              (atr :tr[ℓ]: δ₂) ∗
            (toVal e₂).elim iprop(False) Φ ∗
            [∗list] i ↦ ef ∈ efs,
              WP ef @ s; (localeOf (tp1 ++ fill K e₁ :: (tp2 ++ efs.take i)) ef); ⊤
                {{ forkPost (localeOf (tp1 ++ fill K e₁ :: (tp2 ++ efs.take i)) ef) }}) ⊢
    WP e₁ @ s; ζ; E {{ Φ }} := by
  iintro H
  iapply wp_lift_atomic_step_fupd (E₂ := E) He
  iintro %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hends %Hloc Hσ
  imod H $$ %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hends %Hloc Hσ with ⟨$, H⟩
  iintro !> %e₂ %σ₂ %efs %Hstep !> !>
  iapply H $$ %e₂ %σ₂ %efs %Hstep

@[rocq_alias trillium.wp_lift_pure_det_step_no_fork]
theorem wp_lift_pure_det_step_no_fork [AllowsPureStep M GF] [Inhabited State] (E' : CoPset)
    (Hsafe : ∀ σ₁ : State, match s with
      | .NotStuck => Language.Reducible e₁ σ₁
      | .MaybeStuck => toVal e₁ = none)
    (Hpuredet : ∀ (σ₁ : State) e₂' σ₂ efs', primStep e₁ σ₁ e₂' σ₂ efs' →
      σ₂ = σ₁ ∧ e₂' = e₂ ∧ efs' = []) :
    (|={E}[E']▷=> WP e₂ @ s; ζ; E {{ Φ }}) ⊢ WP e₁ @ s; ζ; E {{ Φ }} := by
  iintro H
  iapply wp_lift_pure_step_no_fork E' Hsafe
    (fun σ₁ e₂' σ₂ efs h => ⟨(Hpuredet σ₁ e₂' σ₂ efs h).1, (Hpuredet σ₁ e₂' σ₂ efs h).2.2⟩)
  iapply step_fupd_wand $$ H
  iintro H %e' %efs' %σ %Hst
  obtain ⟨-, rfl, -⟩ := Hpuredet _ _ _ _ Hst
  iexact H

@[rocq_alias trillium.wp_pure_step_fupd]
theorem wp_pure_step_fupd [AllowsPureStep M GF] [Inhabited State] (E' : CoPset) {φ : Prop}
    {n : Nat} [Hexec : PureExec φ n e₁ e₂] (Hφ : φ) :
    (|={E}[E']▷=>^[n] WP e₂ @ s; ζ; E {{ Φ }}) ⊢ WP e₁ @ s; ζ; E {{ Φ }} := by
  have Hexec := Hexec.pure_exec Hφ
  induction Hexec using Relation.Iterate.head_induction_on with
  | rfl => exact .rfl
  | @head n e₁ c Hps _ IH =>
    refine .trans ?_ (wp_lift_pure_det_step_no_fork (e₂ := c) E' ?_ fun σ₁ e₂' σ₂ efs' h =>
      Hps.det h)
    · exact step_fupd_mono IH
    · intro σ
      cases s with
      | NotStuck => exact Hps.safe σ
      | MaybeStuck => exact Language.reducible_not_val (Hps.safe σ)

@[rocq_alias trillium.wp_pure_step_later]
theorem wp_pure_step_later [AllowsPureStep M GF] [Inhabited State] {φ : Prop} {n : Nat}
    [PureExec φ n e₁ e₂] (Hφ : φ) :
    ▷^[n] WP e₂ @ s; ζ; E {{ Φ }} ⊢ WP e₁ @ s; ζ; E {{ Φ }} := by
  refine .trans ?_ (wp_pure_step_fupd E Hφ)
  generalize iprop(WP e₂ @ s; ζ; E {{ Φ }}) = P
  clear * -
  induction n with
  | zero => exact .rfl
  | succ n IH =>
    simp only [step_fupdN]
    rw [(BI.laterN_succ_left n).to_eq]
    exact (BI.later_mono IH).trans (step_fupd_intro LawfulSet.subset_refl)

end Trillium
