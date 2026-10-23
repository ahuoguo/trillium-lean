/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.ProgramLogic.EctxLanguage
import Trillium.ProgramLogic.Lifting

/-!
# Lifting lemmas for evaluation-context based languages

Port of `trillium/program_logic/ectx_lifting.v`.

Some derived lemmas for ectx-based languages. As in `Trillium/ProgramLogic/Lifting.lean`, Rocq's
`WP e @ E ?{{ Φ }}` in `wp_lift_pure_head_stuck` means locale `E` and mask `⊤` and is stated with
an explicit locale `ζ`. The `Inhabited (state Λ)` section variable is only taken where it is
used.
-/

namespace Trillium

open Iris Iris.BI Iris.Std Iris.ProofMode FiniteTrace Language EctxLanguage
open Iris.ProgramLogic (ToVal EvContext EvContextOps)

#rocq_ignore trillium.reducible_not_val_inhabitant
  "Rocq-local helper registered as an `auto` hint; `reducible_not_val` is used directly"

variable {Expr Val Ectx State Locale : Type _} [EctxLanguage Expr Val Ectx State Locale]
variable {M : Model} {GF : BundledGFunctors} [IrisG Expr M GF]
variable {s : Stuckness} {E E₁ E₂ : CoPset} {ζ : Locale} {e e₁ e₂ : Expr}
variable {Φ : Val → IProp GF}

theorem reducibleIfNotStuck_of_headReducible {σ : State} (h : HeadReducible e σ) :
    reducibleIfNotStuck s e σ := by
  cases s with
  | NotStuck => exact head_prim_reducible h
  | MaybeStuck => trivial

@[rocq_alias trillium.wp_lift_head_step_fupd]
theorem wp_lift_head_step_fupd (He : toVal e₁ = none) :
    (∀ (extr : ExecutionTrace Expr) (atr : AuxiliaryTrace M) (K : Ectx) (tp1 tp2 : List Expr)
        (σ₁ : State),
      ⌜ValidExec extr⌝ -∗
      ⌜extr.EndsIn (tp1 ++ fill K e₁ :: tp2, σ₁)⌝ -∗
      ⌜localeOf tp1 (fill K e₁) = ζ⌝ -∗
      stateInterp extr atr ={E,∅}=∗
        ⌜HeadReducible e₁ σ₁⌝ ∗
        ∀ (e₂ : Expr) (σ₂ : State) (efs : List Expr),
          ⌜headStep e₁ σ₁ e₂ σ₂ efs⌝ ={∅}=∗ ▷ |={∅,E}=>
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
  imod H $$ %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hends %Hloc Hσ with ⟨%Hred, H⟩
  imodintro
  isplit
  · ipureintro
    exact reducibleIfNotStuck_of_headReducible Hred
  · iintro %e₂ %σ₂ %efs %Hstep
    iapply H $$ %e₂ %σ₂ %efs %(head_reducible_prim_step Hred Hstep)

@[rocq_alias trillium.wp_lift_head_step]
theorem wp_lift_head_step (He : toVal e₁ = none) :
    (∀ (extr : ExecutionTrace Expr) (atr : AuxiliaryTrace M) (K : Ectx) (tp1 tp2 : List Expr)
        (σ₁ : State),
      ⌜ValidExec extr⌝ -∗
      ⌜extr.EndsIn (tp1 ++ fill K e₁ :: tp2, σ₁)⌝ -∗
      stateInterp extr atr ={E,∅}=∗
        ⌜HeadReducible e₁ σ₁⌝ ∗
        ▷ ∀ (e₂ : Expr) (σ₂ : State) (efs : List Expr),
          ⌜headStep e₁ σ₁ e₂ σ₂ efs⌝ ={∅,E}=∗
          ∃ (δ₂ : M.mstate) (ℓ : M.mlabel),
            stateInterp (extr :tr[some ζ]: (tp1 ++ fill K e₂ :: (tp2 ++ efs), σ₂))
              (atr :tr[ℓ]: δ₂) ∗
            WP e₂ @ s; ζ; E {{ Φ }} ∗
            [∗list] i ↦ ef ∈ efs,
              WP ef @ s; (localeOf (tp1 ++ fill K e₁ :: (tp2 ++ efs.take i)) ef); ⊤
                {{ forkPost (localeOf (tp1 ++ fill K e₁ :: (tp2 ++ efs.take i)) ef) }}) ⊢
    WP e₁ @ s; ζ; E {{ Φ }} := by
  iintro H
  iapply wp_lift_head_step_fupd He
  iintro %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hends %Hloc Hσ
  imod H $$ %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hends Hσ with ⟨$, H⟩
  iintro !> %e₂ %σ₂ %efs %Hstep !> !>
  iapply H $$ %e₂ %σ₂ %efs %Hstep

@[rocq_alias trillium.wp_lift_head_stuck]
theorem wp_lift_head_stuck (He : toVal e = none) (Hsub : SubRedexesAreValues e) :
    (∀ (extr : ExecutionTrace Expr) (atr : AuxiliaryTrace M) (K : Ectx) (tp1 tp2 : List Expr)
        (σ : State),
      ⌜ValidExec extr⌝ -∗
      ⌜extr.EndsIn (tp1 ++ fill K e :: tp2, σ)⌝ -∗
      stateInterp extr atr ={E,∅}=∗ ⌜HeadStuck e σ⌝) ⊢
    WP e @[ζ] E ? {{ Φ }} := by
  iintro H
  iapply wp_lift_stuck He
  iintro %extr %atr %K %tp1 %tp2 %σ %Hvalid %Hends Hσ
  imod H $$ %extr %atr %K %tp1 %tp2 %σ %Hvalid %Hends Hσ with %Hstuck
  imodintro
  ipureintro
  exact head_stuck_stuck Hstuck Hsub

/-- The Rocq statement uses `WP e @ E ?{{ Φ }}`, i.e. (in Trillium's notation) locale `E` and
mask `⊤`; here the locale is called `ζ`. -/
@[rocq_alias trillium.wp_lift_pure_head_stuck]
theorem wp_lift_pure_head_stuck (He : toVal e = none) (Hsub : SubRedexesAreValues e)
    (Hstuck : ∀ σ : State, HeadStuck e σ) :
    ⊢ WP e @[ζ] ? {{ Φ }} := by
  iapply wp_lift_head_stuck He Hsub
  iintro %extr %atr %K %tp1 %tp2 %σ %_ %_ _
  iapply fupd_mask_intro_discard LawfulSet.empty_subset
  ipureintro
  exact Hstuck σ

@[rocq_alias trillium.wp_lift_atomic_head_step_fupd]
theorem wp_lift_atomic_head_step_fupd (He : toVal e₁ = none) :
    (∀ (extr : ExecutionTrace Expr) (atr : AuxiliaryTrace M) (K : Ectx) (tp1 tp2 : List Expr)
        (σ₁ : State),
      ⌜ValidExec extr⌝ -∗
      ⌜extr.EndsIn (tp1 ++ fill K e₁ :: tp2, σ₁)⌝ -∗
      ⌜localeOf tp1 e₁ = ζ⌝ -∗
      stateInterp extr atr ={E₁}=∗
        ⌜HeadReducible e₁ σ₁⌝ ∗
        ∀ (e₂ : Expr) (σ₂ : State) (efs : List Expr),
          ⌜headStep e₁ σ₁ e₂ σ₂ efs⌝ ={E₁}[E₂]▷=∗
          ∃ (δ₂ : M.mstate) (ℓ : M.mlabel),
            stateInterp (extr :tr[some ζ]: (tp1 ++ fill K e₂ :: (tp2 ++ efs), σ₂))
              (atr :tr[ℓ]: δ₂) ∗
            (toVal e₂).elim iprop(False) Φ ∗
            [∗list] i ↦ ef ∈ efs,
              WP ef @ s; (localeOf (tp1 ++ fill K e₁ :: (tp2 ++ efs.take i)) ef); ⊤
                {{ forkPost (localeOf (tp1 ++ fill K e₁ :: (tp2 ++ efs.take i)) ef) }}) ⊢
    WP e₁ @ s; ζ; E₁ {{ Φ }} := by
  iintro H
  iapply wp_lift_atomic_step_fupd He
  iintro %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hends %Hloc Hσ
  imod H $$ %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hends %Hloc Hσ with ⟨%Hred, H⟩
  imodintro
  isplit
  · ipureintro
    exact reducibleIfNotStuck_of_headReducible Hred
  · iintro %e₂ %σ₂ %efs %Hstep
    iapply H $$ %e₂ %σ₂ %efs %(head_reducible_prim_step Hred Hstep)

@[rocq_alias trillium.wp_lift_atomic_head_step]
theorem wp_lift_atomic_head_step (He : toVal e₁ = none) :
    (∀ (extr : ExecutionTrace Expr) (atr : AuxiliaryTrace M) (K : Ectx) (tp1 tp2 : List Expr)
        (σ₁ : State),
      ⌜ValidExec extr⌝ -∗
      ⌜extr.EndsIn (tp1 ++ fill K e₁ :: tp2, σ₁)⌝ -∗
      ⌜localeOf tp1 e₁ = ζ⌝ -∗
      stateInterp extr atr ={E}=∗
        ⌜HeadReducible e₁ σ₁⌝ ∗
        ▷ ∀ (e₂ : Expr) (σ₂ : State) (efs : List Expr),
          ⌜headStep e₁ σ₁ e₂ σ₂ efs⌝ ={E}=∗
          ∃ (δ₂ : M.mstate) (ℓ : M.mlabel),
            stateInterp (extr :tr[some ζ]: (tp1 ++ fill K e₂ :: (tp2 ++ efs), σ₂))
              (atr :tr[ℓ]: δ₂) ∗
            (toVal e₂).elim iprop(False) Φ ∗
            [∗list] i ↦ ef ∈ efs,
              WP ef @ s; (localeOf (tp1 ++ fill K e₁ :: (tp2 ++ efs.take i)) ef); ⊤
                {{ forkPost (localeOf (tp1 ++ fill K e₁ :: (tp2 ++ efs.take i)) ef) }}) ⊢
    WP e₁ @ s; ζ; E {{ Φ }} := by
  iintro H
  iapply wp_lift_atomic_step He
  iintro %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hends %Hloc Hσ
  imod H $$ %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hends %Hloc Hσ with ⟨%Hred, H⟩
  imodintro
  isplit
  · ipureintro
    exact reducibleIfNotStuck_of_headReducible Hred
  · inext
    iintro %e₂ %σ₂ %efs %Hstep
    iapply H $$ %e₂ %σ₂ %efs %(head_reducible_prim_step Hred Hstep)

@[rocq_alias trillium.wp_lift_atomic_head_step_no_fork_fupd]
theorem wp_lift_atomic_head_step_no_fork_fupd (He : toVal e₁ = none) :
    (∀ (extr : ExecutionTrace Expr) (atr : AuxiliaryTrace M) (K : Ectx) (tp1 tp2 : List Expr)
        (σ₁ : State),
      ⌜ValidExec extr⌝ -∗
      ⌜extr.EndsIn (tp1 ++ fill K e₁ :: tp2, σ₁)⌝ -∗
      ⌜localeOf tp1 e₁ = ζ⌝ -∗
      stateInterp extr atr ={E₁}=∗
        ⌜HeadReducible e₁ σ₁⌝ ∗
        ∀ (e₂ : Expr) (σ₂ : State) (efs : List Expr),
          ⌜headStep e₁ σ₁ e₂ σ₂ efs⌝ ={E₁}[E₂]▷=∗
          ∃ (δ₂ : M.mstate) (ℓ : M.mlabel),
            ⌜efs = []⌝ ∗
            stateInterp (extr :tr[some ζ]: (tp1 ++ fill K e₂ :: (tp2 ++ efs), σ₂))
              (atr :tr[ℓ]: δ₂) ∗
            (toVal e₂).elim iprop(False) Φ) ⊢
    WP e₁ @ s; ζ; E₁ {{ Φ }} := by
  iintro H
  iapply wp_lift_atomic_head_step_fupd He
  iintro %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hends %Hloc Hσ
  imod H $$ %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hends %Hloc Hσ with ⟨$, H⟩
  imodintro
  iintro %e₂ %σ₂ %efs %Hstep
  imod H $$ %e₂ %σ₂ %efs %Hstep with H
  iintro !> !>
  imod H with ⟨%δ₂, %ℓ, %Hefs, Hσ, HΦ⟩
  subst Hefs
  imodintro
  iexists δ₂, ℓ
  iframe Hσ HΦ
  iempintro

@[rocq_alias trillium.wp_lift_atomic_head_step_no_fork]
theorem wp_lift_atomic_head_step_no_fork (He : toVal e₁ = none) :
    (∀ (extr : ExecutionTrace Expr) (atr : AuxiliaryTrace M) (K : Ectx) (tp1 tp2 : List Expr)
        (σ₁ : State),
      ⌜ValidExec extr⌝ -∗
      ⌜extr.EndsIn (tp1 ++ fill K e₁ :: tp2, σ₁)⌝ -∗
      ⌜localeOf tp1 e₁ = ζ⌝ -∗
      stateInterp extr atr ={E}=∗
        ⌜HeadReducible e₁ σ₁⌝ ∗
        ▷ ∀ (e₂ : Expr) (σ₂ : State) (efs : List Expr),
          ⌜headStep e₁ σ₁ e₂ σ₂ efs⌝ ={E}=∗
          ∃ (δ₂ : M.mstate) (ℓ : M.mlabel),
            ⌜efs = []⌝ ∗
            stateInterp (extr :tr[some ζ]: (tp1 ++ fill K e₂ :: (tp2 ++ efs), σ₂))
              (atr :tr[ℓ]: δ₂) ∗
            (toVal e₂).elim iprop(False) Φ) ⊢
    WP e₁ @ s; ζ; E {{ Φ }} := by
  iintro H
  iapply wp_lift_atomic_head_step He
  iintro %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hends %Hloc Hσ
  imod H $$ %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hends %Hloc Hσ with ⟨$, H⟩
  imodintro
  inext
  iintro %e₂ %σ₂ %efs %Hstep
  imod H $$ %e₂ %σ₂ %efs %Hstep with ⟨%δ₂, %ℓ, %Hefs, Hσ, HΦ⟩
  subst Hefs
  imodintro
  iexists δ₂, ℓ
  iframe Hσ HΦ
  iempintro

@[rocq_alias trillium.wp_lift_pure_det_head_step_no_fork]
theorem wp_lift_pure_det_head_step_no_fork [AllowsPureStep M GF] [Inhabited State]
    (E' : CoPset) (He : toVal e₁ = none) (Hred : ∀ σ₁ : State, HeadReducible e₁ σ₁)
    (Hdet : ∀ (σ₁ : State) e₂' σ₂ efs', headStep e₁ σ₁ e₂' σ₂ efs' →
      σ₂ = σ₁ ∧ e₂' = e₂ ∧ efs' = []) :
    (|={E}[E']▷=> WP e₂ @ s; ζ; E {{ Φ }}) ⊢ WP e₁ @ s; ζ; E {{ Φ }} := by
  refine wp_lift_pure_det_step_no_fork E' (fun σ₁ => ?_)
    (fun σ₁ e₂' σ₂ efs' h => Hdet σ₁ e₂' σ₂ efs' (head_reducible_prim_step (Hred σ₁) h))
  cases s with
  | NotStuck => exact head_prim_reducible (Hred σ₁)
  | MaybeStuck => exact He

@[rocq_alias trillium.wp_lift_pure_det_head_step_no_fork']
theorem wp_lift_pure_det_head_step_no_fork' [AllowsPureStep M GF] [Inhabited State]
    (He : toVal e₁ = none) (Hred : ∀ σ₁ : State, HeadReducible e₁ σ₁)
    (Hdet : ∀ (σ₁ : State) e₂' σ₂ efs', headStep e₁ σ₁ e₂' σ₂ efs' →
      σ₂ = σ₁ ∧ e₂' = e₂ ∧ efs' = []) :
    ▷ WP e₂ @ s; ζ; E {{ Φ }} ⊢ WP e₁ @ s; ζ; E {{ Φ }} :=
  (step_fupd_intro LawfulSet.subset_refl).trans
    (wp_lift_pure_det_head_step_no_fork E He Hred Hdet)

end Trillium
