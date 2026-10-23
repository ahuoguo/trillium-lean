/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Iris.Instances.Lib.FUpd
import Iris.ProofMode
import Trillium.BI.WeakestPre
import Trillium.ProgramLogic.Traces

/-!
# Trillium's weakest precondition

Port of `trillium/program_logic/weakestpre.v`.

## Representation

* The Rocq class `irisG Λ M Σ` is `Trillium.IrisG Expr M GF`. The language (`Expr` with its
  `Trillium.Language` instance) and the model `M` are `outParam`s: as in Rocq, where
  `pre_step`'s arguments `Λ M` are found by unification with the unique `irisG` instance in
  context, a `BundledGFunctors` determines the language and model of the program logic. This is
  needed since e.g. `|~{E}~| P` only mentions `P : IProp GF`.
* `pre_step` is `Trillium.preStep` with the notations `|~{E1,E2}~| P`, `|~{E}~| P` and
  `|~~| P`. Its proof-mode support (`IntoPreStep`, `modality_preStep`, the `FromModal` and
  `ElimModal` instances) makes `imodintro` and `imod` work on `|~{E}~|`.
* `wp` is the fixpoint (iris-lean's `fixpoint`) of the contractive `wp.pre`, following
  iris-lean's `Iris/ProgramLogic/WeakestPre.lean`. The Rocq seals are not used.
* `AllowsStuttering M GF` / `AllowsPureStep M GF`: the class projections take the language
  explicitly (their types do not mention it), so use the wrappers `stutteringLabel GF`,
  `pureLabel GF`, `allowsStuttering`, `allowsPureStep`.
* `stateInterp extr atr` alone does not determine `GF`; in statements without another `IProp GF`
  on the same side, write `stateInterp (GF := GF) extr atr`.
* Rocq's `TCEq (to_val e) None` premises are plain hypotheses `toVal e = none`.
* Rocq's `ectx_fill K e` is `fill K e`, `locale_of` is `localeOf`, `trace_ends_in` is
  `FiniteTrace.EndsIn`, `trace_extend` is `FiniteTrace.extend` (`ex :tr[ℓ]: c`), `trace_length`
  is `FiniteTrace.length`.
-/

namespace Trillium

open Iris Iris.BI Iris.Std Iris.ProofMode FiniteTrace Language
open Iris.ProgramLogic (ToVal EvContext EvContextOps)

/-! ## The `IrisG` class -/

/-- The ghost state and interpretations needed to state Trillium's weakest preconditions for the
language `Expr` with model `M` (Rocq `irisG Λ M Σ`). -/
@[rocq_alias trillium.irisG]
class IrisG (Expr : outParam (Type _)) {Val Ectx State Locale : outParam (Type _)}
    [Language Expr Val Ectx State Locale] (M : outParam Model) (GF : BundledGFunctors) where
  [invGS : InvGS_gen .hasNoLC GF]
  /-- The state interpretation, an invariant holding between each step of reduction. It is
  indexed by the execution trace so far and the auxiliary (model) trace. -/
  stateInterp : ExecutionTrace Expr → AuxiliaryTrace M → IProp GF
  /-- A fixed postcondition for any forked-off thread, depending on its locale. -/
  forkPost : Locale → Val → IProp GF

attribute [implicit_reducible, instance] IrisG.invGS

export IrisG (stateInterp forkPost)

variable {Expr Val Ectx State Locale : Type _} [Language Expr Val Ectx State Locale]
variable {M : Model} {GF : BundledGFunctors} [IrisG Expr M GF]

/-! ## The `pre_step` modality -/

/-- `|~{E1,E2}~| P`: given the current state interpretation, one can (by a fancy update from
`E1` to `E2`) obtain `P` and give the state interpretation back. -/
@[rocq_alias trillium.pre_step, rocq_alias trillium.pre_step_def]
def preStep (E1 E2 : CoPset) (P : IProp GF) : IProp GF :=
  iprop(∀ (extr : ExecutionTrace Expr) (atr : AuxiliaryTrace M),
    stateInterp extr atr ={E1,E2}=∗ stateInterp extr atr ∗ P)

#rocq_ignore trillium.pre_step_aux "seal/unseal machinery not used in Lean"
#rocq_ignore trillium.pre_step_unseal "seal/unseal machinery not used in Lean; `preStep` is a plain def"

/-- `|~{E1,E2}~| P`. -/
syntax:max "|~{ " term " , " term " }~| " term : term
/-- `|~{E}~| P`, i.e. `|~{E,E}~| P`. -/
syntax:max "|~{ " term " }~| " term : term
/-- `|~~| P`, i.e. `|~{⊤}~| P`. -/
syntax:max "|~~| " term : term

macro_rules
  | `(iprop(|~{%$tk $E1 , $E2 }~| $P)) => ``($(BI.wrapIprop tk ``preStep) $E1 $E2 iprop($P))
  | `(iprop(|~{%$tk $E }~| $P)) => ``($(BI.wrapIprop tk ``preStep) $E $E iprop($P))
  | `(iprop(|~~|%$tk $P)) => ``($(BI.wrapIprop tk ``preStep) ⊤ ⊤ iprop($P))

delab_rule preStep
  | `($_ $E1 $E2 $P) => do
    let P ← BI.unpackIprop P
    if E1 == E2 then ``(iprop(|~{ $E1 }~| $P)) else ``(iprop(|~{ $E1 , $E2 }~| $P))

section preStep

variable {E E1 E2 E3 : CoPset} {P Q : IProp GF}

@[rocq_alias trillium.pre_step_intro]
theorem preStep_intro : P ⊢ |~{E}~| P := by
  unfold preStep
  iintro HP %extr %atr Hσ
  iframe

@[rocq_alias trillium.pre_step_comm]
theorem preStep_comm : (|~{E}~| P) ⊢ (|~{E}~| Q) -∗ |~{E}~| P ∗ Q := by
  unfold preStep
  iintro HP HQ %extr %atr Hσ
  imod HP $$ Hσ with ⟨Hσ, HP⟩
  imod HQ $$ Hσ with ⟨Hσ, HQ⟩
  iframe

@[rocq_alias trillium.pre_step_mono]
theorem preStep_mono : (P -∗ Q) ⊢ (|~{E}~| P) -∗ |~{E}~| Q := by
  unfold preStep
  iintro HPQ HP %extr %atr Hσ
  imod HP $$ Hσ with ⟨Hσ, HP⟩
  iframe
  iapply HPQ $$ HP

@[rocq_alias trillium.fupd_pre_step_fupd]
theorem fupd_preStep_fupd : (|={E}=> |~{E}~| |={E}=> P) ⊢ |~{E}~| P := by
  unfold preStep
  iintro HP %extr %atr Hσ
  imod HP
  imod HP $$ Hσ with ⟨Hσ, >HP⟩
  iframe

@[rocq_alias trillium.pre_step_fupd]
theorem preStep_fupd : (|~{E}~| |={E}=> P) ⊢ |~{E}~| P := by
  iintro HP
  iapply fupd_preStep_fupd
  imodintro
  iexact HP

@[rocq_alias trillium.fupd_pre_step]
theorem fupd_preStep : (|={E}=> |~{E}~| P) ⊢ |~{E}~| P := by
  iintro HP
  iapply fupd_preStep_fupd
  imod HP
  imodintro
  iapply preStep_mono $$ [] HP
  iintro HP !>
  iexact HP

@[rocq_alias trillium.pre_step_elim]
theorem preStep_elim (extr : ExecutionTrace Expr) (atr : AuxiliaryTrace M) :
    stateInterp extr atr ⊢ (|~{E}~| P) ={E}=∗ stateInterp extr atr ∗ P := by
  unfold preStep
  iintro Hσ HP
  iapply HP $$ Hσ

@[rocq_alias trillium.pre_step_ne]
instance preStep_ne : OFE.NonExpansive (preStep (Expr := Expr) (M := M) (GF := GF) E1 E2) where
  ne {n P Q} HPQ := by
    refine BI.forall_ne fun extr => BI.forall_ne fun atr => ?_
    exact BI.wand_ne.ne .rfl (BIFUpdate.ne.ne (BI.sep_ne.ne .rfl HPQ))

#rocq_ignore trillium.pre_step_proper "Rocq `Proper` instance; derivable from `preStep_ne`"

/-- Proof-mode class: `P` can be turned into `|~{E}~| Q`. Used to transform the spatial context
when introducing `|~{E}~|`. -/
@[ipm_class, rocq_alias trillium.IntoPreStep]
class IntoPreStep (E : CoPset) (P : IProp GF) (Q : outParam (IProp GF)) where
  into_preStep : P ⊢ |~{E}~| Q

@[rocq_alias trillium.into_pre_step_id]
instance (priority := high) intoPreStep_id : IntoPreStep E iprop(|~{E}~| P) P where
  into_preStep := .rfl

@[rocq_alias trillium.into_pre_step_intro]
instance (priority := low) intoPreStep_intro : IntoPreStep E P P where
  into_preStep := preStep_intro

/-- The `|~{E}~|` modality: the intuitionistic context is kept, the spatial context is
transformed with `IntoPreStep E`. -/
@[rocq_alias trillium.modality_pre_step, rocq_alias trillium.modality_pre_step_mixin]
def modality_preStep (E : CoPset) : Modality (IProp GF) (IProp GF) where
  M := preStep (Expr := Expr) (M := M) E E
  action
  | true => .id
  | false => .transform fun P Q => IntoPreStep (Expr := Expr) (M := M) E P Q
  spec
  | true => fun _ => preStep_intro
  | false => fun _ _ h => h.into_preStep
  emp := preStep_intro
  mono h := (BI.emp_sep.2.trans (BI.sep_mono_left (BI.entails_wand h))).trans
    (BI.wand_elim (preStep_mono (Expr := Expr) (M := M)))
  sep := BI.wand_elim preStep_comm

@[rocq_alias trillium.from_modality_pre_step]
instance fromModal_preStep io : FromModal io (modality_preStep (Expr := Expr) (M := M) E) True
    iprop(|~{E}~| P) iprop(|~{E}~| P) P where
  from_modal _ := .rfl

@[rocq_alias trillium.elim_modal_pre_step_pre_step]
instance elimModal_preStep_preStep p io :
    ElimModal True p io false iprop(|~{E1,E2}~| P) P iprop(|~{E1,E3}~| Q)
      iprop(|~{E2,E3}~| Q) where
  elim_modal _ := by
    unfold preStep
    iintro ⟨HP, HPQ⟩
    icases BI.intuitionisticallyIf_elim $$ HP with HP
    iintro %extr %atr Hσ
    imod HP $$ Hσ with ⟨Hσ, HP'⟩
    iapply HPQ $$ HP' Hσ

@[rocq_alias trillium.elim_modal_pre_step_fupd]
instance elimModal_preStep_fupd p io :
    ElimModal True p io false iprop(|={E1,E2}=> P) P iprop(|~{E1,E3}~| Q)
      iprop(|~{E2,E3}~| Q) where
  elim_modal _ := by
    unfold preStep
    iintro ⟨HP, HPQ⟩
    icases BI.intuitionisticallyIf_elim $$ HP with HP
    iintro %extr %atr Hσ
    imod HP
    iapply HPQ $$ HP Hσ

@[rocq_alias trillium.pre_step_mask_subseteq]
theorem preStep_mask_subseteq (h : E2 ⊆ E1) :
    ⊢@{IProp GF} |~{E1,E2}~| |~{E2,E1}~| True := by
  unfold preStep
  iintro %extr %atr Hσ
  imod fupd_mask_subseteq h with Hclose
  imodintro
  iframe
  iintro %extr' %atr' Hσ'
  imod Hclose
  imodintro
  iframe

@[rocq_alias trillium.elim_modal_pre_step_bupd]
instance elimModal_preStep_bupd p io :
    ElimModal True p io false iprop(|==> P) P iprop(|~{E1,E2}~| Q) iprop(|~{E1,E2}~| Q) where
  elim_modal _ := by
    unfold preStep
    iintro ⟨HP, HPQ⟩
    icases BI.intuitionisticallyIf_elim $$ HP with HP
    iintro %extr %atr Hσ
    imod HP
    iapply HPQ $$ HP Hσ

end preStep

/-! ## Weakest preconditions -/

/-- Reducibility condition depending on stuckness (Rocq
`if s is NotStuck then reducible e σ else True`). -/
abbrev reducibleIfNotStuck (s : Stuckness) (e : Expr) (σ : State) : Prop :=
  match s with
  | .NotStuck => Language.Reducible e σ
  | .MaybeStuck => True

/-- One unfolding of Trillium's weakest precondition. -/
@[rocq_alias trillium.wp_pre]
def wp.pre (s : Stuckness) (wp : CoPset → Locale → Expr → (Val → IProp GF) → IProp GF)
    (E : CoPset) (ζ : Locale) (e₁ : Expr) (Φ : Val → IProp GF) : IProp GF :=
  match toVal e₁ with
  | some v => iprop(|~{E}~| Φ v)
  | none => iprop(∀ (extr : ExecutionTrace Expr) (atr : AuxiliaryTrace M) (K : Ectx)
      (tp1 tp2 : List Expr) (σ₁ : State),
      ⌜ValidExec extr⌝ -∗
      ⌜localeOf tp1 (fill K e₁) = ζ⌝ -∗
      ⌜extr.EndsIn (tp1 ++ fill K e₁ :: tp2, σ₁)⌝ -∗
      stateInterp extr atr ={E,∅}=∗
        ⌜reducibleIfNotStuck s e₁ σ₁⌝ ∗
        ∀ (e₂ : Expr) (σ₂ : State) (efs : List Expr),
          ⌜primStep e₁ σ₁ e₂ σ₂ efs⌝ ={∅}▷=∗^[extr.length + 1] |={∅,E}=>
          ∃ (δ₂ : M.mstate) (ℓ : M.mlabel),
            stateInterp (extr :tr[some ζ]: (tp1 ++ fill K e₂ :: (tp2 ++ efs), σ₂))
              (atr :tr[ℓ]: δ₂) ∗
            wp E ζ e₂ Φ ∗
            [∗list] i ↦ ef ∈ efs,
              wp ⊤ (localeOf (tp1 ++ fill K e₁ :: (tp2 ++ efs.take i)) ef) ef
                (forkPost (localeOf (tp1 ++ fill K e₁ :: (tp2 ++ efs.take i)) ef)))

@[rocq_alias trillium.wp_pre_contractive]
instance wp.pre.contractive (s : Stuckness) :
    OFE.Contractive (wp.pre (Expr := Expr) (M := M) (GF := GF) s) where
  distLater_dist := by
    intro n wp wp' Hwp E ζ e₁ Φ
    unfold pre
    cases toVal e₁
    case some _ => exact .rfl
    case none =>
      refine BI.forall_ne fun extr => BI.forall_ne fun atr => BI.forall_ne fun K => ?_
      refine BI.forall_ne fun tp1 => BI.forall_ne fun tp2 => BI.forall_ne fun σ₁ => ?_
      refine BI.wand_ne.ne .rfl <| BI.wand_ne.ne .rfl <| BI.wand_ne.ne .rfl ?_
      refine BI.wand_ne.ne .rfl <| BIFUpdate.ne.ne <| BI.sep_ne.ne .rfl ?_
      refine BI.forall_ne fun e₂ => BI.forall_ne fun σ₂ => BI.forall_ne fun efs => ?_
      refine BI.wand_ne.ne .rfl ?_
      refine step_fupdN_contractive.distLater_dist fun m hm => ?_
      refine BIFUpdate.ne.ne <| BI.exists_ne fun δ₂ => BI.exists_ne fun ℓ => ?_
      refine BI.sep_ne.ne .rfl <| BI.sep_ne.ne (Hwp m hm _ _ _ _) ?_
      exact BI.BigSepL.bigSepL_dist fun _ => Hwp m hm _ _ _ _

/-- Trillium's weakest precondition, the fixpoint of `wp.pre`. -/
@[rocq_alias trillium.wp_def]
instance wp.def : Wp (IProp GF) Expr Val Locale Stuckness where
  wp s := fixpoint (wp.pre (Expr := Expr) (M := M) s)

#rocq_ignore trillium.wp_aux "seal/unseal machinery not used in Lean"
#rocq_ignore trillium.wp' "seal/unseal machinery not used in Lean; the instance is `wp.def`"
#rocq_ignore trillium.wp_eq "seal/unseal machinery not used in Lean; `wp.def` unfolds by `rfl`"

section wp

variable {s s₁ s₂ : Stuckness} {E E₁ E₂ : CoPset} {ζ : Locale} {e : Expr} {v : Val}
variable {Φ Ψ : Val → IProp GF} {P Q R : IProp GF}

@[rocq_alias trillium.wp_unfold]
theorem wp_unfold :
    WP e @ s; ζ; E {{ Φ }} ⊣⊢ wp.pre (M := M) s (Wp.wp (PROP := IProp GF) s) E ζ e Φ :=
  BI.equiv_iff.1 <| OFE.eq_dist_2 <|
    fun _n => (fixpoint_unfold (f := (wp.pre (M := M) s).toContractiveHom)).dist E ζ e Φ

@[rocq_alias trillium.wp_ne]
instance wp_ne : OFE.NonExpansive (Wp.wp (PROP := IProp GF) s E ζ e) where
  ne {n Φ₁ Φ₂} HΦ := by
    induction n using Nat.strongRecOn generalizing e E ζ Φ₁ Φ₂ with | ind n IH =>
    simp only [wp_unfold.to_eq]
    dsimp only [wp.pre]
    cases toVal e
    case some v =>
      exact preStep_ne.ne (HΦ v)
    case none =>
      refine BI.forall_ne fun extr => BI.forall_ne fun atr => BI.forall_ne fun K => ?_
      refine BI.forall_ne fun tp1 => BI.forall_ne fun tp2 => BI.forall_ne fun σ₁ => ?_
      refine BI.wand_ne.ne .rfl <| BI.wand_ne.ne .rfl <| BI.wand_ne.ne .rfl ?_
      refine BI.wand_ne.ne .rfl <| BIFUpdate.ne.ne <| BI.sep_ne.ne .rfl ?_
      refine BI.forall_ne fun e₂ => BI.forall_ne fun σ₂ => BI.forall_ne fun efs => ?_
      refine BI.wand_ne.ne .rfl ?_
      refine step_fupdN_contractive.distLater_dist fun m hm => ?_
      refine BIFUpdate.ne.ne <| BI.exists_ne fun δ₂ => BI.exists_ne fun ℓ => ?_
      refine BI.sep_ne.ne .rfl <| BI.sep_ne.ne ?_ .rfl
      exact IH m hm <| OFE.dist_lt HΦ hm

#rocq_ignore trillium.wp_proper "Rocq `Proper` instance; derivable from `wp_ne`"

@[rocq_alias trillium.wp_contractive]
theorem wp_contractive (h : toVal e = none) :
    OFE.Contractive (Wp.wp (PROP := IProp GF) s E ζ e) where
  distLater_dist {n Φ₁ Φ₂} HΦ := by
    simp only [wp_unfold.to_eq]
    simp only [wp.pre, h]
    refine BI.forall_ne fun extr => BI.forall_ne fun atr => BI.forall_ne fun K => ?_
    refine BI.forall_ne fun tp1 => BI.forall_ne fun tp2 => BI.forall_ne fun σ₁ => ?_
    refine BI.wand_ne.ne .rfl <| BI.wand_ne.ne .rfl <| BI.wand_ne.ne .rfl ?_
    refine BI.wand_ne.ne .rfl <| BIFUpdate.ne.ne <| BI.sep_ne.ne .rfl ?_
    refine BI.forall_ne fun e₂ => BI.forall_ne fun σ₂ => BI.forall_ne fun efs => ?_
    refine BI.wand_ne.ne .rfl ?_
    refine step_fupdN_contractive.distLater_dist fun m hm => ?_
    refine BIFUpdate.ne.ne <| BI.exists_ne fun δ₂ => BI.exists_ne fun ℓ => ?_
    refine BI.sep_ne.ne .rfl <| BI.sep_ne.ne ?_ .rfl
    exact wp_ne.ne (HΦ m hm)

@[rocq_alias trillium.wp_value']
theorem wp_value' : Φ v ⊢ WP (v : Expr) @ s; ζ; E {{ Φ }} := by
  rw [wp_unfold.to_eq]
  simp only [wp.pre, ToVal.toVal_coe]
  exact preStep_intro

@[rocq_alias trillium.wp_value_inv']
theorem wp_value_inv' : WP (v : Expr) @ s; ζ; E {{ Φ }} ⊢ |~{E}~| Φ v := by
  rw [wp_unfold.to_eq]
  simp only [wp.pre, ToVal.toVal_coe]
  exact .rfl

@[rocq_alias trillium.wp_strong_mono]
theorem wp_strong_mono (hs : s₁ ≤ s₂) (hE : E₁ ⊆ E₂) :
    ⊢ WP e @ s₁; ζ; E₁ {{ Φ }} -∗ (∀ v, Φ v ={E₂}=∗ Ψ v) -∗ WP e @ s₂; ζ; E₂ {{ Ψ }} := by
  clear wp_strong_mono
  iloeb as IH generalizing %e %ζ %Φ %Ψ %E₁ %E₂ %hE
  rw [wp_unfold.to_eq, wp_unfold.to_eq]
  iintro H HΦ
  dsimp only [wp.pre]
  match toVal e with
  | some v =>
    dsimp only
    imod preStep_mask_subseteq hE with Hclose
    imod H
    imod Hclose with -
    imod HΦ $$ H with H
    imodintro
    iexact H
  | none =>
    dsimp only
    iintro %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hloc %Hends Hσ
    imod fupd_mask_subseteq hE with Hclose
    icases H $$ %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hloc %Hends Hσ with >⟨%h, H⟩
    imodintro
    isplit
    · ipureintro
      revert h
      cases s₁ <;> cases s₂ <;> simp_all [LE.le]
    · iintro %e₂ %σ₂ %efs %Hstep
      dsimp only [step_fupdN]
      imod H $$ %e₂ %σ₂ %efs %Hstep with H
      iintro !> !>
      imod H
      imodintro
      iapply step_fupdN_wand $$ H
      iintro >⟨%δ₂, %ℓ, Hσ, H, Hefs⟩
      imod Hclose with -
      imodintro
      iexists δ₂, ℓ
      iframe Hσ
      isplitr [Hefs]
      · iapply IH $$ %e₂ %ζ %Φ %Ψ %E₁ %E₂ %hE H HΦ
      · iapply BI.BigSepL.bigSepL_impl $$ Hefs
        iintro !> %k %ef %_ H
        iapply IH $$ %ef %_ %_ %_ %⊤ %⊤ %LawfulSet.subset_refl H
        iintro %v H
        imodintro
        iexact H

@[rocq_alias trillium.fupd_wp]
theorem fupd_wp : (|={E}=> WP e @ s; ζ; E {{ Φ }}) ⊢ WP e @ s; ζ; E {{ Φ }} := by
  simp only [wp_unfold.to_eq]
  iintro H
  match h : toVal e with
  | some v =>
    simp only [wp.pre, h]
    imod H
    iexact H
  | none =>
    simp only [wp.pre, h]
    iintro %extr %atr %K %tp1 %tp2 %σ₁
    imod H
    iapply H

@[rocq_alias trillium.wp_fupd]
theorem wp_fupd : WP e @ s; ζ; E {{ v, |={E}=> Φ v }} ⊢ WP e @ s; ζ; E {{ Φ }} := by
  iintro H
  iapply wp_strong_mono (Std.IsPreorder.le_refl _) LawfulSet.subset_refl $$ H
  iintro %v H
  iexact H

end wp

/-! ## Stuttering steps -/

/-- The state interpretation allows stuttering steps, i.e. steps of the program that do not
change the configuration, matched by a model step labelled `stuttering_label` that does not
change the model state. -/
@[rocq_alias trillium.AllowsStuttering]
class AllowsStuttering {Expr Val Ectx State Locale : Type _} [Language Expr Val Ectx State Locale]
    (M : Model) (GF : BundledGFunctors) [IrisG Expr M GF] where
  stuttering_label : M.mlabel
  allows_stuttering (extr : ExecutionTrace Expr) (atr : AuxiliaryTrace M)
      (c : List Expr × State) (δ : M.mstate) (oζ : Option Locale) :
    ValidExec extr → extr.EndsIn c → atr.EndsIn δ → LocaleStep c oζ c →
    stateInterp (GF := GF) extr atr ⊢
      |==> stateInterp (GF := GF) (extr :tr[oζ]: c) (atr :tr[stuttering_label]: δ)

/-- The state interpretation allows pure steps, i.e. steps that do not change the state, matched
by a model step labelled `pure_label` that does not change the model state. -/
@[rocq_alias trillium.AllowsPureStep]
class AllowsPureStep {Expr Val Ectx State Locale : Type _} [Language Expr Val Ectx State Locale]
    (M : Model) (GF : BundledGFunctors) [IrisG Expr M GF] where
  pure_label : M.mlabel
  allows_pure_step (extr : ExecutionTrace Expr) (atr : AuxiliaryTrace M)
      (tp tp' : List Expr) (σ : State) (δ : M.mstate) (oζ : Option Locale) :
    ValidExec extr → extr.EndsIn (tp, σ) → atr.EndsIn δ → LocaleStep (tp, σ) oζ (tp', σ) →
    stateInterp (GF := GF) extr atr ⊢
      |==> stateInterp (GF := GF) (extr :tr[oζ]: (tp', σ)) (atr :tr[pure_label]: δ)

/-- The stuttering label (with the language parameters implicit). -/
abbrev stutteringLabel (GF : BundledGFunctors) [IrisG Expr M GF] [AllowsStuttering M GF] :
    M.mlabel :=
  AllowsStuttering.stuttering_label (Expr := Expr) (Val := Val) (Ectx := Ectx) (State := State)
    (Locale := Locale) (GF := GF)

/-- The pure-step label (with the language parameters implicit). -/
abbrev pureLabel (GF : BundledGFunctors) [IrisG Expr M GF] [AllowsPureStep M GF] : M.mlabel :=
  AllowsPureStep.pure_label (Expr := Expr) (Val := Val) (Ectx := Ectx) (State := State)
    (Locale := Locale) (GF := GF)

theorem allowsStuttering [AllowsStuttering M GF] (extr : ExecutionTrace Expr)
    (atr : AuxiliaryTrace M) (c : List Expr × State) (δ : M.mstate) (oζ : Option Locale) :
    ValidExec extr → extr.EndsIn c → atr.EndsIn δ → LocaleStep c oζ c →
    stateInterp (GF := GF) extr atr ⊢
      |==> stateInterp (extr :tr[oζ]: c) (atr :tr[stutteringLabel GF]: δ) :=
  AllowsStuttering.allows_stuttering (Val := Val) (Ectx := Ectx) extr atr c δ oζ

theorem allowsPureStep [AllowsPureStep M GF] (extr : ExecutionTrace Expr)
    (atr : AuxiliaryTrace M) (tp tp' : List Expr) (σ : State) (δ : M.mstate)
    (oζ : Option Locale) :
    ValidExec extr → extr.EndsIn (tp, σ) → atr.EndsIn δ → LocaleStep (tp, σ) oζ (tp', σ) →
    stateInterp (GF := GF) extr atr ⊢
      |==> stateInterp (extr :tr[oζ]: (tp', σ)) (atr :tr[pureLabel GF]: δ) :=
  AllowsPureStep.allows_pure_step (Val := Val) (Ectx := Ectx) extr atr tp tp' σ δ oζ

/-- Pure steps include stuttering steps. -/
@[rocq_alias trillium.AllowsPureStep_AllowsStuttering]
instance AllowsPureStep.toAllowsStuttering [AllowsPureStep M GF] : AllowsStuttering M GF where
  stuttering_label := pureLabel GF
  allows_stuttering extr atr c δ oζ h1 h2 h3 h4 :=
    allowsPureStep extr atr c.1 c.1 c.2 δ oζ h1 h2 h3 h4

/-! ## Helpers about extending execution traces -/

section helpers

variable {extr : ExecutionTrace Expr} {K : Ectx} {tp1 tp2 efs : List Expr} {ζ : Locale}
variable {e₁ e₂ : Expr} {σ₁ σ₂ : State}

theorem localeStep_fill (Hloc : localeOf tp1 (fill K e₁) = ζ)
    (Hstep : primStep e₁ σ₁ e₂ σ₂ efs) :
    LocaleStep (tp1 ++ fill K e₁ :: tp2, σ₁) (some ζ) (tp1 ++ fill K e₂ :: (tp2 ++ efs), σ₂) :=
  Hloc ▸ LocaleStep.atomic tp1 tp2 (Language.fill_step K Hstep)

theorem validExec_extend_fill (Hvalid : ValidExec extr) (Hloc : localeOf tp1 (fill K e₁) = ζ)
    (Hends : extr.EndsIn (tp1 ++ fill K e₁ :: tp2, σ₁)) (Hstep : primStep e₁ σ₁ e₂ σ₂ efs) :
    ValidExec (extr :tr[some ζ]: (tp1 ++ fill K e₂ :: (tp2 ++ efs), σ₂)) :=
  ValidExec.extend Hvalid Hends (localeStep_fill Hloc Hstep)

theorem localeOf_fill_step (Hloc : localeOf tp1 (fill K e₁) = ζ)
    (Hstep : primStep e₁ σ₁ e₂ σ₂ efs) : localeOf tp1 (fill K e₂) = ζ :=
  (Language.locale_fill_step tp1 K Hstep).symm.trans Hloc

end helpers

section wp_atomic

variable {s : Stuckness} {E E₁ E₂ : CoPset} {ζ : Locale} {e : Expr} {Φ : Val → IProp GF}

open Language (StutteringAtomic Atomic) in
@[rocq_alias trillium.wp_stuttering_atomic]
theorem wp_stuttering_atomic [AllowsStuttering M GF]
    [hat : StutteringAtomic (State := State) (Iris.ProgramLogic.Language.Atomicity.ofStuckness s) e] :
    (|={E₁,E₂}=> WP e @ s; ζ; E₂ {{ v, |={E₂,E₁}=> Φ v }}) ⊢ WP e @ s; ζ; E₁ {{ Φ }} := by
  iintro H
  iloeb as IH
  ieval (simp only [wp_unfold.to_eq])
  ieval (simp only [wp_unfold.to_eq]) at H
  match He : toVal e with
  | some v =>
    isimp only [wp.pre, He] at H
    simp only [wp.pre, He]
    imod H
    imod H
    imod H
    imodintro
    iexact H
  | none =>
    isimp only [wp.pre, He] at H
    simp only [wp.pre, He]
    iintro %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hloc %Hends Hσ
    icombine H Hσ as HR
    ihave Hkeep := fupd_keep_plain_sep (E' := ∅)
      (P := iprop(⌜reducibleIfNotStuck s e σ₁⌝ : IProp GF)) $$ [] HR
    · iintro ⟨H, Hσ⟩
      imod H
      imod H $$ %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hloc %Hends Hσ with ⟨%Hred, -⟩
      imodintro
      ipureintro
      exact Hred
    imod Hkeep with ⟨%Hred, H, Hσ⟩
    imod fupd_mask_subseteq (E1 := E₁) (E2 := ∅) LawfulSet.empty_subset with Hmsk
    imodintro
    isplit
    · ipureintro
      exact Hred
    iintro %e₂ %σ₂ %efs %Hstep
    rcases hat.stutteringatomic Hstep with ⟨rfl, rfl, rfl⟩ | Hs
    · dsimp only [step_fupdN]
      imodintro
      inext
      have Hls : LocaleStep (tp1 ++ fill K e₂ :: tp2, σ₂) (some ζ) (tp1 ++ fill K e₂ :: tp2, σ₂) := by
        simpa using localeStep_fill (tp2 := tp2) Hloc Hstep
      imod allowsStuttering extr atr _ atr.last (some ζ) Hvalid Hends rfl Hls $$ Hσ with Hσ
      imodintro
      iapply step_fupdN_intro LawfulSet.subset_refl
      inext
      imod Hmsk with -
      imodintro
      iexists atr.last, stutteringLabel GF
      simp only [List.append_nil]
      iframe Hσ
      isplitl
      · iapply IH
        ieval (simp only [wp_unfold.to_eq])
        ieval (simp only [wp.pre, He])
        dsimp only [step_fupdN]
        iexact H
      · iempintro
    · iclear IH
      dsimp only [step_fupdN]
      imod Hmsk with -
      imod H
      imod H $$ %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hloc %Hends Hσ with ⟨-, H⟩
      imod H $$ %e₂ %σ₂ %efs %Hstep with H
      iintro !> !>
      imod H
      imodintro
      iapply step_fupdN_wand $$ H
      iintro H
      imod H with ⟨%δ₂, %ℓ, Hσ, H, Hefs⟩
      cases s with
      | NotStuck =>
        ieval (simp only [wp_unfold.to_eq]) at H
        match He₂ : toVal e₂ with
        | some v₂ =>
          isimp only [wp.pre, He₂] at H
          imod preStep_elim _ _ $$ Hσ H with ⟨Hσ, >H⟩
          imodintro
          iexists δ₂, ℓ
          iframe Hσ Hefs
          rw [← ToVal.coe_of_toVal_eq_some He₂]
          iapply wp_value' $$ H
        | none =>
          isimp only [wp.pre, He₂] at H
          imod H $$ %_ %_ %K %tp1 %(tp2 ++ efs) %σ₂
            %(validExec_extend_fill Hvalid Hloc Hends Hstep)
            %(localeOf_fill_step Hloc Hstep) %(by rfl) Hσ with ⟨%Hred₂, -⟩
          exact absurd Hred₂ (Language.not_reducible.mpr Hs)
      | MaybeStuck =>
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp Hs
        obtain rfl := ToVal.coe_of_toVal_eq_some hv
        ihave H := wp_value_inv' $$ H
        imod preStep_elim _ _ $$ Hσ H with ⟨Hσ, >H⟩
        imodintro
        iexists δ₂, ℓ
        iframe Hσ Hefs
        iapply wp_value' $$ H

/-- The common final part of the atomicity lemmas: after an atomic step to `e₂`, the
weakest precondition of `e₂` (which is irreducible or a value) can be closed. -/
theorem wp_atomic_step_close {s : Stuckness} {E₁ E₂ : CoPset} {ζ : Locale} {e₂ : Expr}
    {Φ Ψ : Val → IProp GF} {extr : ExecutionTrace Expr} {atr : AuxiliaryTrace M} {K : Ectx}
    {tp1 tp2 : List Expr} {σ₂ : State}
    (Hs : match Iris.ProgramLogic.Language.Atomicity.ofStuckness s with
      | .WeaklyAtomic => Language.Irreducible e₂ σ₂
      | .StronglyAtomic => (toVal e₂).isSome)
    (Hvalid : ValidExec extr) (Hends : extr.EndsIn (tp1 ++ fill K e₂ :: tp2, σ₂))
    (Hloc : localeOf tp1 (fill K e₂) = ζ) :
    stateInterp extr atr ⊢ WP e₂ @ s; ζ; E₂ {{ Ψ }} -∗ (∀ v, Ψ v ={E₂,E₁}=∗ Φ v) -∗
      |={E₂,E₁}=> stateInterp extr atr ∗ WP e₂ @ s; ζ; E₁ {{ Φ }} := by
  iintro Hσ H HΨ
  cases s with
  | NotStuck =>
    ieval (simp only [wp_unfold.to_eq]) at H
    match He₂ : toVal e₂ with
    | some v₂ =>
      isimp only [wp.pre, He₂] at H
      imod preStep_elim _ _ $$ Hσ H with ⟨Hσ, H⟩
      imod HΨ $$ H with H
      imodintro
      iframe Hσ
      rw [← ToVal.coe_of_toVal_eq_some He₂]
      iapply wp_value' $$ H
    | none =>
      isimp only [wp.pre, He₂] at H
      imod H $$ %extr %atr %K %tp1 %tp2 %σ₂ %Hvalid %Hloc %Hends Hσ with ⟨%Hred₂, -⟩
      exact absurd Hred₂ (Language.not_reducible.mpr Hs)
  | MaybeStuck =>
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp Hs
    obtain rfl := ToVal.coe_of_toVal_eq_some hv
    ihave H := wp_value_inv' $$ H
    imod preStep_elim _ _ $$ Hσ H with ⟨Hσ, H⟩
    imod HΨ $$ H with H
    imodintro
    iframe Hσ
    iapply wp_value' $$ H

open Language (StutteringAtomic Atomic) in
@[rocq_alias trillium.wp_stutteringatomic_take_step]
theorem wp_stutteringAtomic_take_step [AllowsStuttering M GF]
    [hat : StutteringAtomic (State := State) (Iris.ProgramLogic.Language.Atomicity.ofStuckness s) e]
    (He : toVal e = none) :
    (|={E₁,E₂}=> ∀ (extr : ExecutionTrace Expr) (atr : AuxiliaryTrace M) c₁ δ₁ ζ',
      ⌜extr.EndsIn c₁⌝ -∗ ⌜atr.EndsIn δ₁⌝ -∗ ⌜ζ = ζ'⌝ -∗ stateInterp extr atr ={E₂}=∗
      ∃ (Q R : IProp GF),
        stateInterp extr atr ∗
        (∀ c₂ δ₂ ℓ, ∃ δ',
          stateInterp (extr :tr[some ζ']: c₂) (atr :tr[ℓ]: δ₂) ∗ Q ={E₂}=∗
          stateInterp (extr :tr[some ζ']: c₂) (atr :tr[stutteringLabel GF]: δ') ∗ R) ∗
        (stateInterp extr atr ={E₂}=∗ stateInterp extr atr ∗ Q) ∗
        WP e @ s; ζ; E₂ {{ v, R ={E₂,E₁}=∗ Φ v }}) ⊢
    WP e @ s; ζ; E₁ {{ Φ }} := by
  iintro H
  iloeb as IH
  ieval (simp only [wp_unfold.to_eq])
  simp only [wp.pre, He]
  iintro %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hloc %Hends Hσ
  icombine H Hσ as HR
  ihave Hkeep := fupd_keep_plain_sep (E' := ∅)
    (P := iprop(⌜reducibleIfNotStuck s e σ₁⌝ : IProp GF)) $$ [] HR
  · iintro ⟨H, Hσ⟩
    imod H
    imod H $$ %extr %atr %_ %atr.last %ζ %Hends %rfl %rfl Hσ with ⟨%Q, %R, Hσ, -, -, H⟩
    ieval (simp only [wp_unfold.to_eq]) at H
    isimp only [wp.pre, He] at H
    imod H $$ %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hloc %Hends Hσ with ⟨%Hred, -⟩
    imodintro
    ipureintro
    exact Hred
  imod Hkeep with ⟨%Hred, H, Hσ⟩
  imod fupd_mask_subseteq (E1 := E₁) (E2 := ∅) LawfulSet.empty_subset with Hmsk
  imodintro
  isplit
  · ipureintro
    exact Hred
  iintro %e₂ %σ₂ %efs %Hstep
  rcases hat.stutteringatomic Hstep with ⟨rfl, rfl, rfl⟩ | Hs
  · dsimp only [step_fupdN]
    imodintro
    inext
    have Hls : LocaleStep (tp1 ++ fill K e₂ :: tp2, σ₂) (some ζ)
        (tp1 ++ fill K e₂ :: tp2, σ₂) := by
      simpa using localeStep_fill (tp2 := tp2) Hloc Hstep
    imod allowsStuttering extr atr _ atr.last (some ζ) Hvalid Hends rfl Hls $$ Hσ with Hσ
    imodintro
    iapply step_fupdN_intro LawfulSet.subset_refl
    inext
    imod Hmsk with -
    imodintro
    iexists atr.last, stutteringLabel GF
    simp only [List.append_nil]
    iframe Hσ
    isplitl
    · iapply IH $$ H
    · iempintro
  · iclear IH
    dsimp only [step_fupdN]
    imod Hmsk with -
    imod H
    imod H $$ %extr %atr %_ %atr.last %ζ %Hends %rfl %rfl Hσ with
      ⟨%Q, %R, Hσ, Hupdate, Htrans, H⟩
    ieval (simp only [wp_unfold.to_eq]) at H
    isimp only [wp.pre, He] at H
    imod Htrans $$ Hσ with ⟨Hσ, HQ⟩
    imod H $$ %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hloc %Hends Hσ with ⟨-, H⟩
    dsimp only [step_fupdN]
    imod H $$ %e₂ %σ₂ %efs %Hstep with H
    iintro !> !>
    imod H
    imodintro
    iapply step_fupdN_wand $$ H
    iintro H
    imod H with ⟨%δ₃, %ℓ, Hσ, H, Hefs⟩
    icases Hupdate $$ %(tp1 ++ fill K e₂ :: (tp2 ++ efs), σ₂) %δ₃ %ℓ with ⟨%δ', Hupdate⟩
    imod Hupdate $$ [HQ Hσ] with ⟨Hσ, HR⟩
    · iframe
    imod wp_atomic_step_close (E₁ := E₁) Hs (validExec_extend_fill Hvalid Hloc Hends Hstep) rfl
      (localeOf_fill_step Hloc Hstep) $$ Hσ H [HR] with ⟨Hσ, H⟩
    · iintro %v HΦ
      iapply HΦ $$ HR
    imodintro
    iexists δ', stutteringLabel GF
    iframe

open Language (StutteringAtomic Atomic) in
@[rocq_alias trillium.wp_atomic]
theorem wp_atomic
    [hat : Atomic (State := State) (Iris.ProgramLogic.Language.Atomicity.ofStuckness s) e] :
    (|={E₁,E₂}=> WP e @ s; ζ; E₂ {{ v, |={E₂,E₁}=> Φ v }}) ⊢ WP e @ s; ζ; E₁ {{ Φ }} := by
  simp only [wp_unfold.to_eq]
  match He : toVal e with
  | some v =>
    simp only [wp.pre, He]
    iintro H
    imod H
    imod H
    imod H
    imodintro
    iexact H
  | none =>
    simp only [wp.pre, He]
    iintro H %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hloc %Hends Hσ
    imod H
    imod H $$ %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hloc %Hends Hσ with ⟨%Hred, H⟩
    imodintro
    isplit
    · ipureintro
      exact Hred
    iintro %e₂ %σ₂ %efs %Hstep
    dsimp only [step_fupdN]
    imod H $$ %e₂ %σ₂ %efs %Hstep with H
    iintro !> !>
    imod H
    imodintro
    iapply step_fupdN_wand $$ H
    iintro H
    imod H with ⟨%δ₂, %ℓ, Hσ, H, Hefs⟩
    imod wp_atomic_step_close (E₁ := E₁) (hat.atomic Hstep)
      (validExec_extend_fill Hvalid Hloc Hends Hstep) rfl
      (localeOf_fill_step Hloc Hstep) $$ Hσ H [] with ⟨Hσ, H⟩
    · iintro %v HΦ
      iexact HΦ
    imodintro
    iexists δ₂, ℓ
    iframe

open Language (StutteringAtomic Atomic) in
@[rocq_alias trillium.wp_atomic_take_step]
theorem wp_atomic_take_step
    [hat : Atomic (State := State) (Iris.ProgramLogic.Language.Atomicity.ofStuckness s) e]
    (He : toVal e = none) :
    (|={E₁,E₂}=> ∀ (extr : ExecutionTrace Expr) (atr : AuxiliaryTrace M) c₁ δ₁ ζ',
      ⌜extr.EndsIn c₁⌝ -∗ ⌜atr.EndsIn δ₁⌝ -∗ ⌜ζ = ζ'⌝ -∗ stateInterp extr atr ={E₂}=∗
      ∃ (Q R : IProp GF),
        stateInterp extr atr ∗
        (∀ c₂ δ₂ ℓ, ∃ δ' ℓ',
          stateInterp (extr :tr[some ζ']: c₂) (atr :tr[ℓ]: δ₂) ∗ Q ={E₂}=∗
          stateInterp (extr :tr[some ζ']: c₂) (atr :tr[ℓ']: δ') ∗ R) ∗
        (stateInterp extr atr ={E₂}=∗ stateInterp extr atr ∗ Q) ∗
        WP e @ s; ζ; E₂ {{ v, R ={E₂,E₁}=∗ Φ v }}) ⊢
    WP e @ s; ζ; E₁ {{ Φ }} := by
  iintro H
  ieval (simp only [wp_unfold.to_eq])
  ieval (simp only [wp.pre, He])
  iintro %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hloc %Hends Hσ
  imod H
  imod H $$ %extr %atr %_ %atr.last %ζ %Hends %rfl %rfl Hσ with
    ⟨%Q, %R, Hσ, Hupdate, Htrans, H⟩
  ieval (simp only [wp_unfold.to_eq]) at H
  isimp only [wp.pre, He] at H
  imod Htrans $$ Hσ with ⟨Hσ, HQ⟩
  imod H $$ %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hloc %Hends Hσ with ⟨%Hred, H⟩
  imodintro
  isplit
  · ipureintro
    exact Hred
  iintro %e₂ %σ₂ %efs %Hstep
  dsimp only [step_fupdN]
  imod H $$ %e₂ %σ₂ %efs %Hstep with H
  iintro !> !>
  imod H
  imodintro
  iapply step_fupdN_wand $$ H
  iintro H
  imod H with ⟨%δ₃, %ℓ, Hσ, H, Hefs⟩
  icases Hupdate $$ %(tp1 ++ fill K e₂ :: (tp2 ++ efs), σ₂) %δ₃ %ℓ with ⟨%δ', %ℓ', Hupdate⟩
  imod Hupdate $$ [HQ Hσ] with ⟨Hσ, HR⟩
  · iframe
  imod wp_atomic_step_close (E₁ := E₁) (hat.atomic Hstep)
    (validExec_extend_fill Hvalid Hloc Hends Hstep) rfl
    (localeOf_fill_step Hloc Hstep) $$ Hσ H [HR] with ⟨Hσ, H⟩
  · iintro %v HΦ
    iapply HΦ $$ HR
  imodintro
  iexists δ', ℓ'
  iframe

end wp_atomic

section wp_step

variable {s : Stuckness} {E E₁ E₂ : CoPset} {ζ : Locale} {e : Expr} {Φ : Val → IProp GF}
variable {P : IProp GF}

/-- In this stronger version of `wp_step_fupdN`, the masks in the step-taking fancy update are
a bit weird and somewhat difficult to use in practice. -/
@[rocq_alias trillium.wp_step_fupdN_strong]
theorem wp_step_fupdN_strong {n : Nat} (He : toVal e = none) (HE : E₂ ⊆ E₁) :
    (∀ (extr : ExecutionTrace Expr) (atr : AuxiliaryTrace M),
      stateInterp extr atr ={E₁,∅}=∗ ⌜n ≤ extr.length + 1⌝) ∧
    ((|={E₁,E₂}=> |={∅}▷=>^[n] |={E₂,E₁}=> P) ∗
      WP e @ s; ζ; E₂ {{ v, P ={E₁}=∗ Φ v }}) ⊢
    WP e @ s; ζ; E₁ {{ Φ }} := by
  match n with
  | 0 =>
    iintro ⟨-, Hp, Hwp⟩
    iapply wp_strong_mono (Std.IsPreorder.le_refl s) HE $$ Hwp
    iintro %v H
    dsimp only [step_fupdN]
    imod Hp
    imod Hp
    iapply H $$ Hp
  | n + 1 =>
    simp only [wp_unfold.to_eq]
    simp only [wp.pre, He]
    iintro H %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hloc %Hends Hσ
    by_cases Hn : n ≤ extr.length
    · icases H with ⟨-, Hp, Hwp⟩
      imod Hp
      dsimp only [step_fupdN]
      imod Hwp $$ %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hloc %Hends Hσ with ⟨$, H⟩
      iintro !> %e₂ %σ₂ %efs %Hstep
      icases H $$ %_ %_ %_ %Hstep with H
      imod H
      imod Hp
      iintro !> !>
      imod H
      imod Hp
      imodintro
      generalize extr.length = n0 at *
      induction n generalizing n0 with
      | zero =>
        iapply step_fupdN_wand $$ H
        iintro >⟨%δ₂, %ℓ, Hσ, Hwp, Hefs⟩
        dsimp only [step_fupdN]
        imod Hp
        imodintro
        iexists δ₂, ℓ
        iframe Hσ Hefs
        iapply wp_strong_mono (Std.IsPreorder.le_refl s) HE $$ Hwp
        iintro %v HΦ
        iapply HΦ $$ Hp
      | succ n IH =>
        obtain ⟨n0, rfl⟩ : ∃ n0', n0 = n0' + 1 := by cases n0 <;> grind
        dsimp only [step_fupdN]
        imod Hp
        imod H
        imodintro
        imodintro
        imod Hp
        imod H
        imodintro
        unfold ProofMode.Entails' at IH
        iapply IH n0 (Nat.le_of_succ_le_succ Hn) $$ [$]
    · icases H with ⟨Hlen, -⟩
      imod Hlen $$ %extr %atr Hσ with %h
      grind only

@[rocq_alias trillium.wp_step_fupdN]
theorem wp_step_fupdN {n : Nat} (He : toVal e = none) (HE : E₂ ⊆ E₁) :
    (∀ (extr : ExecutionTrace Expr) (atr : AuxiliaryTrace M),
      stateInterp extr atr ={E₁,∅}=∗ ⌜n ≤ extr.length + 1⌝) ∧
    ((|={E₁ \ E₂,∅}=> |={∅}▷=>^[n] |={∅,E₁ \ E₂}=> P) ∗
      WP e @ s; ζ; E₂ {{ v, P ={E₁}=∗ Φ v }}) ⊢
    WP e @ s; ζ; E₁ {{ Φ }} := by
  iintro H
  iapply wp_step_fupdN_strong (s := s) (P := P) (n := n) He HE $$ [H]
  iapply BI.and_mono_right $$ H
  iintro ⟨HP, $⟩
  imod fupd_mask_subseteq_emptyset_difference
    (show E₁ \ E₂ ⊆ E₁ from LawfulSet.diff_subset_left) with G
  imod HP
  imod G with -
  rw [show E₁ \ (E₁ \ E₂) = E₂ from LawfulSet.diff_self_diff_of_subset HE]
  imodintro
  iapply step_fupdN_wand $$ HP
  iintro H
  iapply fupd_mask_frame LawfulSet.empty_subset
  imod H
  imodintro
  simp [LawfulSet.diff_empty, ← LawfulSet.diff_subset_decomp HE]
  itrivial

@[rocq_alias trillium.wp_step_fupd]
theorem wp_step_fupd (He : toVal e = none) (HE : E₂ ⊆ E₁) :
    ⊢ (|={E₁}[E₂]▷=> P) -∗ WP e @ s; ζ; E₂ {{ v, P ={E₁}=∗ Φ v }} -∗ WP e @ s; ζ; E₁ {{ Φ }} := by
  iintro HR H
  iapply wp_step_fupdN_strong (n := 1) (P := P) He HE $$ [-]
  iframe H
  isplit
  · iintro %extr %atr Hσ
    iapply fupd_mask_intro_discard LawfulSet.empty_subset
    ipureintro
    omega
  · imod HR
    dsimp only [step_fupdN]
    iframe

end wp_step

section wp_preStep

variable {s : Stuckness} {E : CoPset} {ζ : Locale} {e : Expr} {Φ : Val → IProp GF}

@[rocq_alias trillium.pre_step_wp_pre_step]
theorem preStep_wp_preStep :
    (|~{E}~| WP e @ s; ζ; E {{ v, |~{E}~| Φ v }}) ⊢ WP e @ s; ζ; E {{ Φ }} := by
  clear preStep_wp_preStep
  iintro H
  iloeb as IH generalizing %e
  ieval (rewrite [wp_unfold.to_eq])
  match He : toVal e with
  | some v =>
    ieval (rewrite [wp_unfold.to_eq]) at H
    isimp only [wp.pre, He] at H
    simp only [wp.pre, He]
    imod H
    imod H
    imod H
    imodintro
    iexact H
  | none =>
    simp only [wp.pre, He]
    iintro %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hloc %Hends Hσ
    imod preStep_elim _ _ $$ Hσ H with ⟨Hσ, H⟩
    ieval (rewrite [wp_unfold.to_eq]) at H
    isimp only [wp.pre, He] at H
    imod H $$ %extr %atr %K %tp1 %tp2 %σ₁ %Hvalid %Hloc %Hends Hσ with ⟨%Hred, H⟩
    imodintro
    isplit
    · ipureintro
      exact Hred
    iintro %e₂ %σ₂ %efs %Hstep
    dsimp only [step_fupdN]
    imod H $$ %e₂ %σ₂ %efs %Hstep with H
    iintro !> !>
    imod H
    imodintro
    iapply step_fupdN_wand $$ H
    iintro H
    imod H with ⟨%δ₂, %ℓ, Hσ, Hwp, Hefs⟩
    imodintro
    iexists δ₂, ℓ
    iframe Hσ Hefs
    iapply IH
    iapply preStep_intro $$ Hwp

@[rocq_alias trillium.pre_step_wp]
theorem preStep_wp : (|~{E}~| WP e @ s; ζ; E {{ v, Φ v }}) ⊢ WP e @ s; ζ; E {{ Φ }} := by
  iintro H
  iapply preStep_wp_preStep
  imodintro
  iapply wp_strong_mono (Std.IsPreorder.le_refl s) LawfulSet.subset_refl $$ H
  iintro %v H !>
  iapply preStep_intro $$ H

@[rocq_alias trillium.wp_pre_step]
theorem wp_preStep : WP e @ s; ζ; E {{ v, |~{E}~| Φ v }} ⊢ WP e @ s; ζ; E {{ Φ }} := by
  iintro H
  iapply preStep_wp_preStep
  iapply preStep_intro $$ H

end wp_preStep

@[rocq_alias trillium.wp_bind]
theorem wp_bind (K : Ectx) {s : Stuckness} {E : CoPset} {ζ : Locale} {e : Expr}
    {Φ : Val → IProp GF} :
    WP e @ s; ζ; E {{ v, WP (fill K (ToVal.ofVal (Expr := Expr) v)) @ s; ζ; E {{ Φ }} }} ⊢
    WP (fill K e) @ s; ζ; E {{ Φ }} := by
  clear wp_bind
  iintro H
  iloeb as IH generalizing %e
  match He : toVal e with
  | some v =>
    obtain rfl := ToVal.coe_of_toVal_eq_some He
    ieval (rewrite [wp_unfold.to_eq]) at H
    isimp only [wp.pre, He] at H
    iapply preStep_wp $$ H
  | none =>
    ieval (rewrite [wp_unfold.to_eq])
    ieval (rewrite [wp_unfold.to_eq]) at H
    isimp only [wp.pre, He] at H
    simp only [wp.pre, Language.fill_not_val K He]
    iintro %extr %atr %K' %tp1 %tp2 %σ₁ %Hvalid %Hloc %Hends Hσ
    imod H $$ %extr %atr %(EvContextOps.comp K' K) %tp1 %tp2 %σ₁ %Hvalid
      %(by rw [Language.ectx_comp_comp]; exact Hloc)
      %(by rw [Language.ectx_comp_comp]; exact Hends) Hσ with ⟨%Hred, H⟩
    imodintro
    isplit
    · ipureintro
      cases s with
      | NotStuck => exact Language.reducible_fill K Hred
      | MaybeStuck => trivial
    iintro %e₂ %σ₂ %efs %Hstep
    obtain ⟨e₂', rfl, Hstep'⟩ := Language.fill_step_inv K He Hstep
    dsimp only [step_fupdN]
    imod H $$ %e₂' %σ₂ %efs %Hstep' with H
    iintro !> !>
    imod H
    imodintro
    iapply step_fupdN_wand $$ H
    iintro H
    imod H with ⟨%δ₂, %ℓ, Hσ, Hwp, Hefs⟩
    isimp only [Language.ectx_comp_comp] at Hσ Hefs
    imodintro
    iexists δ₂, ℓ
    iframe Hσ Hefs
    iapply IH $$ Hwp

/-! ## Derived rules -/

section derived

variable {s s₁ s₂ : Stuckness} {E E₁ E₂ : CoPset} {ζ : Locale} {e : Expr} {v : Val}
variable {Φ Ψ : Val → IProp GF} {R Q : IProp GF}

@[rocq_alias trillium.wp_mono]
theorem wp_mono (HΦ : ∀ v, Φ v ⊢ Ψ v) : WP e @ s; ζ; E {{ Φ }} ⊢ WP e @ s; ζ; E {{ Ψ }} := by
  iintro H
  iapply wp_strong_mono (Std.IsPreorder.le_refl s) LawfulSet.subset_refl $$ H
  iintro %v HΦ' !>
  iapply HΦ $$ HΦ'

@[rocq_alias trillium.wp_stuck_mono]
theorem wp_stuck_mono (hs : s₁ ≤ s₂) : WP e @ s₁; ζ; E {{ Φ }} ⊢ WP e @ s₂; ζ; E {{ Φ }} := by
  iintro H
  iapply wp_strong_mono hs LawfulSet.subset_refl $$ H
  iintro %v HΦ
  iframe HΦ

@[rocq_alias trillium.wp_stuck_weaken]
theorem wp_stuck_weaken : WP e @ s; ζ; E {{ Φ }} ⊢ WP e @[ζ] E ? {{ Φ }} :=
  wp_stuck_mono Stuckness.le_MaybeStuck

@[rocq_alias trillium.wp_mask_mono]
theorem wp_mask_mono (hE : E₁ ⊆ E₂) : WP e @ s; ζ; E₁ {{ Φ }} ⊢ WP e @ s; ζ; E₂ {{ Φ }} := by
  iintro H
  iapply wp_strong_mono (Std.IsPreorder.le_refl s) hE $$ H
  iintro %v HΦ
  iframe HΦ

#rocq_ignore trillium.wp_mono' "Rocq `Proper` instance; use `wp_mono`"
#rocq_ignore trillium.wp_flip_mono' "Rocq `Proper` instance; use `wp_mono`"

@[rocq_alias trillium.wp_value]
theorem wp_value [h : Language.IntoVal e v] : Φ v ⊢ WP e @ s; ζ; E {{ Φ }} :=
  h.into_val ▸ wp_value'

@[rocq_alias trillium.wp_value_fupd']
theorem wp_value_fupd' : (|={E}=> Φ v) ⊢ WP (v : Expr) @ s; ζ; E {{ Φ }} :=
  (wp_value' (Φ := fun v => iprop(|={E}=> Φ v))).trans wp_fupd

@[rocq_alias trillium.wp_value_fupd]
theorem wp_value_fupd [h : Language.IntoVal e v] : (|={E}=> Φ v) ⊢ WP e @ s; ζ; E {{ Φ }} :=
  h.into_val ▸ wp_value_fupd'

@[rocq_alias trillium.wp_value_inv]
theorem wp_value_inv [h : Language.IntoVal e v] : WP e @ s; ζ; E {{ Φ }} ⊢ |~{E}~| Φ v :=
  h.into_val ▸ wp_value_inv'

@[rocq_alias trillium.wp_frame_l]
theorem wp_frame_l : R ∗ WP e @ s; ζ; E {{ Φ }} ⊢ WP e @ s; ζ; E {{ v, R ∗ Φ v }} := by
  iintro ⟨HR, H⟩
  iapply wp_strong_mono (Std.IsPreorder.le_refl s) LawfulSet.subset_refl $$ H
  iintro %v HΦ !>
  iframe

@[rocq_alias trillium.wp_frame_r]
theorem wp_frame_r : WP e @ s; ζ; E {{ Φ }} ∗ R ⊢ WP e @ s; ζ; E {{ v, Φ v ∗ R }} := by
  iintro ⟨H, HR⟩
  iapply wp_strong_mono (Std.IsPreorder.le_refl s) LawfulSet.subset_refl $$ H
  iintro %v HΦ !>
  iframe

@[rocq_alias trillium.wp_frame_step_l]
theorem wp_frame_step_l (He : toVal e = none) (HE : E₂ ⊆ E₁) :
    (|={E₁}[E₂]▷=> R) ∗ WP e @ s; ζ; E₂ {{ Φ }} ⊢ WP e @ s; ζ; E₁ {{ v, R ∗ Φ v }} := by
  iintro ⟨Hu, Hwp⟩
  iapply wp_step_fupd He HE $$ Hu
  iapply wp_mono $$ Hwp
  iintro %v HΦ HR !>
  iframe

@[rocq_alias trillium.wp_frame_step_r]
theorem wp_frame_step_r (He : toVal e = none) (HE : E₂ ⊆ E₁) :
    WP e @ s; ζ; E₂ {{ Φ }} ∗ (|={E₁}[E₂]▷=> R) ⊢ WP e @ s; ζ; E₁ {{ v, Φ v ∗ R }} :=
  BI.sep_comm.1.trans <| (wp_frame_step_l He HE).trans <| wp_mono fun _ => BI.sep_comm.1

@[rocq_alias trillium.wp_frame_step_l']
theorem wp_frame_step_l' (He : toVal e = none) :
    ▷ R ∗ WP e @ s; ζ; E {{ Φ }} ⊢ WP e @ s; ζ; E {{ v, R ∗ Φ v }} := by
  iintro ⟨HR, Hwp⟩
  iapply wp_frame_step_l He LawfulSet.subset_refl
  iframe Hwp
  iapply step_fupd_intro LawfulSet.subset_refl $$ HR

@[rocq_alias trillium.wp_frame_step_r']
theorem wp_frame_step_r' (He : toVal e = none) :
    WP e @ s; ζ; E {{ Φ }} ∗ ▷ R ⊢ WP e @ s; ζ; E {{ v, Φ v ∗ R }} :=
  BI.sep_comm.1.trans <| (wp_frame_step_l' He).trans <| wp_mono fun _ => BI.sep_comm.1

@[rocq_alias trillium.wp_wand]
theorem wp_wand :
    ⊢ WP e @ s; ζ; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; ζ; E {{ Ψ }} := by
  iintro Hwp H
  iapply wp_strong_mono (Std.IsPreorder.le_refl s) LawfulSet.subset_refl $$ Hwp
  iintro %v HΦ !>
  iapply H $$ HΦ

@[rocq_alias trillium.wp_wand_l]
theorem wp_wand_l :
    (∀ v, Φ v -∗ Ψ v) ∗ WP e @ s; ζ; E {{ Φ }} ⊢ WP e @ s; ζ; E {{ Ψ }} := by
  iintro ⟨H, Hwp⟩
  iapply wp_wand $$ Hwp H

@[rocq_alias trillium.wp_wand_r]
theorem wp_wand_r :
    WP e @ s; ζ; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ s; ζ; E {{ Ψ }} := by
  iintro ⟨Hwp, H⟩
  iapply wp_wand $$ Hwp H

@[rocq_alias trillium.wp_frame_wand_l]
theorem wp_frame_wand_l :
    ⊢ Q ∗ WP e @ s; ζ; E {{ v, Q -∗ Φ v }} -∗ WP e @ s; ζ; E {{ Φ }} := by
  iintro ⟨HQ, Hwp⟩
  iapply wp_wand $$ Hwp
  iintro %v HΦ
  iapply HΦ $$ HQ

end derived

/-! ## Proof-mode instances -/

section proofmode_classes

variable {s : Stuckness} {E E₁ E₂ : CoPset} {ζ : Locale} {e : Expr}
variable {Φ Ψ : Val → IProp GF} {P R : IProp GF}

@[rocq_alias trillium.frame_wp]
instance frameWp {p : Bool} [H : ∀ v, FrameInstantiateExistDisabled p R (Φ v) (Ψ v)] :
    Frame p R (WP e @ s; ζ; E {{ Φ }}) (WP e @ s; ζ; E {{ Ψ }}) where
  frame := wp_frame_l.trans <| wp_mono fun v => (H v).frame_instantiatiate_exist_disabled.frame

@[rocq_alias trillium.is_except_0_wp]
instance isExcept0Wp : IsExcept0 (WP e @ s; ζ; E {{ Φ }}) where
  is_except0 :=
    calc iprop(◇ _)
      _ ⊢ ◇ |={E}=> _ := BI.except0_mono fupd_intro
      _ ⊢ |={E}=> _ := BIFUpdate.except0
      _ ⊢ WP e @ s; ζ; E {{ Φ }} := fupd_wp

@[rocq_alias trillium.elim_modal_fupd_wp]
instance (priority := default + 10) elimModalFupdWp p io :
    ElimModal True p io false iprop(|={E}=> P) P (WP e @ s; ζ; E {{ Φ }})
      (WP e @ s; ζ; E {{ Φ }}) where
  elim_modal := by
    iintro %_ ⟨H, G⟩
    icases BI.intuitionisticallyIf_elim $$ H with H
    iapply fupd_wp
    imod H
    imodintro
    iapply G $$ H

@[rocq_alias trillium.elim_modal_bupd_wp]
instance elimModalBupdWp p io :
    ElimModal True p io false iprop(|==> P) P (WP e @ s; ζ; E {{ Φ }})
      (WP e @ s; ζ; E {{ Φ }}) where
  elim_modal := by
    rintro ⟨⟩
    refine BI.sep_mono (BI.intuitionisticallyIf_mono
      (BIUpdateFUpdate.fupd_of_bupd (E := E))) .rfl |>.trans ?_
    exact (elimModalFupdWp _ (io := io)).elim_modal ⟨⟩

open Language (StutteringAtomic Atomic) in
@[ipm_backtrack, rocq_alias trillium.elim_modal_fupd_wp_stutteringatomic]
instance (priority := default + 1) elimModalFupdWpStutteringAtomic [AllowsStuttering M GF] p io :
    ElimModal (StutteringAtomic (State := State)
        (Iris.ProgramLogic.Language.Atomicity.ofStuckness s) e) p io false
      iprop(|={E₁,E₂}=> P) P (WP e @ s; ζ; E₁ {{ Φ }})
      (WP e @ s; ζ; E₂ {{ v, |={E₂,E₁}=> Φ v }}) where
  elim_modal := by
    rintro hat
    iintro ⟨H, G⟩
    icases BI.intuitionisticallyIf_elim $$ H with H
    iapply wp_stuttering_atomic
    imod H
    imodintro
    iapply G $$ H

@[rocq_alias trillium.add_modal_fupd_wp]
instance addModalFupdWp : AddModal iprop(|={E}=> P) P (WP e @ s; ζ; E {{ Φ }}) where
  add_modal := by
    iintro ⟨H1, H2⟩
    imod H1
    iapply H2 $$ H1

open Language (StutteringAtomic Atomic) in
@[ipm_backtrack, rocq_alias trillium.elim_acc_wp_stuttering]
instance (priority := low + 1) elimAcc_wp_stuttering [AllowsStuttering M GF] {X}
    (α β : X → IProp GF) (γ : X → Option (IProp GF)) :
    ElimAcc (StutteringAtomic (State := State)
        (Iris.ProgramLogic.Language.Atomicity.ofStuckness s) e)
      (fupd E₁ E₂) (fupd E₂ E₁) α β γ (WP e @ s; ζ; E₁ {{ Φ }})
      (fun x => WP e @ s; ζ; E₂ {{ v, |={E₂}=> β x ∗ (γ x -∗? Φ v) }}) where
  elim_acc := by
    dsimp only [accessor, BIBase.wandM, Option.getD]
    iintro %hat Hinner >⟨%x, Hα, Hclose⟩
    iapply wp_wand $$ [Hinner Hα]
    · iapply Hinner $$ Hα
    · iintro %v >⟨Hβ, HΦ⟩
      ispecialize Hclose $$ Hβ
      imod Hclose
      imodintro
      cases (γ x) with
      | none => iexact HΦ
      | some P => iapply HΦ $$ Hclose

open Language (StutteringAtomic Atomic) in
@[rocq_alias trillium.elim_modal_fupd_wp_atomic]
instance elimModalFupdWpAtomic p io :
    ElimModal (Atomic (State := State)
        (Iris.ProgramLogic.Language.Atomicity.ofStuckness s) e) p io false
      iprop(|={E₁,E₂}=> P) P (WP e @ s; ζ; E₁ {{ Φ }})
      (WP e @ s; ζ; E₂ {{ v, |={E₂,E₁}=> Φ v }}) where
  elim_modal := by
    rintro hat
    iintro ⟨H, G⟩
    icases BI.intuitionisticallyIf_elim $$ H with H
    iapply wp_atomic
    imod H
    imodintro
    iapply G $$ H

open Language (StutteringAtomic Atomic) in
@[rocq_alias trillium.elim_acc_wp_atomic]
instance (priority := low) elimAcc_wp_atomic {X} (α β : X → IProp GF)
    (γ : X → Option (IProp GF)) :
    ElimAcc (Atomic (State := State) (Iris.ProgramLogic.Language.Atomicity.ofStuckness s) e)
      (fupd E₁ E₂) (fupd E₂ E₁) α β γ (WP e @ s; ζ; E₁ {{ Φ }})
      (fun x => WP e @ s; ζ; E₂ {{ v, |={E₂}=> β x ∗ (γ x -∗? Φ v) }}) where
  elim_acc := by
    dsimp only [accessor, BIBase.wandM, Option.getD]
    iintro %hat Hinner Hacc
    iapply wp_atomic
    imod Hacc with ⟨%x, Hα, Hclose⟩
    imodintro
    iapply wp_wand $$ [Hinner Hα]
    · iapply Hinner $$ Hα
    · iintro %v H
      imod H with ⟨Hβ, HΦ⟩
      ispecialize Hclose $$ Hβ
      imod Hclose
      imodintro
      cases (γ x) with
      | none => iexact HΦ
      | some P => iapply HΦ $$ Hclose

@[rocq_alias trillium.elim_acc_wp_nonatomic]
instance elimAcc_wp_nonatomic {X} (α β : X → IProp GF) (γ : X → Option (IProp GF)) :
    ElimAcc True (fupd E E) (fupd E E) α β γ (WP e @ s; ζ; E {{ Φ }})
      (fun x => WP e @ s; ζ; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }}) where
  elim_acc := by
    dsimp only [accessor, BIBase.wandM, Option.getD]
    iintro %_ Hinner >⟨%x, Hα, Hclose⟩
    iapply wp_fupd
    iapply wp_wand $$ [Hinner Hα]
    · iapply Hinner $$ Hα
    · iintro %v >⟨Hβ, HΦ⟩
      ispecialize Hclose $$ Hβ
      imod Hclose
      imodintro
      cases (γ x) with
      | none => iexact HΦ
      | some P => iapply HΦ $$ Hclose

@[rocq_alias trillium.elim_modal_pre_step_wp]
instance elimModalPreStepWp p io :
    ElimModal True p io false iprop(|~{E}~| P) P (WP e @ s; ζ; E {{ Φ }})
      (WP e @ s; ζ; E {{ v, Φ v }}) where
  elim_modal := by
    iintro %_ ⟨H, G⟩
    icases BI.intuitionisticallyIf_elim $$ H with H
    iapply preStep_wp
    imod H
    imodintro
    iapply G $$ H

end proofmode_classes

end Trillium
