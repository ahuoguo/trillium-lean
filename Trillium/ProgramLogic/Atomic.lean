/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Iris.BI.Lib.Atomic
import Iris.Instances.Lib.Invariants
import Trillium.ProgramLogic.WeakestPre

/-!
# Logically atomic Hoare triples

Port of `trillium/program_logic/atomic.v`.

`atomic_wp e Eo ζ α β f` is the logically atomic triple for the thread with locale `ζ`, built from
iris-lean's atomic updates (`Iris.atomic_update`) and telescopes (`Iris.Std.Tele`). Unlike
iris-lean's (newer) `Iris.atomic_wp`, Trillium's version has no private postcondition and its
mask argument `Eo` is the outer mask of the atomic update itself (not its complement).

Notation: `<<{ ∀∀ x, α }>> e @ Eo; ζ <<{ ∃∃ y, β | RET v }>>` (the binder groups may be
omitted); it is distinguished from iris-lean's `<<{ … }>> e @ E <<{ … }>>` by the locale.

In Iris 4.3, `atomic_wp_seq` and `atomic_wp_seq_step` assume that the atomic precondition is
`Laterable`; the proofs here do not need this assumption, so it is dropped.
-/

namespace Trillium

open Iris Iris.BI Iris.Std Iris.ProofMode Language

section definition

variable {Expr Val Ectx State Locale : Type _} [Language Expr Val Ectx State Locale]
variable {M : Model} {GF : BundledGFunctors} [IrisG Expr M GF] {TA TB : Tele}

/-- A logically atomic triple for the thread `ζ`: `e` refines the atomic update from `α` to `β`
with outer mask `Eo` (the inner mask is hard-coded to be empty) and returns `f x y`. -/
@[rocq_alias trillium.atomic_wp]
def atomic_wp (e : Expr) (Eo : CoPset) (ζ : Locale) (α : TA.Arg → IProp GF)
    (β : TA.Arg → TB.Arg → IProp GF) (f : TA.Arg → TB.Arg → Val) : IProp GF :=
  iprop(∀ Φ, atomic_update Eo ∅ α β (λ.. x y, Φ (f x y)) -∗ WP e @[ζ] {{ Φ }})

end definition

/-! ## Notation -/

/-- `<<{ ∀∀ x, α }>> e @ Eo; ζ <<{ ∃∃ y, β | RET v }>>` is the logically atomic triple
`atomic_wp e Eo ζ α β f` over the telescopes bound by `∀∀ …` and `∃∃ …`. -/
syntax:max (name := trilliumAtomicWpNotation)
  ppGroup("<<{ " (auAllBinders)? term " }>>" ppSpace term:max " @ " term:max " ; " term:max
    ppSpace "<<{ " (auExBinders)? term " | " &"RET " term " }>>") : term

open Lean in
macro_rules
  | `(iprop(<<{%$tk $[$xs]? $α }>> $e @ $Eo ; $ζ <<{ $[$ys]? $β | RET $v }>>)) => do
    let xstx? := xs.map fun xs => (⟨xs.raw[1]⟩ : TSyntax ``Lean.explicitBinders)
    let ystx? := ys.map fun ys => (⟨ys.raw[1]⟩ : TSyntax ``Lean.explicitBinders)
    let TA ← Tele.expandLiteral xstx?
    let TB ← Tele.expandLiteral ystx?
    let α ← Tele.expandFun TA xstx? (← `(iprop($α)))
    let β ← Tele.expandFun TA xstx? (← Tele.expandFun TB ystx? (← `(iprop($β))))
    let f ← Tele.expandFun TA xstx? (← Tele.expandFun TB ystx? v)
    ``($(BI.wrapIprop tk ``atomic_wp) (TA := $TA) (TB := $TB) $e $Eo $ζ $α $β $f)

/-! ## Theory -/

section lemmas

variable {Expr Val Ectx State Locale : Type _} [Language Expr Val Ectx State Locale]
variable {M : Model} {GF : BundledGFunctors} [IrisG Expr M GF] {TA TB : Tele}
variable {e : Expr} {Eo : CoPset} {ζ : Locale}
variable {α : TA.Arg → IProp GF} {β : TA.Arg → TB.Arg → IProp GF} {f : TA.Arg → TB.Arg → Val}

@[rocq_alias trillium.atomic_wp_mask_weaken]
theorem atomic_wp_mask_weaken {Eo₁ Eo₂ : CoPset} (HE : Eo₂ ⊆ Eo₁) :
    atomic_wp e Eo₁ ζ α β f ⊢ atomic_wp e Eo₂ ζ α β f := by
  iunfold atomic_wp
  iintro Hwp %Φ AU
  iapply Hwp
  iapply atomic_update_mask_weaken HE $$ AU

/-- Atomic triples imply sequential triples. -/
@[rocq_alias trillium.atomic_wp_seq]
theorem atomic_wp_seq :
    atomic_wp e Eo ζ α β f ⊢
    ∀ Φ, ∀.. x, α x -∗ (∀.. y, β x y -∗ Φ (f x y)) -∗ WP e @[ζ] {{ Φ }} := by
  iunfold atomic_wp
  iintro Hwp %Φ %x Hα HΦ
  iapply wp_frame_wand_l (Q := iprop(∀.. y, β x y -∗ Φ (f x y)))
  isplitl [HΦ]
  · iexact HΦ
  iapply Hwp
  iauintro
  iaaccintro Hα
  · iintro $
  · iintro %y Hβ !>
    isimp only [Tele.app_bind]
    iintro HΦ
    iapply HΦ $$ Hβ

/-- This version matches the Texan triple, i.e., with a later in front of the
`(∀.. y, β x y -∗ Φ (f x y))`. -/
@[rocq_alias trillium.atomic_wp_seq_step]
theorem atomic_wp_seq_step (He : toVal e = none) :
    atomic_wp e Eo ζ α β f ⊢
    ∀ Φ, ∀.. x, α x -∗ ▷ (∀.. y, β x y -∗ Φ (f x y)) -∗ WP e @[ζ] {{ Φ }} := by
  iintro Hwp %Φ %x Hα HΦ
  iapply wp_step_fupd (P := iprop(∀.. y, β x y -∗ Φ (f x y))) He LawfulSet.subset_refl
    $$ [HΦ]
  · iapply step_fupd_intro LawfulSet.subset_refl $$ HΦ
  iapply atomic_wp_seq $$ Hwp %_ %x Hα
  iintro %y Hβ HΦ !>
  iapply HΦ $$ Hβ

/-- Sequential triples with the empty mask for a physically atomic `e` are atomic. -/
@[rocq_alias trillium.atomic_seq_wp_atomic]
theorem atomic_seq_wp_atomic [Atomic (State := State) .WeaklyAtomic e] :
    (∀ Φ, ∀.. x, α x -∗ (∀.. y, β x y -∗ Φ (f x y)) -∗ WP e @[ζ] ∅ {{ Φ }}) ⊢
    atomic_wp e Eo ζ α β f := by
  iunfold atomic_wp
  iintro Hwp %Φ AU
  imod AU with ⟨%x, Hα, -, Hclose⟩
  iapply Hwp $$ %_ %x Hα
  iintro %y Hβ
  imod Hclose $$ %y Hβ with HΦ
  isimp only [Tele.app_bind] at HΦ
  imodintro
  iexact HΦ

/-- Sequential triples with a persistent precondition and no initial quantifier are atomic. -/
@[rocq_alias trillium.persistent_seq_wp_atomic]
theorem persistent_seq_wp_atomic {α : Tele.Arg .nil → IProp GF}
    {β : Tele.Arg .nil → TB.Arg → IProp GF} {f : Tele.Arg .nil → TB.Arg → Val}
    [Persistent (α .nil)] :
    (∀ Φ, α .nil -∗ (∀.. y, β .nil y -∗ Φ (f .nil y)) -∗ WP e @[ζ] {{ Φ }}) ⊢
    atomic_wp e Eo ζ α β f := by
  iunfold atomic_wp
  iintro Hwp %Φ HΦ
  iapply fupd_wp
  imod HΦ with ⟨%⟨⟩, #Hα, Hclose, -⟩
  imod Hclose $$ Hα with HΦ
  iapply wp_fupd
  iapply Hwp $$ Hα
  iintro !> %y Hβ
  imod HΦ with ⟨%⟨⟩, -, -, Hclose⟩
  imod Hclose $$ Hβ with HΦ
  isimp only [Tele.lam, Tele.app, Tele.bind, Tele.app_bind] at HΦ
  imodintro
  iexact HΦ

/-- We can open invariants around atomic triples. -/
@[rocq_alias trillium.wp_atomic_inv]
theorem wp_atomic_inv {N : Namespace} {I : IProp GF} (HN : (↑N : CoPset) ⊆ Eo) :
    atomic_wp e Eo ζ (λ.. x, iprop(▷ I ∗ α x)) (λ.. x y, iprop(▷ I ∗ β x y)) f ⊢
    inv N I -∗ atomic_wp e (Eo \ ↑N) ζ α β f := by
  iunfold atomic_wp
  iintro Hwp #Hinv %Φ AU
  iapply Hwp
  iauintro
  iinv N with HI
  iapply aacc_aupd $$ AU
  · exact LawfulSet.subset_refl
  iintro %x Hα
  iaaccintro %x [HI Hα] <;> isimp only [Tele.app_bind]
  · iframe
  · iintro ⟨HI, $⟩
    iintro !> AU !>
    iframe
  · iintro %y H
    icases H with ⟨HI, Hβ⟩
    imodintro
    iright
    iexists y
    iintro {$Hβ} HΦ !>
    iframe HI HΦ

end lemmas

end Trillium
