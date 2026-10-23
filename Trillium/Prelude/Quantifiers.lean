/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Iris.Std.RocqPorting
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Monotone.Basic
import Trillium.Prelude.Sigma

/-!
# Cardinality, regularity and swapping quantifiers

Port of `trillium/prelude/quantifiers.v`.

`SmallerCard A B` says that there is no injection `B → A`. A preorder `R` on `A` is *regular* if
every cofinal subset of `A` admits an injection from `A`. For regular total preorders, a union of
fewer than `|A|` non-cofinal subsets is non-cofinal, which yields `forall_exists_swap`: if
`P x y` is antitone in `x` and `B` is smaller than `A`, then `∀ x, ∃ y, P x y` implies
`∃ y, ∀ x, P x y`. It is used (with `A = ℕ`, see `nat_regular`) to extract existentials from
step-indexed propositions (`Trillium.Prelude.IrisExtraction`).

Rocq's `injective` is Mathlib's `Function.Injective`; subsets `subset := A → Prop` are plain
predicates `A → Prop` and `subset_type S := sig S` is `Subtype S`.
-/

namespace Trillium

attribute [rocq_alias trillium.injective] Function.Injective

/-- Rocq `injective_compose f g : injective f → injective g → injective (g ∘ f)` is
`Function.Injective.comp` (with the hypotheses in the opposite order). -/
@[rocq_alias trillium.injective_compose]
theorem injective_compose {A B C : Sort _} (f : A → B) (g : B → C) :
    Function.Injective f → Function.Injective g → Function.Injective (fun x => g (f x)) :=
  fun Hf Hg => Hg.comp Hf

/-- `A` has strictly smaller cardinality than `B`: there is no injection from `B` into `A`. -/
@[rocq_alias trillium.smaller_card]
def SmallerCard (A B : Sort _) : Prop := ∀ f : B → A, ¬ Function.Injective f

#rocq_ignore trillium.subset "type abbreviation for `A → Prop`; predicates `A → Prop` are used directly"
#rocq_ignore trillium.subset_type "`sig S`; Lean's `Subtype S` is used directly"

section quantifiers

variable {A : Type _} (R : A → A → Prop)

/-- `S` is cofinal for `R`: above every element there is an element of `S`. -/
@[rocq_alias trillium.cofinal]
def Cofinal (S : A → Prop) : Prop := ∀ x, ∃ y, S y ∧ R x y

/-- `R` is regular: every cofinal subset admits an injection from the whole of `A`. -/
@[rocq_alias trillium.regular]
def Regular : Prop := ∀ S : A → Prop, Cofinal R S → ∃ f : A → Subtype S, Function.Injective f

variable {R}

@[rocq_alias trillium.not_cofinal_smaller]
theorem not_cofinal_smaller {S : A → Prop} (Hncf : ¬ Cofinal R S) :
    ∃ x, ∀ y, S y → ¬ R x y := by
  obtain ⟨x, Hncf⟩ := Classical.not_forall.mp Hncf
  exact ⟨x, fun y Hy HR => Hncf ⟨y, Hy, HR⟩⟩

/-- The union of a family of subsets. -/
@[rocq_alias trillium.union]
def union {I : Sort _} (fam : I → A → Prop) : A → Prop := fun x => ∃ i, fam i x

@[rocq_alias trillium.regular_union_of_smaller]
theorem regular_union_of_smaller (Htotal : ∀ x y, R x y ∨ R y x)
    (Htrans : ∀ x y z, R x y → R y z → R x z) (I : Type _) (fam : I → A → Prop) :
    Regular R → SmallerCard I A → (∀ i, ¬ Cofinal R (fam i)) → ¬ Cofinal R (union fam) := by
  intro Hreg HI Hfam Hcnf
  have Hmax : ∀ i, ∃ x, ∀ y, fam i y → ¬ R x y := fun i => not_cofinal_smaller (Hfam i)
  choose g Hg using Hmax
  let Img : A → Prop := fun x => ∃ i, g i = x
  have Himgback : ∀ x : Subtype Img, ∃ i : I, x.1 = g i := fun ⟨_, i, Hi⟩ => ⟨i, Hi.symm⟩
  choose h Hh using Himgback
  have Hinj : Function.Injective h := by
    intro x y Hxy
    apply Subtype.ext
    rw [Hh x, Hh y, Hxy]
  have Himgncnf : ¬ Cofinal R Img := by
    intro Himgcnf
    obtain ⟨h', Hh'⟩ := Hreg _ Himgcnf
    exact HI (fun x => h (h' x)) (injective_compose _ _ Hh' Hinj)
  obtain ⟨z, Hz⟩ := not_cofinal_smaller Himgncnf
  obtain ⟨u, ⟨i, Hu1⟩, Hu2⟩ := Hcnf z
  have Hzgi : R z (g i) := by
    have := Hg i _ Hu1
    rcases Htotal (g i) u with H | H
    · exact absurd H this
    · exact Htrans _ _ _ Hu2 H
  exact Hz _ ⟨i, rfl⟩ Hzgi

@[rocq_alias trillium.regular_union_biger]
theorem regular_union_biger (Htotal : ∀ x y, R x y ∨ R y x)
    (Htrans : ∀ x y z, R x y → R y z → R x z) (I : Type _) (fam : I → A → Prop) :
    Regular R → SmallerCard I A → Cofinal R (union fam) → ∃ i, Cofinal R (fam i) := by
  intro Hreg HI Hcnf
  suffices H : ∃ i, ¬ ¬ Cofinal R (fam i) by
    obtain ⟨i, Hi⟩ := H
    exact ⟨i, Classical.not_not.mp Hi⟩
  refine Classical.not_forall.mp fun Hfam => ?_
  exact regular_union_of_smaller Htotal Htrans I fam Hreg HI Hfam Hcnf

variable {B : Type _} (P : A → B → Prop)

/-- The fiber of `P` over `b`. -/
@[rocq_alias trillium.fiber]
def fiber (b : B) : A → Prop := fun x => P x b

variable {P}

@[rocq_alias trillium.cofinal_fiber_forall]
theorem cofinal_fiber_forall (Hmono : ∀ x y z, R x y → P y z → P x z) (b : B) :
    Cofinal R (fiber P b) → ∀ x, P x b := by
  intro Hb x
  obtain ⟨y, Hy1, Hy2⟩ := Hb x
  exact Hmono _ _ _ Hy2 Hy1

@[rocq_alias trillium.forall_exists_swap]
theorem forall_exists_swap (Htotal : ∀ x y, R x y ∨ R y x)
    (Htrans : ∀ x y z, R x y → R y z → R x z) (Hmono : ∀ x y z, R x y → P y z → P x z)
    (Hrefl : ∀ x, R x x) :
    Regular R → SmallerCard B A → (∀ x : A, ∃ y : B, P x y) → ∃ y, ∀ x, P x y := by
  intro Hreg HB Hfe
  obtain ⟨y, Hy⟩ := regular_union_biger Htotal Htrans B (fiber P) Hreg HB (by
    intro x
    obtain ⟨y, Hy⟩ := Hfe x
    exact ⟨x, ⟨y, Hy⟩, Hrefl x⟩)
  exact ⟨y, cofinal_fiber_forall Hmono y Hy⟩

end quantifiers

/-- `≤` on `ℕ` is regular. -/
@[rocq_alias trillium.nat_regular]
theorem nat_regular : Regular (· ≤ · : ℕ → ℕ → Prop) := by
  intro St HS
  choose f Hf using HS
  let g : ℕ → ℕ := fun n => Nat.rec (f 0) (fun _ gn => f (gn + 1)) n
  have Hg : ∀ n, St (g n) := fun n => by cases n <;> exact (Hf _).1
  have Hglt : StrictMono g := strictMono_nat_of_lt_succ fun n => (Hf (g n + 1)).2
  exact ⟨fun n => ⟨g n, Hg n⟩, fun x y Hxy => Hglt.injective (congrArg Subtype.val Hxy)⟩

end Trillium
