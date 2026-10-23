/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.Fairness.UtilsLogic
import Trillium.Fairness.UtilsSets
import Trillium.Fairness.UtilsMaps
import Trillium.Fairness.UtilsRelations
import Mathlib.Algebra.Group.Nat.Even

/-!
# Miscellaneous utilities
Port of `fairness/utils.v`.

Representation decisions:
* Big operators are iris-lean's `bigOpS`/`bigOpM` over the generic `LawfulFiniteSet`/
  `LawfulFiniteMap` interfaces (which cover `GSet`/`GMap`); stdpp's `gset_to_gmap` is
  `FiniteMap.ofSet` there.
* stdpp's list disjointness `l1 ## l2` is Mathlib's `List.Disjoint`.
* Rocq's `Nat.even`/`Nat.odd : nat → bool` are `decide (Even n)`/`decide (Odd n)`; the
  lemmas using them as propositions use Mathlib's `Even n`/`Odd n`.
* The Ltac `add_case` is not ported.
-/

namespace Trillium.Fairness

open Iris Iris.Std Iris.Algebra

section Disjoint

@[rocq_alias trillium.fairness.disjoint_subseteq]
theorem disjoint_subseteq {S A : Type _} [LawfulSet S A] (X1 X2 Y1 Y2 : S) :
    X1 ⊆ Y1 → X2 ⊆ Y2 → Y1 ## Y2 → X1 ## X2 :=
  fun h1 h2 h x ⟨hx1, hx2⟩ => h x ⟨h1 x hx1, h2 x hx2⟩

end Disjoint

@[rocq_alias trillium.fairness.map_img_sets_split_helper]
theorem map_img_sets_split_helper {K A : Type _} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]
    [Ord A] [Std.TransOrd A] [Std.LawfulEqOrd A] (k : K) (m : GMap K (GSet A)) :
    flattenGSet (GMap.img m) = (m[k]?.getD ∅) ∪ flattenGSet (GMap.img (m.erase k)) := by
  ext a
  simp only [flattenGSet_spec, GMap.mem_img, LawfulSet.mem_union, GMap.getElem?_erase_ite]
  constructor
  · rintro ⟨s, ⟨k', hk'⟩, ha⟩
    by_cases h : k = k'
    · subst h; rw [hk']; exact .inl ha
    · exact .inr ⟨s, ⟨k', by simp [h, hk']⟩, ha⟩
  · rintro (ha | ⟨s, ⟨k', hk'⟩, ha⟩)
    · cases hk : m[k]? with
      | none => rw [hk] at ha; exact absurd ha LawfulSet.mem_empty
      | some s => rw [hk] at ha; exact ⟨s, ⟨k, hk⟩, ha⟩
    · by_cases h : k = k'
      · simp [h] at hk'
      · simp only [h, ite_false] at hk'; exact ⟨s, ⟨k', hk'⟩, ha⟩

#rocq_ignore trillium.fairness.big_opMS
  "Relates `big_opS` on a `gset` to `big_opM` on its underlying `mapset` (stdpp implementation detail); `GSet` is not a `mapset` in Lean"

attribute [rocq_alias trillium.fairness.gset_to_gmap_singletons] Heap.bigOpS_ofSet

@[rocq_alias trillium.fairness.big_opM_fmap_singletons]
theorem big_opM_fmap_singletons {K : Type _} {M : Type _ → Type _} [LawfulFiniteMap M K]
    {A B : Type _} [ORA B] (m : M A) (f : A → B) :
    ([^ ORA.op map] k ↦ x ∈ m, Iris.Std.PartialMap.map f (Iris.Std.PartialMap.singleton k x : M A)) =
      Iris.Std.PartialMap.map f m := by
  classical
  have : ∀ k x, Iris.Std.PartialMap.map f (Iris.Std.PartialMap.singleton k x : M A) = Iris.Std.PartialMap.singleton k (f x) :=
    fun k x => LawfulPartialMap.equiv_iff_eq.1 fun k' => by
      simp only [Iris.Std.PartialMap.singleton, LawfulPartialMap.get?_map, LawfulPartialMap.get?_insert,
        get?_empty]
      split <;> rfl
  simp only [this]
  rw [← BigOpM.bigOpM_map_eq f (fun k y => (Iris.Std.PartialMap.singleton k y : M B)) m]
  exact Heap.bigOpM_singletons _

attribute [rocq_alias trillium.fairness.big_opM_insert_delete'] BigOpM.bigOpM_delete_eq

@[rocq_alias trillium.fairness.fmap_flat_map]
theorem fmap_flat_map {A B C : Type _} (f : A → List B) (g : B → C) (l : List A) :
    (l.flatMap f).map g = l.flatMap (List.map g ∘ f) := by
  induction l with
  | nil => rfl
  | cons a l IH => simp [List.flatMap_cons, List.map_append, IH]

@[rocq_alias trillium.fairness.concat_NoDup]
theorem concat_NoDup {A : Type _} (ll : List (List A)) :
    (∀ (i : Nat) (l : List A), ll[i]? = some l → l.Nodup) →
    (∀ (i j : Nat) (li lj : List A), i ≠ j → ll[i]? = some li → ll[j]? = some lj → li.Disjoint lj) →
    ll.flatten.Nodup := by
  induction ll with
  | nil => intros; exact List.nodup_nil
  | cons l ll IH =>
    intro H H0
    rw [List.flatten_cons, List.nodup_append]
    refine ⟨H 0 l rfl, IH (fun i l h => H (i + 1) l h)
      (fun i j li lj ne hi hj => H0 (i + 1) (j + 1) li lj (by omega) hi hj), ?_⟩
    intro x hx y hy e
    subst e
    obtain ⟨lx, hlx, hy⟩ := List.mem_flatten.1 hy
    obtain ⟨ix, IX⟩ := List.mem_iff_getElem?.1 hlx
    exact H0 0 (ix + 1) l lx (by omega) rfl IX hx hy

section Arithmetic

@[rocq_alias trillium.fairness.even_succ_negb]
theorem even_succ_negb (n : Nat) : decide (Even (n + 1)) = !decide (Even n) := by
  rcases Nat.even_or_odd n with h | h
  · simp [Nat.even_add_one, h]
  · have := Nat.not_even_iff_odd.2 h
    simp [h, this]

@[rocq_alias trillium.fairness.odd_succ_negb]
theorem odd_succ_negb (n : Nat) : decide (Odd (n + 1)) = !decide (Odd n) := by
  rcases Nat.even_or_odd n with h | h
  · have := Nat.not_odd_iff_even.2 h
    simp [h, this]
  · simp [Nat.odd_add_one, h]

@[rocq_alias trillium.fairness.even_plus1_negb]
theorem even_plus1_negb (n : Nat) : decide (Even (n + 1)) = !decide (Even n) :=
  even_succ_negb n

@[rocq_alias trillium.fairness.odd_plus1_negb]
theorem odd_plus1_negb (n : Nat) : decide (Odd (n + 1)) = !decide (Odd n) :=
  odd_succ_negb n

@[rocq_alias trillium.fairness.even_odd_False]
theorem even_odd_False (n : Nat) : Even n → Odd n → False :=
  fun he ho => Nat.not_even_iff_odd.2 ho he

@[rocq_alias trillium.fairness.even_not_odd]
theorem even_not_odd (n : Nat) : Even n → ¬ Odd n := even_odd_False n

@[rocq_alias trillium.fairness.odd_not_even]
theorem odd_not_even (n : Nat) : Odd n → ¬ Even n := fun ho he => even_odd_False n he ho

@[rocq_alias trillium.fairness.even_or_odd]
theorem even_or_odd (n : Nat) : Even n ∨ Odd n := Nat.even_or_odd n

end Arithmetic

end Trillium.Fairness
