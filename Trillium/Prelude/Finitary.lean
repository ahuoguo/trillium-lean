/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Basic.Finite.Sum
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.List
import Trillium.Std.Maps
import Trillium.Prelude.Classical
import Trillium.Prelude.Quantifiers
import Trillium.Prelude.Sigma

/-!
# Finiteness

Port of `trillium/prelude/finitary.v`.

## Representation decisions

* stdpp's `Finite A` (a type class carrying a duplicate-free enumeration list) is Mathlib's
  **`Finite A`** (a `Prop`-valued class). Trillium only uses `Finite` propositionally (all its
  finiteness facts are proved classically, e.g. `smaller_card_nat_finite`, `in_list_finite`), and a
  `Prop` avoids any decidability/proof-irrelevance side conditions. A `Fintype` can be recovered
  noncomputably with `Fintype.ofFinite` when an explicit enumeration is needed. The
  finite-branching argument of the adequacy theorem goes through
  `finite_smaller_card_nat : Finite A → SmallerCard A ℕ` and `in_list_finite`.
* stdpp's `ProofIrrel` and (classical) `Decision` hypotheses are dropped: proof irrelevance is
  definitional in Lean, and the proofs here are classical.
* `gmap`/`gset` are `Trillium.GMap`/`Trillium.GSet`. As in the other ports
  (e.g. `Trillium.Fairis.MapIncludedUtils`), `dom m = D` is stated as `∀ k, k ∈ m ↔ k ∈ D`,
  `X ⊆ D` (for sets) as `∀ k, k ∈ X → k ∈ D`, `map_Forall (λ _ v, φ v) m` as
  `∀ k v, m[k]? = some v → φ v`, `elements D` as `D.toList`, `Forall P l` as `∀ x ∈ l, P x`,
  `≡ₚ` as `List.Perm`, `seq 0 n` as `List.range n`, and list `bind` as `List.flatMap`.
-/

namespace Trillium

/-! ## Finite types are smaller than `ℕ` -/

section finite_smaller_card_nat

variable {A : Type _}

/-- `[f n, f (n-1), …, f 0]`. -/
@[rocq_alias trillium.list_generated_by]
def listGeneratedBy (f : ℕ → A) : ℕ → List A
  | 0 => [f 0]
  | n + 1 => f (n + 1) :: listGeneratedBy f n

@[rocq_alias trillium.list_generated_by_length]
theorem listGeneratedBy_length (f : ℕ → A) (n : ℕ) : (listGeneratedBy f n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n IH => simp [listGeneratedBy, IH]

@[rocq_alias trillium.elem_of_list_generated_by]
theorem mem_listGeneratedBy (f : ℕ → A) (n : ℕ) (x : A) :
    x ∈ listGeneratedBy f n ↔ ∃ m, m ≤ n ∧ x = f m := by
  induction n with
  | zero => simp [listGeneratedBy]
  | succ n IH =>
    simp only [listGeneratedBy, List.mem_cons, IH]
    constructor
    · rintro (rfl | ⟨m, Hm, rfl⟩)
      · exact ⟨n + 1, le_rfl, rfl⟩
      · exact ⟨m, by omega, rfl⟩
    · rintro ⟨m, Hm, rfl⟩
      rcases Nat.lt_or_eq_of_le Hm with Hm | rfl
      · exact .inr ⟨m, by omega, rfl⟩
      · exact .inl rfl

@[rocq_alias trillium.list_generated_by_NoDup]
theorem listGeneratedBy_nodup (f : ℕ → A) (n : ℕ) (Hf : Function.Injective f) :
    (listGeneratedBy f n).Nodup := by
  induction n with
  | zero => simp [listGeneratedBy]
  | succ n IH =>
    refine List.nodup_cons.mpr ⟨fun Hin => ?_, IH⟩
    obtain ⟨m, Hm, Heq⟩ := (mem_listGeneratedBy f n _).mp Hin
    have := Hf Heq
    omega

@[rocq_alias trillium.finite_smaller_card_nat]
theorem finite_smaller_card_nat (_ : Finite A) : SmallerCard A ℕ := by
  intro f Hf
  have := Fintype.ofFinite A
  have Hlen := (listGeneratedBy_nodup f (Fintype.card A) Hf).length_le_card
  rw [listGeneratedBy_length] at Hlen
  omega

end finite_smaller_card_nat

attribute [rocq_alias trillium.surjective] Function.Surjective

/-! ## Types smaller than `ℕ` are finite -/

section smaller_card_nat_finite

variable {A : Type _}

section no_fin_inj

variable (Hnfin : ¬ Finite A)

include Hnfin in
@[rocq_alias trillium.no_fin_new_elem_exist]
theorem no_fin_new_elem_exist (l : List A) : ∃ x, x ∉ l := by
  by_contra H
  simp only [not_exists, not_not] at H
  exact Hnfin (Set.finite_univ_iff.mp ((List.finite_toSet l).subset fun x _ => H x))

/-- Extend `l` by `n` fresh elements (which exist since `A` is not finite). -/
@[rocq_alias trillium.no_fin_make_list]
noncomputable def noFinMakeList (l : List A) : ℕ → List A
  | 0 => l
  | n + 1 =>
    noFinMakeList l n ++ [Classical.choose (no_fin_new_elem_exist Hnfin (noFinMakeList l n))]

@[rocq_alias trillium.no_fin_make_list_length]
theorem noFinMakeList_length (l : List A) (n : ℕ) :
    (noFinMakeList Hnfin l n).length = l.length + n := by
  induction n with
  | zero => rfl
  | succ n IH => simp [noFinMakeList, IH]; omega

@[rocq_alias trillium.no_fin_make_list_prefix]
theorem noFinMakeList_prefix (l : List A) (n1 n2 : ℕ) (H : n1 ≤ n2) :
    noFinMakeList Hnfin l n1 <+: noFinMakeList Hnfin l n2 := by
  induction H with
  | refl => exact List.prefix_refl _
  | step _ IH => exact IH.trans (List.prefix_append _ _)

@[rocq_alias trillium.no_fin_make_list_NoDup]
theorem noFinMakeList_nodup (l : List A) (n : ℕ) (Hl : l.Nodup) :
    (noFinMakeList Hnfin l n).Nodup := by
  induction n with
  | zero => exact Hl
  | succ n IH =>
    simp only [noFinMakeList]
    refine List.nodup_append.mpr ⟨IH, List.nodup_singleton _, ?_⟩
    intro x Hx y Hy
    rw [List.mem_singleton] at Hy
    subst Hy
    rintro rfl
    exact Classical.choose_spec (no_fin_new_elem_exist Hnfin (noFinMakeList Hnfin l n)) Hx

/-- An injection `ℕ → A`: the `n`-th fresh element. -/
@[rocq_alias trillium.no_fin_make_inj_fun]
noncomputable def noFinMakeInjFun (n : ℕ) : A :=
  ((noFinMakeList Hnfin [] (n + 1))[n]?).getD (Classical.choose (no_fin_new_elem_exist Hnfin []))

@[rocq_alias trillium.no_fin_make_inj_fun_inj]
theorem noFinMakeInjFun_inj : Function.Injective (noFinMakeInjFun Hnfin) := by
  have Hnm : ∀ n m, n ≤ m → noFinMakeInjFun Hnfin n = noFinMakeInjFun Hnfin m → n = m := by
    intro n m Hnm Hfnm
    unfold noFinMakeInjFun at Hfnm
    have Hn : n < (noFinMakeList Hnfin [] (n + 1)).length := by
      rw [noFinMakeList_length]; simp
    have Hm : m < (noFinMakeList Hnfin [] (m + 1)).length := by
      rw [noFinMakeList_length]; simp
    rw [List.getElem?_eq_getElem Hn, List.getElem?_eq_getElem Hm] at Hfnm
    simp only [Option.getD_some] at Hfnm
    obtain ⟨t, Ht⟩ := noFinMakeList_prefix Hnfin [] (n + 1) (m + 1) (by omega)
    have Hk : (noFinMakeList Hnfin [] (m + 1))[n]? = (noFinMakeList Hnfin [] (m + 1))[m]? := by
      rw [← Ht, List.getElem?_append_left Hn, List.getElem?_eq_getElem Hn, Ht,
        List.getElem?_eq_getElem Hm, Hfnm]
    exact ((List.Nodup.getElem?_inj (by rw [← Ht, List.length_append]; omega)
      (noFinMakeList_nodup Hnfin [] (m + 1) List.nodup_nil)).mp Hk)
  intro n m Hfnm
  rcases le_total n m with H | H
  · exact Hnm n m H Hfnm
  · exact (Hnm m n H Hfnm.symm).symm

end no_fin_inj

@[rocq_alias trillium.smaller_card_nat_finite]
theorem smaller_card_nat_finite (HA : SmallerCard A ℕ) : Finite A := by
  by_contra Hnfin
  exact HA (noFinMakeInjFun Hnfin) (noFinMakeInjFun_inj Hnfin)

end smaller_card_nat_finite

attribute [rocq_alias trillium.NoDup_list_prod] List.Nodup.product

/-! ## Finiteness of subtypes -/

section finite_lemmas

variable {A B : Type _}

@[rocq_alias trillium.sig_finite_and]
instance sig_finite_and {P : A → Prop} {Q : B → Prop} [HfP : Finite {x : A // P x}]
    [HfQ : Finite {x : B // Q x}] : Finite {x : A × B // P x.1 ∧ Q x.2} :=
  Finite.of_surjective (fun x : {x : A // P x} × {x : B // Q x} => sigProdAnd x.1 x.2)
    fun ⟨⟨a, b⟩, Ha, Hb⟩ => ⟨(⟨a, Ha⟩, ⟨b, Hb⟩), rfl⟩

@[rocq_alias trillium.sig_finite_and2]
theorem sig_finite_and2 (P Q : A → Prop) (HfP : Finite {x : A // P x}) :
    Finite {x : A // P x ∧ Q x} :=
  Finite.of_injective (fun x : {x : A // P x ∧ Q x} => (⟨x.1, x.2.1⟩ : {x : A // P x}))
    fun _ _ Hxy => Subtype.ext (congrArg Subtype.val Hxy :)

@[rocq_alias trillium.sig_finite_eq1]
instance sig_finite_eq1 (a : A) : Finite {x : A // x = a} :=
  Finite.of_surjective (fun _ : Unit => (⟨a, rfl⟩ : {x : A // x = a}))
    fun ⟨_, Hx⟩ => ⟨(), Subtype.ext Hx.symm⟩

@[rocq_alias trillium.sig_finite_eq2]
instance sig_finite_eq2 (a : A) : Finite {x : A // a = x} :=
  Finite.of_surjective (fun _ : Unit => (⟨a, rfl⟩ : {x : A // a = x}))
    fun ⟨_, Hx⟩ => ⟨(), Subtype.ext Hx⟩

@[rocq_alias trillium.sig_finite_or]
instance sig_finite_or {P Q : A → Prop} [HfP : Finite {x : A // P x}]
    [HfQ : Finite {x : A // Q x}] : Finite {x : A // P x ∨ Q x} :=
  Finite.of_surjective (Sum.elim (sigProdOrL (Q := Q)) (sigProdOrR (P := P)))
    fun
    | ⟨a, .inl Ha⟩ => ⟨.inl ⟨a, Ha⟩, rfl⟩
    | ⟨a, .inr Ha⟩ => ⟨.inr ⟨a, Ha⟩, rfl⟩

end finite_lemmas

/-! ## Finiteness of subtypes bounded by a list or a set -/

section in_list_finite

variable {A : Type _} {P : A → Prop}

/-- Turn a list all of whose elements satisfy `P` into a list of elements of `{x // P x}`. -/
@[rocq_alias trillium.Forall_to_sig]
def forallToSig : (l : List A) → (∀ x ∈ l, P x) → List {x // P x}
  | [], _ => []
  | a :: l', Hal =>
    ⟨a, Hal a List.mem_cons_self⟩ :: forallToSig l' fun x Hx => Hal x (List.mem_cons_of_mem _ Hx)

@[rocq_alias trillium.elem_of_Forall_to_sig_1]
theorem mem_forallToSig_1 (l : List A) (HPl : ∀ x ∈ l, P x) (x : {x // P x}) :
    x ∈ forallToSig l HPl → x.1 ∈ l := by
  induction l with
  | nil => simp [forallToSig]
  | cons a l IH =>
    simp only [forallToSig, List.mem_cons]
    rintro (rfl | Hx)
    · exact .inl rfl
    · exact .inr (IH _ Hx)

@[rocq_alias trillium.elem_of_Forall_to_sig_2]
theorem mem_forallToSig_2 (l : List A) (HPl : ∀ x ∈ l, P x) (x : A) :
    x ∈ l → ∃ Hx, ⟨x, Hx⟩ ∈ forallToSig l HPl := by
  induction l with
  | nil => simp
  | cons a l IH =>
    simp only [forallToSig, List.mem_cons]
    rintro (rfl | Hx)
    · exact ⟨_, .inl rfl⟩
    · obtain ⟨Hx', Hin⟩ := IH _ Hx
      exact ⟨Hx', .inr Hin⟩

@[rocq_alias trillium.Forall_to_sig_NoDup]
theorem forallToSig_nodup (l : List A) (HPl : ∀ x ∈ l, P x) (Hl : l.Nodup) :
    (forallToSig l HPl).Nodup := by
  induction l with
  | nil => simp [forallToSig]
  | cons a l IH =>
    obtain ⟨Ha, Hl⟩ := List.nodup_cons.mp Hl
    refine List.nodup_cons.mpr ⟨fun Hin => Ha ?_, IH _ Hl⟩
    exact mem_forallToSig_1 l _ _ Hin

@[rocq_alias trillium.in_list_finite]
theorem in_list_finite (l : List A) (Hl : ∀ x, P x → x ∈ l) : Finite {x : A // P x} :=
  ((List.finite_toSet l).subset Hl).to_subtype

@[rocq_alias trillium.in_gset_finite]
theorem in_gset_finite [Ord A] [Std.TransOrd A] [Std.LawfulEqOrd A] (g : GSet A)
    (Hg : ∀ x, P x → x ∈ g) : Finite {x : A // P x} :=
  in_list_finite g.toList fun x Hx => Std.ExtTreeSet.mem_toList.mpr (Hg x Hx)

end in_list_finite

#rocq_ignore trillium.all_the_instances
  "local classical `Decision` instance; Lean uses `Classical.propDecidable` where needed"
#rocq_ignore trillium.proof_irrel_P "local `ProofIrrel` instance; proof irrelevance is definitional in Lean"
#rocq_ignore trillium.all_the_range_instances
  "local classical `Decision` instance; Lean uses `Classical.propDecidable` where needed"
#rocq_ignore trillium.proof_irrel_range_P
  "local `ProofIrrel` instance; proof irrelevance is definitional in Lean"
#rocq_ignore trillium.all_the_range_instances'
  "local classical `Decision` instance; Lean uses `Classical.propDecidable` where needed"

/-! ## Enumerating bounded maps -/

section finite_range_gmap

variable {K : Type _} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]

theorem gset_exists_mem_of_ne_empty {X : GSet K} (Hne : X ≠ ∅) : ∃ k, k ∈ X := by
  by_contra H
  simp only [not_exists] at H
  exact Hne (Std.ExtTreeSet.ext_mem fun k => by simp [H k])

/-- Choose an element of a nonempty set. -/
@[rocq_alias trillium.set_choose_L']
noncomputable def setChooseL' (X : GSet K) (Hne : X ≠ ∅) : {k : K // k ∈ X} :=
  Classical.indefiniteDescription _ (gset_exists_mem_of_ne_empty Hne)

/-- All maps with domain `D` and values `≤ N` (possibly with repetitions). -/
@[rocq_alias trillium.enumerate_gmaps]
def enumerateGmaps : List K → ℕ → List (GMap K ℕ)
  | [], _ => [∅]
  | k :: ks, N =>
    (enumerateGmaps ks N).flatMap fun m1 =>
      (List.range (N + 1)).flatMap fun new => [m1.insert k new]

/-- `m` has domain `{l}` (`l` duplicate-free) and values bounded by `N`. -/
private theorem enumerateGmaps_spec_aux (N : ℕ) (l : List K) (m : GMap K ℕ) (Hl : l.Nodup)
    (Hdom : ∀ k, k ∈ m ↔ k ∈ l) (Hbound : ∀ (k : K) (v : ℕ), m[k]? = some v → v ≤ N) :
    m ∈ enumerateGmaps l N := by
  induction l generalizing m with
  | nil =>
    have : m = ∅ := Std.ExtTreeMap.ext_getElem? fun k => by
      rw [Std.ExtTreeMap.getElem?_empty]
      exact Std.ExtTreeMap.getElem?_eq_none fun Hk => by simpa using (Hdom k).mp Hk
    simp [enumerateGmaps, this]
  | cons a l IH =>
    obtain ⟨Ha, Hl⟩ := List.nodup_cons.mp Hl
    obtain ⟨v, Hv⟩ := Option.isSome_iff_exists.mp
      (Std.ExtTreeMap.mem_iff_isSome_getElem?.mp ((Hdom a).mpr List.mem_cons_self))
    have Hm' : m.erase a ∈ enumerateGmaps l N := by
      refine IH _ Hl (fun k => ?_) (fun k w Hk => ?_)
      · rw [Std.ExtTreeMap.mem_erase, Hdom, List.mem_cons, Ne, Std.compare_eq_iff_eq]
        constructor
        · rintro ⟨Hak, rfl | Hk⟩
          · exact absurd rfl Hak
          · exact Hk
        · intro Hk
          exact ⟨fun Hak => Ha (Hak ▸ Hk), .inr Hk⟩
      · rw [Std.ExtTreeMap.getElem?_erase] at Hk
        split at Hk
        · cases Hk
        · exact Hbound k w Hk
    have Hm : m = (m.erase a).insert a v := Std.ExtTreeMap.ext_getElem? fun k => by
      rw [Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_erase]
      by_cases Hak : a = k
      · subst Hak; simp [Hv]
      · simp [Hak]
    simp only [enumerateGmaps, List.mem_flatMap, List.mem_range, List.mem_singleton]
    exact ⟨m.erase a, Hm', v, Nat.lt_succ_of_le (Hbound a v Hv), Hm⟩

@[rocq_alias trillium.enumerate_gmaps_spec]
theorem enumerateGmaps_spec (N : ℕ) (l : List K) (D : GSet K) (m : GMap K ℕ) :
    D.toList.Perm l ∧ (∀ k, k ∈ m ↔ k ∈ D) ∧ (∀ (k : K) (v : ℕ), m[k]? = some v → v ≤ N) →
      m ∈ enumerateGmaps l N := by
  rintro ⟨Hel, Hdom, Hbound⟩
  refine enumerateGmaps_spec_aux N l m (Hel.nodup_iff.mp ?_) (fun k => ?_) Hbound
  · exact (List.pairwise_iff_getElem.mpr fun i j hi hj hij Heq =>
      (List.pairwise_iff_getElem.mp Std.ExtTreeSet.distinct_toList i j hi hj hij)
        (by rw [Heq]; exact Std.compare_eq_iff_eq.mpr rfl))
  · rw [Hdom, ← Hel.mem_iff, Std.ExtTreeSet.mem_toList]

@[rocq_alias trillium.bounded_maps_finite]
theorem bounded_maps_finite (D : GSet K) (N : ℕ) :
    Finite {m : GMap K ℕ // (∀ k, k ∈ m ↔ k ∈ D) ∧ ∀ (k : K) (v : ℕ), m[k]? = some v → v ≤ N} :=
  in_list_finite (enumerateGmaps D.toList N) fun m H =>
    enumerateGmaps_spec N _ D m ⟨List.Perm.refl _, H⟩

@[rocq_alias trillium.enum_gmap_bounded]
def enumGmapBounded (D : GSet K) (N : ℕ) : List (GMap K ℕ) :=
  enumerateGmaps D.toList N

@[rocq_alias trillium.enum_gmap_bounded_spec]
theorem enumGmapBounded_spec (N : ℕ) (D : GSet K) (m : GMap K ℕ) :
    (∀ k, k ∈ m ↔ k ∈ D) ∧ (∀ (k : K) (v : ℕ), m[k]? = some v → v ≤ N) → m ∈ enumGmapBounded D N :=
  fun H => enumerateGmaps_spec N _ D m ⟨List.Perm.refl _, H⟩

private theorem enumerateGmaps_dom (N : ℕ) (l : List K) :
    ∀ m ∈ enumerateGmaps l N, ∀ k, k ∈ m ↔ k ∈ l := by
  induction l with
  | nil => simp [enumerateGmaps]
  | cons a l IH =>
    simp only [enumerateGmaps, List.mem_flatMap, List.mem_range, List.mem_singleton]
    rintro m ⟨m', Hm', v, -, rfl⟩ k
    rw [Std.ExtTreeMap.mem_insert, Std.compare_eq_iff_eq, IH m' Hm', List.mem_cons, eq_comm]

@[rocq_alias trillium.enum_gmap_dom]
theorem enumGmap_dom (N : ℕ) (D : GSet K) :
    ∀ m ∈ enumGmapBounded D N, ∀ k, k ∈ m ↔ k ∈ D := by
  intro m Hm k
  rw [enumerateGmaps_dom N _ m Hm, Std.ExtTreeSet.mem_toList]

/-- The bounded maps with domain `D`, packed with their domain proof. -/
@[rocq_alias trillium.enum_gmap_bounded']
def enumGmapBounded' (D : GSet K) (N : ℕ) : List {m : GMap K ℕ // ∀ k, k ∈ m ↔ k ∈ D} :=
  forallToSig _ (enumGmap_dom N D)

@[rocq_alias trillium.enum_gmap_bounded'_spec]
theorem enumGmapBounded'_spec (N : ℕ) (D : GSet K) (m : GMap K ℕ) (Hdom : ∀ k, k ∈ m ↔ k ∈ D) :
    (∀ k, k ∈ m ↔ k ∈ D) ∧ (∀ (k : K) (v : ℕ), m[k]? = some v → v ≤ N) →
      (⟨m, Hdom⟩ : {m : GMap K ℕ // ∀ k, k ∈ m ↔ k ∈ D}) ∈ enumGmapBounded' D N := fun H =>
  (mem_forallToSig_2 _ (enumGmap_dom N D) m (enumGmapBounded_spec N D m H)).choose_spec

end finite_range_gmap

/-! ## Enumerating maps with values in a list -/

section finite_range_gmap

variable {A : Type _} {K : Type _} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]

/-- All maps with domain `D` and values in `lr` (possibly with repetitions). -/
@[rocq_alias trillium.enumerate_range_gmaps]
def enumerateRangeGmaps : List K → List A → List (GMap K A)
  | [], _ => [∅]
  | k :: ks, lr =>
    (enumerateRangeGmaps ks lr).flatMap fun m1 => lr.flatMap fun new => [m1.insert k new]

private theorem enumerateRangeGmaps_spec_aux (lr : List A) (l : List K) (m : GMap K A)
    (Hl : l.Nodup) (Hdom : ∀ k, k ∈ m ↔ k ∈ l) (Hbound : ∀ (k : K) (v : A), m[k]? = some v → v ∈ lr) :
    m ∈ enumerateRangeGmaps l lr := by
  induction l generalizing m with
  | nil =>
    have : m = ∅ := Std.ExtTreeMap.ext_getElem? fun k => by
      rw [Std.ExtTreeMap.getElem?_empty]
      exact Std.ExtTreeMap.getElem?_eq_none fun Hk => by simpa using (Hdom k).mp Hk
    simp [enumerateRangeGmaps, this]
  | cons a l IH =>
    obtain ⟨Ha, Hl⟩ := List.nodup_cons.mp Hl
    obtain ⟨v, Hv⟩ := Option.isSome_iff_exists.mp
      (Std.ExtTreeMap.mem_iff_isSome_getElem?.mp ((Hdom a).mpr List.mem_cons_self))
    have Hm' : m.erase a ∈ enumerateRangeGmaps l lr := by
      refine IH _ Hl (fun k => ?_) (fun k w Hk => ?_)
      · rw [Std.ExtTreeMap.mem_erase, Hdom, List.mem_cons, Ne, Std.compare_eq_iff_eq]
        constructor
        · rintro ⟨Hak, rfl | Hk⟩
          · exact absurd rfl Hak
          · exact Hk
        · intro Hk
          exact ⟨fun Hak => Ha (Hak ▸ Hk), .inr Hk⟩
      · rw [Std.ExtTreeMap.getElem?_erase] at Hk
        split at Hk
        · cases Hk
        · exact Hbound k w Hk
    have Hm : m = (m.erase a).insert a v := Std.ExtTreeMap.ext_getElem? fun k => by
      rw [Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_erase]
      by_cases Hak : a = k
      · subst Hak; simp [Hv]
      · simp [Hak]
    simp only [enumerateRangeGmaps, List.mem_flatMap, List.mem_singleton]
    exact ⟨m.erase a, Hm', v, Hbound a v Hv, Hm⟩

@[rocq_alias trillium.enumerate_range_gmaps_spec]
theorem enumerateRangeGmaps_spec (l : List K) (lr : List A) (D : GSet K) (m : GMap K A) :
    D.toList.Perm l ∧ (∀ k, k ∈ m ↔ k ∈ D) ∧ (∀ (k : K) (v : A), m[k]? = some v → v ∈ lr) →
      m ∈ enumerateRangeGmaps l lr := by
  rintro ⟨Hel, Hdom, Hbound⟩
  refine enumerateRangeGmaps_spec_aux lr l m (Hel.nodup_iff.mp ?_) (fun k => ?_) Hbound
  · exact (List.pairwise_iff_getElem.mpr fun i j hi hj hij Heq =>
      (List.pairwise_iff_getElem.mp Std.ExtTreeSet.distinct_toList i j hi hj hij)
        (by rw [Heq]; exact Std.compare_eq_iff_eq.mpr rfl))
  · rw [Hdom, ← Hel.mem_iff, Std.ExtTreeSet.mem_toList]

@[rocq_alias trillium.bounded_range_maps_finite]
theorem bounded_range_maps_finite (D : GSet K) (lr : List A) :
    Finite {m : GMap K A // (∀ k, k ∈ m ↔ k ∈ D) ∧ ∀ (k : K) (v : A), m[k]? = some v → v ∈ lr} :=
  in_list_finite (enumerateRangeGmaps D.toList lr) fun m H =>
    enumerateRangeGmaps_spec _ lr D m ⟨List.Perm.refl _, H⟩

@[rocq_alias trillium.enum_gmap_range_bounded]
def enumGmapRangeBounded (D : GSet K) (lr : List A) : List (GMap K A) :=
  enumerateRangeGmaps D.toList lr

@[rocq_alias trillium.enum_gmap_range_bounded_spec]
theorem enumGmapRangeBounded_spec (D : GSet K) (m : GMap K A) (lr : List A) :
    (∀ k, k ∈ m ↔ k ∈ D) ∧ (∀ (k : K) (v : A), m[k]? = some v → v ∈ lr) → m ∈ enumGmapRangeBounded D lr :=
  fun H => enumerateRangeGmaps_spec _ lr D m ⟨List.Perm.refl _, H⟩

private theorem enumerateRangeGmaps_dom (lr : List A) (l : List K) :
    ∀ m ∈ enumerateRangeGmaps l lr, ∀ k, k ∈ m ↔ k ∈ l := by
  induction l with
  | nil => simp [enumerateRangeGmaps]
  | cons a l IH =>
    simp only [enumerateRangeGmaps, List.mem_flatMap, List.mem_singleton]
    rintro m ⟨m', Hm', v, -, rfl⟩ k
    rw [Std.ExtTreeMap.mem_insert, Std.compare_eq_iff_eq, IH m' Hm', List.mem_cons, eq_comm]

@[rocq_alias trillium.enum_gmap_range_dom]
theorem enumGmapRange_dom (lr : List A) (D : GSet K) :
    ∀ m ∈ enumGmapRangeBounded D lr, ∀ k, k ∈ m ↔ k ∈ D := by
  intro m Hm k
  rw [enumerateRangeGmaps_dom lr _ m Hm, Std.ExtTreeSet.mem_toList]

@[rocq_alias trillium.enum_gmap_range_bounded']
def enumGmapRangeBounded' (D : GSet K) (lr : List A) :
    List {m : GMap K A // ∀ k, k ∈ m ↔ k ∈ D} :=
  forallToSig _ (enumGmapRange_dom lr D)

@[rocq_alias trillium.enum_gmap_range_bounded'_spec]
theorem enumGmapRangeBounded'_spec (lr : List A) (D : GSet K) (m : GMap K A)
    (Hdom : ∀ k, k ∈ m ↔ k ∈ D) :
    (∀ k, k ∈ m ↔ k ∈ D) ∧ (∀ (k : K) (v : A), m[k]? = some v → v ∈ lr) →
      (⟨m, Hdom⟩ : {m : GMap K A // ∀ k, k ∈ m ↔ k ∈ D}) ∈ enumGmapRangeBounded' D lr := fun H =>
  (mem_forallToSig_2 _ (enumGmapRange_dom lr D) m (enumGmapRangeBounded_spec D m lr H)).choose_spec

end finite_range_gmap

/-! ## Enumerating subsets -/

section enumerate_gsets

variable {A : Type _} [Ord A] [Std.TransOrd A] [Std.LawfulEqOrd A]

/-- All subsets of `D`. (`{[k]} ∪ s` is written `s.insert k`.) -/
@[rocq_alias trillium.enumerate_dom_gsets]
def enumerateDomGsets : List A → List (GSet A)
  | [] => [∅]
  | k :: ks =>
    (enumerateDomGsets ks).flatMap fun s_wo =>
      [true, false].flatMap fun b => if b then [s_wo] else [s_wo.insert k]

@[rocq_alias trillium.enumerate_dom_gsets']
def enumerateDomGsets' (D : GSet A) : List (GSet A) :=
  enumerateDomGsets D.toList

private theorem enumerateDomGsets_spec_aux (l : List A) (m : GSet A) (Hm : ∀ x, x ∈ m → x ∈ l) :
    m ∈ enumerateDomGsets l := by
  induction l generalizing m with
  | nil =>
    have : m = ∅ := Std.ExtTreeSet.ext_mem fun k => by simpa using Hm k
    simp [enumerateDomGsets, this]
  | cons a l IH =>
    have Hm' : m.erase a ∈ enumerateDomGsets l := by
      refine IH _ fun x Hx => ?_
      rw [Std.ExtTreeSet.mem_erase, Ne, Std.compare_eq_iff_eq] at Hx
      rcases List.mem_cons.mp (Hm x Hx.2) with rfl | Hx'
      · exact absurd rfl Hx.1
      · exact Hx'
    simp only [enumerateDomGsets, List.mem_flatMap]
    refine ⟨m.erase a, Hm', ?_⟩
    by_cases Ha : a ∈ m
    · refine ⟨false, by simp, ?_⟩
      simp only [Bool.false_eq_true, ↓reduceIte, List.mem_singleton]
      refine Std.ExtTreeSet.ext_mem fun k => ?_
      rw [Std.ExtTreeSet.mem_insert, Std.ExtTreeSet.mem_erase, Ne, Std.compare_eq_iff_eq]
      by_cases Hak : a = k
      · subst Hak; simp [Ha]
      · simp [Hak]
    · refine ⟨true, by simp, ?_⟩
      simp only [↓reduceIte, List.mem_singleton]
      refine Std.ExtTreeSet.ext_mem fun k => ?_
      rw [Std.ExtTreeSet.mem_erase, Ne, Std.compare_eq_iff_eq]
      by_cases Hak : a = k
      · subst Hak; simp [Ha]
      · simp [Hak]

@[rocq_alias trillium.enumerate_gsets_spec]
theorem enumerate_gsets_spec (D : GSet A) (l : List A) (m : GSet A) :
    D.toList.Perm l ∧ (∀ x, x ∈ m → x ∈ D) → m ∈ enumerateDomGsets l := by
  rintro ⟨Hel, Hsub⟩
  exact enumerateDomGsets_spec_aux l m fun x Hx =>
    Hel.mem_iff.mp (Std.ExtTreeSet.mem_toList.mpr (Hsub x Hx))

@[rocq_alias trillium.enumerate_dom_gsets'_spec]
theorem enumerateDomGsets'_spec (D s : GSet A) (H : ∀ x, x ∈ s → x ∈ D) :
    s ∈ enumerateDomGsets' D :=
  enumerate_gsets_spec D _ s ⟨List.Perm.refl _, H⟩

end enumerate_gsets

/-! ## Enumerating maps with bounded values and domain included in a set -/

section finite_range_gmap

variable {K : Type _} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]

@[rocq_alias trillium.enumerate_subdomain_gmap]
def enumerateSubdomainGmap (D : GSet K) (B : ℕ) : List (GMap K ℕ) :=
  (enumerateDomGsets' D).flatMap fun D' => (enumGmapBounded' D' B).flatMap fun m => [m.1]

@[rocq_alias trillium.enumerate_subdomain_gmap_spec]
theorem enumerateSubdomainGmap_spec (m : GMap K ℕ) (D : GSet K) (B : ℕ)
    (Hincl : ∀ k, k ∈ m → k ∈ D) (Hfa : ∀ (k : K) (v : ℕ), m[k]? = some v → v ≤ B) :
    m ∈ enumerateSubdomainGmap D B := by
  -- `dom m`, as a set
  let D' : GSet K := D.filter fun k => m.contains k
  have HD' : ∀ k, k ∈ m ↔ k ∈ D' := fun k => by
    simp only [D', Std.ExtTreeSet.mem_filter, Std.ExtTreeSet.get_eq, Std.ExtTreeMap.contains_iff_mem]
    exact ⟨fun Hk => ⟨Hincl k Hk, Hk⟩, fun ⟨_, Hk⟩ => Hk⟩
  simp only [enumerateSubdomainGmap, List.mem_flatMap, List.mem_singleton]
  refine ⟨D', enumerateDomGsets'_spec D D' fun k Hk => Hincl k ((HD' k).mpr Hk), ⟨m, HD'⟩,
    enumGmapBounded'_spec B D' m HD' ⟨HD', Hfa⟩, rfl⟩

end finite_range_gmap

end Trillium
