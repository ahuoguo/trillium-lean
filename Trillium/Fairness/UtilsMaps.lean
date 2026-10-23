/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.Fairness.UtilsSets
import Iris.Algebra.Heap
import Iris.Algebra.Agree

/-!
# Map helpers
Port of `fairness/utils_maps.v`.

`gmap K V` is `Trillium.GMap K V` (`Std.ExtTreeMap K V compare`); we state everything with the
core `Std.ExtTreeMap` API: `m[k]?` (stdpp `m !! k`), `m.insert k v` (`<[k:=v]> m`),
`m.erase k` (`delete k m`), `m.map (fun _ => f)` (`f <$> m`), `m.filterMap f`
(`map_imap f m`), `m.filter (fun k v => decide (P (k, v)))` (`filter P m`),
`m.foldr f b` (`map_fold f b m`) and `m₁ ∪ m₂`. **Note:** core's union is *right*-biased,
stdpp's is left-biased; all unions in this file are of disjoint maps.

This file adds the missing stdpp vocabulary for `GMap` (namespace `Trillium.GMap`):
* `GMap.dom m : GSet K` (stdpp `dom m`), with `GMap.mem_dom : k ∈ dom m ↔ k ∈ m`;
* `m₁ ⊆ m₂` (stdpp map inclusion), `GMap.Disjoint m₁ m₂` (stdpp `m₁ ##ₘ m₂`, notation
  `m₁ ##ₘ m₂` after `open Trillium`);
* `GMap.singleton k v` (stdpp `{[k := v]}`), `GMap.img m : GSet V` (stdpp `map_img m`),
  `m ⇂ R` (Trillium's domain restriction, after `open Trillium`);
* `GMap.getElem?_insert_ite`/`GMap.getElem?_erase_ite`, stated with `=` on keys.

Lemmas that stdpp/Trillium state about the gmap *CMRA* (`gmap_disj_op_union`,
`map_nat_agree_valid`) are stated for iris-lean's generic heap CMRA on any
`LawfulPartialMap M K` (which covers `GMap` via `M := (Std.ExtTreeMap K · compare)`).
-/

set_option linter.unusedSectionVars false

namespace Trillium

open Iris Iris.Std

namespace GMap

variable {K V : Type _} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]

/-- stdpp's `dom m`. -/
def dom (m : GMap K V) : GSet K := ⟨m.map fun _ _ => ()⟩

omit [Std.LawfulEqOrd K] in
@[simp]
theorem mem_dom {m : GMap K V} {k : K} : k ∈ dom m ↔ k ∈ m := by
  rw [GSet.mem_iff_mem_inner]
  exact Std.ExtTreeMap.mem_map

omit [Std.LawfulEqOrd K] in
theorem mem_iff_exists {m : GMap K V} {k : K} : k ∈ m ↔ ∃ v, m[k]? = some v := by
  rw [Std.ExtTreeMap.mem_iff_isSome_getElem?, Option.isSome_iff_exists]

omit [Std.LawfulEqOrd K] in
theorem not_mem_iff {m : GMap K V} {k : K} : k ∉ m ↔ m[k]? = none := by
  rw [Std.ExtTreeMap.mem_iff_isSome_getElem?, Option.not_isSome_iff_eq_none]

omit [Std.LawfulEqOrd K] in
theorem mem_dom_iff {m : GMap K V} {k : K} : k ∈ dom m ↔ ∃ v, m[k]? = some v := by
  rw [mem_dom, mem_iff_exists]

omit [Std.LawfulEqOrd K] in
theorem mem_of_getElem? {m : GMap K V} {k : K} {v : V} (h : m[k]? = some v) : k ∈ m :=
  mem_iff_exists.2 ⟨v, h⟩

/-- stdpp's map inclusion `m₁ ⊆ m₂`. -/
instance instHasSubset : HasSubset (GMap K V) :=
  ⟨fun m₁ m₂ => ∀ (k : K) (v : V), m₁[k]? = some v → m₂[k]? = some v⟩

omit [Std.LawfulEqOrd K] in
theorem subseteq_def {m₁ m₂ : GMap K V} :
    m₁ ⊆ m₂ ↔ ∀ (k : K) (v : V), m₁[k]? = some v → m₂[k]? = some v := .rfl

/-- stdpp's `m₁ ##ₘ m₂`. -/
abbrev Disjoint (m₁ m₂ : GMap K V) : Prop := ∀ k : K, m₁[k]? = none ∨ m₂[k]? = none

@[inherit_doc] scoped infix:50 " ##ₘ " => GMap.Disjoint

omit [Std.LawfulEqOrd K] in
theorem disjoint_iff_mem {m₁ m₂ : GMap K V} : m₁ ##ₘ m₂ ↔ ∀ k, k ∈ m₁ → k ∉ m₂ := by
  refine forall_congr' fun k => ?_
  rw [← not_mem_iff, ← not_mem_iff]
  tauto

theorem disjoint_dom {m₁ m₂ : GMap K V} : m₁ ##ₘ m₂ ↔ dom m₁ ## dom m₂ := by
  rw [disjoint_iff_mem]
  simp only [Iris.Std.Disjoint.disjoint, mem_dom]
  exact forall_congr' fun _ => by tauto

/-- stdpp's `{[k := v]}`. -/
def singleton (k : K) (v : V) : GMap K V := (∅ : GMap K V).insert k v

open Classical in
theorem getElem?_insert_ite {m : GMap K V} {i k : K} {x : V} :
    (m.insert i x)[k]? = if i = k then some x else m[k]? := by
  rw [Std.ExtTreeMap.getElem?_insert]
  by_cases h : i = k <;> simp [h]

open Classical in
theorem getElem?_erase_ite {m : GMap K V} {i k : K} :
    (m.erase i)[k]? = if i = k then none else m[k]? := by
  rw [Std.ExtTreeMap.getElem?_erase]
  by_cases h : i = k <;> simp [h]

open Classical in
theorem getElem?_singleton {k k' : K} {v : V} :
    (singleton k v)[k']? = if k = k' then some v else none := by
  rw [singleton, getElem?_insert_ite, Std.ExtTreeMap.getElem?_empty]

omit [Std.LawfulEqOrd K] in
theorem getElem?_union_disjoint {m₁ m₂ : GMap K V} (h : m₁ ##ₘ m₂) (k : K) :
    (m₁ ∪ m₂)[k]? = m₁[k]?.or m₂[k]? := by
  rw [Std.ExtTreeMap.getElem?_union]
  rcases h k with h | h <;> simp [h]

/-- stdpp's `map_img m`. -/
def img [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V] (m : GMap K V) : GSet V :=
  LawfulSet.ofList (m.toList.map Prod.snd)

theorem mem_img [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V] {m : GMap K V} {v : V} :
    v ∈ img m ↔ ∃ k : K, m[k]? = some v := by
  simp [img, ← LawfulSet.mem_ofList, Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some]

theorem dom_empty : dom (∅ : GMap K V) = ∅ := by
  ext k; simp [LawfulSet.mem_empty]

theorem eq_empty_iff {m : GMap K V} : m = ∅ ↔ ∀ k : K, m[k]? = none := by
  rw [Std.ExtTreeMap.eq_empty_iff_forall_not_mem]
  simp only [not_mem_iff]

end GMap

namespace Fairness

open GMap

section gmap

variable {K : Type _} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]

@[rocq_alias trillium.fairness.max_gmap]
def maxGMap (m : GMap K Nat) : Nat := m.foldr (fun _ v r => max v r) 0

@[rocq_alias trillium.fairness.max_gmap_spec]
theorem maxGMap_spec (m : GMap K Nat) : ∀ (k : K) (v : Nat), m[k]? = some v → v ≤ maxGMap m := by
  intro k v h
  rw [← Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some] at h
  rw [maxGMap, Std.ExtTreeMap.foldr_eq_foldr_toList]
  generalize m.toList = l at h ⊢
  induction l with
  | nil => simp at h
  | cons a l IH =>
    simp only [List.mem_cons, List.foldr_cons] at h ⊢
    rcases h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (IH h) (Nat.le_max_right _ _)

@[rocq_alias trillium.fairness.gmap_disj_op_union]
theorem gmap_disj_op_union {M : Type _ → Type _} [LawfulPartialMap M K] {A : Type _} [CMRA A]
    (m1 m2 : M A) (h : PartialMap.disjoint m1 m2) :
    m1 • m2 = PartialMap.union m1 m2 := by
  apply LawfulPartialMap.equiv_iff_eq.1
  intro k
  rw [Heap.get?_op, PartialMap.union, get?_merge]
  have := h k
  cases h1 : get? m1 k <;> cases h2 : get? m2 k <;>
    simp_all [Option.merge, Iris.Option.op_none_left_id, Iris.Option.op_none_right_id]

@[rocq_alias trillium.fairness.map_split]
theorem map_split {A : Type _} (m : GMap K A) (k : K) :
    m = (m[k]?.elim ∅ fun v => GMap.singleton k v) ∪ m.erase k := by
  apply Std.ExtTreeMap.ext_getElem?
  intro k'
  rw [Std.ExtTreeMap.getElem?_union, getElem?_erase_ite]
  by_cases h : k = k'
  · subst h
    cases hk : m[k]? <;> simp [getElem?_singleton]
  · simp only [h, ite_false]
    cases hk : m[k]? <;> simp [getElem?_singleton, h]

open Classical in
@[rocq_alias trillium.fairness.lookup_map_singleton]
theorem lookup_map_singleton {A : Type _} (k : K) (a : A) (k' : K) :
    (GMap.singleton k a)[k']? = if k' = k then some a else none := by
  rw [getElem?_singleton]
  by_cases h : k' = k <;> simp [h, Ne.symm]

/-- The bindings of a union of disjoint maps. -/
theorem toList_union_perm {V : Type _} {m1 m2 : GMap K V} (DISJ : m1 ##ₘ m2) :
    (m1 ∪ m2).toList.Perm (m2.toList ++ m1.toList) := by
  have nodup : ∀ m : GMap K V, m.toList.Nodup := fun m =>
    Std.ExtTreeMap.distinct_keys_toList.imp fun {a b} h e => h (by rw [e]; exact Std.ReflCmp.compare_self)
  refine (List.perm_ext_iff_of_nodup (nodup _) ?_).2 ?_
  · refine List.nodup_append.2 ⟨nodup _, nodup _, ?_⟩
    rintro ⟨k, v⟩ h1 ⟨k', v'⟩ h2 e
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some] at h1 h2
    rcases DISJ k with h | h <;> simp_all
  · rintro ⟨k, v⟩
    simp only [List.mem_append, Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some,
      getElem?_union_disjoint DISJ]
    rcases DISJ k with h | h <;> simp [h, or_comm]

@[rocq_alias trillium.fairness.map_fold_union]
theorem map_fold_union {V B : Type _} (m1 m2 : GMap K V) (f : K → V → B → B) (b0 : B)
    (DISJ : m1 ##ₘ m2)
    (ASSOC : ∀ a b c d e, f a b (f c d e) = f c d (f a b e)) :
    (m1 ∪ m2).foldr f b0 = m2.foldr f (m1.foldr f b0) := by
  simp only [Std.ExtTreeMap.foldr_eq_foldr_toList]
  rw [List.Perm.foldr_eq' (f := fun a b => f a.1 a.2 b) (toList_union_perm DISJ)
    (fun x _ y _ z => ASSOC y.1 y.2 x.1 x.2 z), List.foldr_append]

@[rocq_alias trillium.fairness.gmap_filter_dom_id]
theorem gmap_filter_dom_id {A : Type _} (m : GMap K A) :
    m.filter (fun k _ => decide (k ∈ dom m)) = m := by
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  rw [Std.ExtTreeMap.getElem?_filter']
  cases h : m[k]? with
  | none => rfl
  | some v => simp [mem_of_getElem? h]

@[rocq_alias trillium.fairness.gmap_empty_subseteq_equiv]
theorem gmap_empty_subseteq_equiv {A : Type _} (m : GMap K A) : m ⊆ ∅ ↔ m = ∅ := by
  rw [subseteq_def, eq_empty_iff]
  constructor
  · intro h k
    cases hk : m[k]? with
    | none => rfl
    | some v => simpa using h k v hk
  · intro h k v hk
    rw [h k] at hk; cases hk

@[rocq_alias trillium.fairness.gmap_filter_disj_id]
theorem gmap_filter_disj_id {A : Type _} (m1 m2 : GMap K A) (DISJ : m1 ##ₘ m2) :
    m1 = (m1 ∪ m2).filter (fun k _ => decide (k ∈ dom m1)) := by
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  rw [Std.ExtTreeMap.getElem?_filter', getElem?_union_disjoint DISJ]
  cases h : m1[k]? with
  | some v => simp [mem_of_getElem? h, Option.filter]
  | none =>
    have : k ∉ dom m1 := by rw [mem_dom, not_mem_iff]; exact h
    cases m2[k]? <;> simp [this]

@[rocq_alias trillium.fairness.map_img_insert_L]
theorem map_img_insert_L {A : Type _} [Ord A] [Std.TransOrd A] [Std.LawfulEqOrd A]
    (m : GMap K A) (i : K) (x : A) :
    GMap.img (m.insert i x) = {x} ∪ GMap.img (m.erase i) := by
  ext a
  simp only [mem_img, LawfulSet.mem_union, LawfulSet.mem_singleton, getElem?_insert_ite,
    getElem?_erase_ite]
  constructor
  · rintro ⟨k, hk⟩
    by_cases h : i = k
    · simp only [h, ite_true, Option.some.injEq] at hk; exact .inl hk.symm
    · simp only [h, ite_false] at hk; exact .inr ⟨k, by simp [h, hk]⟩
  · rintro (rfl | ⟨k, hk⟩)
    · exact ⟨i, by simp⟩
    · by_cases h : i = k
      · simp [h] at hk
      · exact ⟨k, by simp_all⟩

end gmap

/-- Trillium's domain restriction `f ⇂ R` (stdpp `filter (λ '(k, v), k ∈ R) f`). -/
scoped notation:30 f " ⇂ " R => Std.ExtTreeMap.filter (fun k _ => decide (k ∈ R)) f

section DomRestrict

variable {X : Type _} [Ord X] [Std.TransOrd X] [Std.LawfulEqOrd X]

theorem mem_filter_iff {A : Type _} (m : GMap X A) (P : X → A → Bool) (k : X) :
    k ∈ m.filter P ↔ ∃ v, m[k]? = some v ∧ P k v = true := by
  rw [mem_iff_exists, Std.ExtTreeMap.getElem?_filter']
  cases m[k]? <;> simp

@[rocq_alias trillium.fairness.dom_domain_restrict]
theorem dom_domain_restrict {A : Type _} (f : GMap X A) (R : GSet X) :
    R ⊆ dom f → dom (f ⇂ R) = R := by
  intro hR
  ext i
  rw [mem_dom, mem_filter_iff]
  constructor
  · rintro ⟨_, _, h⟩; simpa using h
  · intro h
    obtain ⟨v, hv⟩ := mem_dom_iff.1 (hR i h)
    exact ⟨v, hv, by simpa using h⟩

@[rocq_alias trillium.fairness.dom_filter_sub]
theorem dom_filter_sub {V : Type _} (m : GMap X V) (ks : GSet X) :
    dom (m.filter fun k _ => decide (k ∈ ks)) ⊆ ks := by
  intro k hk
  rw [mem_dom, mem_filter_iff] at hk
  obtain ⟨_, _, h⟩ := hk
  simpa using h

@[rocq_alias trillium.fairness.dom_filter_comm]
theorem dom_filter_comm {A : Type _} (P : X → Prop) [DecidablePred P] :
    ∀ m : GMap X A, dom (m.filter fun k _ => decide (P k)) =
      FiniteSet.filter (fun k => decide (P k)) (dom m) := by
  intro m
  ext k
  rw [mem_dom, mem_filter_iff, FiniteSet.mem_filter, mem_dom, mem_iff_exists]
  simp only [decide_eq_true_eq]
  exact ⟨fun ⟨v, h1, h2⟩ => ⟨⟨v, h1⟩, h2⟩, fun ⟨⟨v, h1⟩, h2⟩ => ⟨v, h1, h2⟩⟩

@[rocq_alias trillium.fairness.dom_domain_restrict_union_l]
theorem dom_domain_restrict_union_l {A : Type _} (f : GMap X A) (R1 R2 : GSet X) :
    R1 ∪ R2 ⊆ dom f → dom (f ⇂ R1) = R1 :=
  fun h => dom_domain_restrict f R1 fun x hx => h x (LawfulSet.mem_union.2 (.inl hx))

@[rocq_alias trillium.fairness.dom_domain_restrict_union_r]
theorem dom_domain_restrict_union_r {A : Type _} (f : GMap X A) (R1 R2 : GSet X) :
    R1 ∪ R2 ⊆ dom f → dom (f ⇂ R2) = R2 :=
  fun h => dom_domain_restrict f R2 fun x hx => h x (LawfulSet.mem_union.2 (.inr hx))

/-- Note: core's `∪` is right-biased, but both sides agree here since the filters select the
same values. -/
@[rocq_alias trillium.fairness.gmap_filter_or]
theorem gmap_filter_or {A : Type _} (P1 P2 : X × A → Prop) [DecidablePred P1] [DecidablePred P2]
    (m : GMap X A) :
    m.filter (fun k v => decide (P1 (k, v) ∨ P2 (k, v))) =
      m.filter (fun k v => decide (P1 (k, v))) ∪ m.filter (fun k v => decide (P2 (k, v))) := by
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  rw [Std.ExtTreeMap.getElem?_union]
  simp only [Std.ExtTreeMap.getElem?_filter']
  cases m[k]? with
  | none => rfl
  | some a =>
    by_cases h1 : P1 (k, a) <;> by_cases h2 : P2 (k, a) <;> simp [Option.filter, h1, h2]

end DomRestrict

section MapsInverseMatch

variable {K V : Type _} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]
  [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V]

@[rocq_alias trillium.fairness.maps_inverse_match]
def mapsInverseMatch (m : GMap K V) (m' : GMap V (GSet K)) : Prop :=
  ∀ (k : K) (v : V), m[k]? = some v ↔ ∃ ks : GSet K, m'[v]? = some ks ∧ k ∈ ks

@[rocq_alias trillium.fairness.no_locale_empty]
theorem no_locale_empty (M : GMap K V) (M' : GMap V (GSet K)) (ρ : K) (ζ : V) :
    mapsInverseMatch M M' → M'[ζ]? = some ∅ → M[ρ]? ≠ some ζ := by
  intro Hinv Hem contra
  obtain ⟨ks, h1, h2⟩ := (Hinv ρ ζ).1 contra
  rw [Hem] at h1
  cases h1
  exact LawfulSet.mem_empty h2

@[rocq_alias trillium.fairness.maps_inverse_bij]
theorem maps_inverse_bij (M : GMap K V) (M' : GMap V (GSet K)) (ρ : K) (X1 X2 : GSet K)
    (ζ ζ' : V) :
    mapsInverseMatch M M' → M'[ζ]? = some X1 → ρ ∈ X1 → M'[ζ']? = some X2 → ρ ∈ X2 →
      ζ = ζ' := by
  intro Hinv Hζ Hρ Hζ' Hρ'
  have h1 : M[ρ]? = some ζ := (Hinv ρ ζ).2 ⟨X1, Hζ, Hρ⟩
  have h2 : M[ρ]? = some ζ' := (Hinv ρ ζ').2 ⟨X2, Hζ', Hρ'⟩
  rw [h1] at h2
  exact Option.some.inj h2

@[rocq_alias trillium.fairness.maps_inverse_match_exact]
theorem mapsInverseMatch_exact (v : V) (S : GSet K) :
    mapsInverseMatch (GSet.toGMap v S) (GMap.singleton v S) := by
  intro k v'
  rw [GSet.getElem?_toGMap, getElem?_singleton]
  by_cases hk : k ∈ S <;> by_cases hv : v = v' <;> simp [hk, hv]

@[rocq_alias trillium.fairness.maps_inverse_match_uniq1]
theorem mapsInverseMatch_uniq1 (m1 m2 : GMap K V) (m' : GMap V (GSet K))
    (M1 : mapsInverseMatch m1 m') (M2 : mapsInverseMatch m2 m') : m1 = m2 := by
  apply Std.ExtTreeMap.ext_getElem?
  intro i
  cases L1 : m1[i]? with
  | some v => exact ((M2 i v).2 ((M1 i v).1 L1)).symm
  | none =>
    cases L2 : m2[i]? with
    | none => rfl
    | some v => exact absurd ((M1 i v).2 ((M2 i v).1 L2)) (by simp [L1])

@[rocq_alias trillium.fairness.maps_inverse_match_subseteq]
theorem mapsInverseMatch_subseteq (m1 m2 : GMap K V) (m1' m2' : GMap V (GSet K))
    (M1 : mapsInverseMatch m1 m1') (M2 : mapsInverseMatch m2 m2')
    (SUB : dom m1' ⊆ dom m2')
    (INCL : ∀ (v : V) (S1 S2 : GSet K), m1'[v]? = some S1 → m2'[v]? = some S2 → S1 ⊆ S2) :
    m1 ⊆ m2 := by
  intro k v h
  obtain ⟨S1, L1, hk⟩ := (M1 k v).1 h
  obtain ⟨S2, L2⟩ := mem_dom_iff.1 (SUB v (mem_dom_iff.2 ⟨S1, L1⟩))
  exact (M2 k v).2 ⟨S2, L2, INCL v S1 S2 L1 L2 k hk⟩

@[rocq_alias trillium.fairness.mim_in_1]
theorem mim_in_1 (m : GMap K V) (m' : GMap V (GSet K)) (k : K) (v : V)
    (MIM : mapsInverseMatch m m') (DOM : m[k]? = some v) : v ∈ dom m' := by
  obtain ⟨ks, h, _⟩ := (MIM k v).1 DOM
  exact mem_dom_iff.2 ⟨ks, h⟩

@[rocq_alias trillium.fairness.mim_in_2]
theorem mim_in_2 (m : GMap K V) (m' : GMap V (GSet K)) (k : K) (v : V)
    (MIM : mapsInverseMatch m m') (IN : k ∈ (m'[v]?).getD ∅) : k ∈ dom m := by
  cases TM : m'[v]? with
  | none => rw [TM] at IN; exact absurd IN LawfulSet.mem_empty
  | some ks =>
    rw [TM] at IN
    exact mem_dom_iff.2 ⟨v, (MIM k v).2 ⟨ks, TM, IN⟩⟩

@[rocq_alias trillium.fairness.mim_lookup_helper]
theorem mim_lookup_helper (tm : GMap V (GSet K)) (m : GMap K V) (R : GSet K) (ζ : V)
    (MIM : mapsInverseMatch m tm) (NE : R ≠ ∅)
    (DOM : ∀ ρ, m[ρ]? = some ζ ↔ ρ ∈ R) : tm[ζ]? = some R := by
  obtain ⟨k, INR⟩ := LawfulSet.nonempty_iff.1 NE
  obtain ⟨R', TM', _⟩ := (MIM k ζ).1 ((DOM k).2 INR)
  rw [TM']
  congr 1
  ext k'
  rw [← DOM, MIM k' ζ]
  constructor
  · intro h; exact ⟨R', TM', h⟩
  · rintro ⟨ks, h, hk⟩; rw [TM'] at h; cases h; exact hk

@[rocq_alias trillium.fairness.mim_neg]
theorem mim_neg (m : GMap K V) (tm : GMap V (GSet K)) (MIM : mapsInverseMatch m tm) :
    ∀ k : K, m[k]? = none ↔ ∀ g : V, k ∉ (tm[g]?).getD ∅ := by
  intro k
  constructor
  · intro MAP g IN
    cases TM : tm[g]? with
    | none => rw [TM] at IN; exact LawfulSet.mem_empty IN
    | some ks =>
      rw [TM] at IN
      rw [(MIM k g).2 ⟨ks, TM, IN⟩] at MAP
      cases MAP
  · intro NIN
    cases MAP : m[k]? with
    | none => rfl
    | some v =>
      obtain ⟨ks, h1, h2⟩ := (MIM k v).1 MAP
      have := NIN v
      rw [h1] at this
      exact absurd h2 this

end MapsInverseMatch

section fin_map_dom

variable {K : Type _} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]

/-- stdpp's `dom_empty_iff` and its Leibniz variant `dom_empty_iff_L` (set equivalence is
equality here). -/
@[rocq_alias trillium.fairness.dom_empty_iff, rocq_alias trillium.fairness.dom_empty_iff_L]
theorem dom_empty_iff {A : Type _} (m : GMap K A) : dom m = ∅ ↔ m = ∅ := by
  rw [LawfulSet.eq_empty_iff, eq_empty_iff]
  simp only [mem_dom, not_mem_iff]

end fin_map_dom

section map_imap

variable {K : Type _} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]

@[rocq_alias trillium.fairness.map_imap_dom_inclusion]
theorem map_imap_dom_inclusion {A B : Type _} (f : K → A → Option B) (m : GMap K A) :
    dom (m.filterMap f) ⊆ dom m := by
  intro i hi
  rw [mem_dom_iff, Std.ExtTreeMap.getElem?_filterMap'] at hi
  obtain ⟨b, hb⟩ := hi
  cases h : m[i]? with
  | none => rw [h] at hb; cases hb
  | some a => exact mem_dom_iff.2 ⟨a, h⟩

@[rocq_alias trillium.fairness.map_imap_dom_eq]
theorem map_imap_dom_eq {A B : Type _} (f : K → A → Option B) (m : GMap K A) :
    (∀ k a, k ∈ dom m → (f k a).isSome) → dom (m.filterMap f) = dom m := by
  intro HisSome
  apply LawfulSet.eq_subset (map_imap_dom_inclusion f m)
  intro i hi
  obtain ⟨a, ha⟩ := mem_dom_iff.1 hi
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (HisSome i a hi)
  rw [mem_dom_iff, Std.ExtTreeMap.getElem?_filterMap', ha]
  exact ⟨b, hb⟩

end map_imap

section TmapDisj

variable {K V : Type _} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]
  [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V]

@[rocq_alias trillium.fairness.tmap_disj]
def tmapDisj (tm : GMap K (GSet V)) : Prop :=
  ∀ (k1 k2 : K) (S1 S2 : GSet V), k1 ≠ k2 → tm[k1]? = some S1 → tm[k2]? = some S2 → S1 ## S2

@[rocq_alias trillium.fairness.tmap_disj_dec]
instance tmapDisj_dec (tm : GMap K (GSet V)) : Decidable (tmapDisj tm) :=
  letI : DecidableEq K := fun a b =>
    decidable_of_iff (compare a b = .eq) Std.LawfulEqOrd.compare_eq_iff_eq
  letI : DecidableEq V := fun a b =>
    decidable_of_iff (compare a b = .eq) Std.LawfulEqOrd.compare_eq_iff_eq
  decidable_of_iff (∀ p ∈ tm.toList, ∀ q ∈ tm.toList, p.1 ≠ q.1 → p.2 ## q.2) <| by
    simp only [Prod.forall, Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some, tmapDisj]
    exact ⟨fun h k1 k2 S1 S2 ne h1 h2 => h k1 S1 h1 k2 S2 h2 ne,
      fun h k1 S1 h1 k2 S2 h2 ne => h k1 k2 S1 S2 ne h1 h2⟩

end TmapDisj

@[rocq_alias trillium.fairness.map_nat_agree_valid]
theorem map_nat_agree_valid {M : Type _ → Type _} [LawfulPartialMap M Nat] {A : Type _} [OFE A]
    (m : M A) : ✓ (Iris.Std.PartialMap.map (M := M) toAgree m) := by
  intro k
  simp only [Iris.Std.PartialMap.map, get?_bindAlter]
  cases get? m k with
  | none => trivial
  | some a => exact Agree.toAgree_valid (a := a)

end Fairness

end Trillium
