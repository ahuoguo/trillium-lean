/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.Std.Maps

/-!
# Pointwise relations between finite maps
Port of `fairis/map_included_utils.v`.

Lemmas about stdpp's `map_included R m1 m2` (every key of `m1` is a key of `m2`, with related
values) and Trillium's `map_agree_R R m1 m2` (same keys, related values).

Representation decisions:
* stdpp's `option_relation`, `map_relation` and `map_included` are not part of Trillium; they are
  defined here as `Trillium.optionRelation`, `Trillium.mapRelation` and `Trillium.mapIncluded` on
  `Trillium.GMap` (with the key-indexed relation, as in stdpp).
* The Rocq lemmas stated for an arbitrary `MAP` with a `Lookup` instance are stated for `GMap`.
* `f <$> m` is `m.map (fun _ => f)`; `filter P m` (with `P : K * A → Prop`) is
  `m.filter (fun k x => decide (P (k, x)))`.
* `dom m1 ⊆ dom m2` is stated as `∀ k, k ∈ m1 → k ∈ m2`, `dom m1 = dom m2` as
  `∀ k, k ∈ m1 ↔ k ∈ m2`, `k ∉ dom m` as `k ∉ m`, and `m1 ##ₘ m2` as `∀ k, k ∈ m1 → k ∉ m2`
  (membership in `Std.ExtTreeMap`).
* `∪` is `Std.ExtTreeMap`'s union, which is *right*-biased (stdpp's is left-biased); all unions
  in this file are of disjoint maps, where the two agree.
-/

#rocq_ignore_file trillium.fairis "fairness.v" "Entirely commented out in the Rocq development."

set_option linter.unusedSectionVars false

namespace Trillium

/-- stdpp's `option_relation R P Q`. -/
def optionRelation {A B : Type _} (R : A → B → Prop) (P : A → Prop) (Q : B → Prop) :
    Option A → Option B → Prop
  | some x, some y => R x y
  | some x, none => P x
  | none, some y => Q y
  | none, none => True

variable {K : Type _} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]

/-- stdpp's `map_relation R P Q m1 m2`. -/
def mapRelation {A B : Type _} (R : K → A → B → Prop) (P : K → A → Prop) (Q : K → B → Prop)
    (m1 : GMap K A) (m2 : GMap K B) : Prop :=
  ∀ i, optionRelation (R i) (P i) (Q i) m1[i]? m2[i]?

/-- stdpp's `map_included R m1 m2`: every binding of `m1` has an `R`-related binding in `m2`. -/
def mapIncluded {A B : Type _} (R : K → A → B → Prop) (m1 : GMap K A) (m2 : GMap K B) : Prop :=
  mapRelation R (fun _ _ => False) (fun _ _ => True) m1 m2

namespace Fairis

open Std

section

variable {A : Type _}

open Classical in
private theorem getElem?_insert_eq_ite {m : GMap K A} {i k : K} {x : A} :
    (m.insert i x)[k]? = if i = k then some x else m[k]? := by
  rw [ExtTreeMap.getElem?_insert]
  by_cases h : i = k <;> simp [h]

open Classical in
private theorem getElem?_erase_eq_ite {m : GMap K A} {i k : K} :
    (m.erase i)[k]? = if i = k then none else m[k]? := by
  rw [ExtTreeMap.getElem?_erase]
  by_cases h : i = k <;> simp [h]

private theorem mem_iff_exists {m : GMap K A} {k : K} : k ∈ m ↔ ∃ v, m[k]? = some v := by
  rw [ExtTreeMap.mem_iff_isSome_getElem?, Option.isSome_iff_exists]

@[rocq_alias trillium.fairis.map_included_spec]
theorem mapIncluded_spec (R : A → A → Prop) (m1 m2 : GMap K A) :
    mapIncluded (fun _ => R) m1 m2 ↔
      ∀ (k : K) (v1 : A), m1[k]? = some v1 → ∃ v2, m2[k]? = some v2 ∧ R v1 v2 := by
  constructor
  · intro HR k v1 Hv1
    have := HR k
    rw [Hv1] at this
    revert this
    cases m2[k]? with
    | none => intro h; exact h.elim
    | some a => intro h; exact ⟨a, rfl, h⟩
  · intro HR k
    cases Heqn : m1[k]? with
    | some v1 =>
      obtain ⟨v2, Hv2, HR'⟩ := HR k v1 Heqn
      rw [Hv2]; exact HR'
    | none => cases m2[k]? <;> trivial

@[rocq_alias trillium.fairis.map_included_insert]
theorem mapIncluded_insert (R : A → A → Prop) (m1 m2 : GMap K A) (i : K) (x y : A) :
    R x y → mapIncluded (fun _ => R) m1 m2 →
      mapIncluded (fun _ => R) (m1.insert i x) (m2.insert i y) := by
  intro HR Hle k
  simp only [getElem?_insert_eq_ite]
  by_cases h : i = k
  · simp only [h, ↓reduceIte]; exact HR
  · simp only [h, ↓reduceIte]; exact Hle k

@[rocq_alias trillium.fairis.map_included_refl]
theorem mapIncluded_refl {R : A → A → Prop} [Std.Refl R] (m : GMap K A) :
    mapIncluded (fun _ => R) m m := by
  rw [mapIncluded_spec]
  intro k v1 h
  exact ⟨v1, h, Std.Refl.refl v1⟩

@[rocq_alias trillium.fairis.map_included_subseteq]
theorem mapIncluded_subseteq (R : A → A → Prop) (m1 m2 m3 : GMap K A) :
    (∀ (k : K) (v : A), m1[k]? = some v → m2[k]? = some v) →
      mapIncluded (fun _ => R) m2 m3 → mapIncluded (fun _ => R) m1 m3 := by
  rw [mapIncluded_spec, mapIncluded_spec]
  intro Hle1 Hle2 k v1 HSome
  exact Hle2 k v1 (Hle1 k v1 HSome)

@[rocq_alias trillium.fairis.map_included_subseteq_inv]
theorem mapIncluded_subseteq_inv (R : A → A → Prop) (m1 m2 : GMap K A) :
    mapIncluded (fun _ => R) m1 m2 → ∀ k, k ∈ m1 → k ∈ m2 := by
  rw [mapIncluded_spec]
  intro Hle k
  rw [mem_iff_exists, mem_iff_exists]
  rintro ⟨v1, Heq⟩
  obtain ⟨v2, Hv2, -⟩ := Hle k v1 Heq
  exact ⟨v2, Hv2⟩

@[rocq_alias trillium.fairis.map_included_transitivity]
theorem mapIncluded_transitivity {R : A → A → Prop} [IsTrans A R] (m1 m2 m3 : GMap K A) :
    mapIncluded (fun _ => R) m1 m2 → mapIncluded (fun _ => R) m2 m3 →
      mapIncluded (fun _ => R) m1 m3 := by
  rw [mapIncluded_spec, mapIncluded_spec, mapIncluded_spec]
  intro Hle1 Hle2 k v1 HSome
  obtain ⟨v2, HSome, HR⟩ := Hle1 k v1 HSome
  obtain ⟨v3, HSome, HR'⟩ := Hle2 k v2 HSome
  exact ⟨v3, HSome, IsTrans.trans _ _ _ HR HR'⟩

@[rocq_alias trillium.fairis.map_included_fmap]
theorem mapIncluded_fmap (R : A → A → Prop) (m : GMap K A) (f : A → A) :
    (∀ x, R x (f x)) → mapIncluded (fun _ => R) m (m.map fun _ => f) := by
  intro Hf k
  rw [ExtTreeMap.getElem?_map]
  cases m[k]? with
  | some x => exact Hf x
  | none => trivial

@[rocq_alias trillium.fairis.map_included_mono]
theorem mapIncluded_mono (R : A → A → Prop) (m1 m2 : GMap K A) (f : A → A) :
    (∀ x1 x2, R x1 x2 → R (f x1) (f x2)) →
      mapIncluded (fun _ => R) m1 m2 →
      mapIncluded (fun _ => R) (m1.map fun _ => f) (m2.map fun _ => f) := by
  rw [mapIncluded_spec, mapIncluded_spec]
  intro Hf Hle k v1 HSome
  rw [ExtTreeMap.getElem?_map, Option.map_eq_some_iff] at HSome
  obtain ⟨v1', HSome, rfl⟩ := HSome
  obtain ⟨v2', HSome2, Hv2⟩ := Hle k v1' HSome
  exact ⟨f v2', by rw [ExtTreeMap.getElem?_map, HSome2]; rfl, Hf _ _ Hv2⟩

@[rocq_alias trillium.fairis.map_included_mono_strong]
theorem mapIncluded_mono_strong (R : A → A → Prop) (m1 m2 : GMap K A)
    (f1 f2 : GMap K A → GMap K A) :
    (∀ k, k ∈ f1 m1 → k ∈ m1) → (∀ k, k ∈ m2 → k ∈ f2 m2) →
      (∀ (k : K) (x1 x2 y1 y2 : A), m1[k]? = some x1 → m2[k]? = some x2 →
        (f1 m1)[k]? = some y1 → (f2 m2)[k]? = some y2 → R x1 x2 → R y1 y2) →
      mapIncluded (fun _ => R) m1 m2 →
      mapIncluded (fun _ => R) (f1 m1) (f2 m2) := by
  rw [mapIncluded_spec, mapIncluded_spec]
  intro Hle1 Hle2 Hf HR k v1 HSome1
  obtain ⟨v1', HSome1'⟩ := mem_iff_exists.mp (Hle1 k (mem_iff_exists.mpr ⟨v1, HSome1⟩))
  obtain ⟨v2', HSome2', Hv2'⟩ := HR k v1' HSome1'
  obtain ⟨v2, HSome2⟩ := mem_iff_exists.mp (Hle2 k (mem_iff_exists.mpr ⟨v2', HSome2'⟩))
  exact ⟨v2, HSome2, Hf k _ _ _ _ HSome1' HSome2' HSome1 HSome2 Hv2'⟩

@[rocq_alias trillium.fairis.map_included_filter]
theorem mapIncluded_filter (R : A → A → Prop) (m1 m2 : GMap K A) (P : K × A → Prop)
    [DecidablePred P] :
    (∀ (k : K) (x1 x2 : A), m1[k]? = some x1 → m2[k]? = some x2 → P (k, x1) → P (k, x2)) →
      mapIncluded (fun _ => R) m1 m2 →
      mapIncluded (fun _ => R) (m1.filter fun k x => decide (P (k, x)))
        (m2.filter fun k x => decide (P (k, x))) := by
  rw [mapIncluded_spec, mapIncluded_spec]
  intro HP Hle k v1 HSome1
  rw [ExtTreeMap.getElem?_filter', Option.filter_eq_some_iff] at HSome1
  obtain ⟨HSome1, HP'⟩ := HSome1
  obtain ⟨v2, HSome2, HR⟩ := Hle k v1 HSome1
  have HP2 := HP k v1 v2 HSome1 HSome2 (of_decide_eq_true HP')
  refine ⟨v2, ?_, HR⟩
  rw [ExtTreeMap.getElem?_filter', Option.filter_eq_some_iff]
  exact ⟨HSome2, decide_eq_true HP2⟩

@[rocq_alias trillium.fairis.map_included_subseteq_r]
theorem mapIncluded_subseteq_r (R : A → A → Prop) (m1 m2 m3 : GMap K A) :
    (∀ (k : K) (v : A), m2[k]? = some v → m3[k]? = some v) →
      mapIncluded (fun _ => R) m1 m2 → mapIncluded (fun _ => R) m1 m3 := by
  rw [mapIncluded_spec, mapIncluded_spec]
  intro Hle1 Hle2 k v1 HSome
  obtain ⟨v2, HSome, HR⟩ := Hle2 k v1 HSome
  exact ⟨v2, Hle1 k v2 HSome, HR⟩

end

/-- Trillium's `map_agree_R R m1 m2`: `m1` and `m2` have the same keys and `R`-related values. -/
@[rocq_alias trillium.fairis.map_agree_R]
def mapAgreeR {A B : Type _} (R : A → B → Prop) (m1 : GMap K A) (m2 : GMap K B) : Prop :=
  mapRelation (fun _ => R) (fun _ _ => False) (fun _ _ => False) m1 m2

section

variable {A : Type _}

@[rocq_alias trillium.fairis.map_agree_R_spec]
theorem mapAgreeR_spec (R : A → A → Prop) (m1 m2 : GMap K A) :
    mapAgreeR R m1 m2 ↔
      (∀ (k : K) (v1 : A), m1[k]? = some v1 → ∃ v2, m2[k]? = some v2 ∧ R v1 v2) ∧
      (∀ (k : K) (v2 : A), m2[k]? = some v2 → ∃ v1, m1[k]? = some v1 ∧ R v1 v2) := by
  constructor
  · intro HR
    constructor
    · intro k v HSome
      have := HR k
      rw [HSome] at this
      revert this
      cases m2[k]? with
      | none => intro h; exact h.elim
      | some a => intro h; exact ⟨a, rfl, h⟩
    · intro k v HSome
      have := HR k
      rw [HSome] at this
      revert this
      cases m1[k]? with
      | none => intro h; exact h.elim
      | some a => intro h; exact ⟨a, rfl, h⟩
  · rintro ⟨HR1, HR2⟩ k
    cases Heqn1 : m1[k]? with
    | some v1 =>
      obtain ⟨v2, Hv2, HR⟩ := HR1 k v1 Heqn1
      rw [Hv2]; exact HR
    | none =>
      cases Heqn2 : m2[k]? with
      | some v2 =>
        obtain ⟨v1, Hv1, -⟩ := HR2 k v2 Heqn2
        rw [Heqn1] at Hv1; cases Hv1
      | none => trivial

@[rocq_alias trillium.fairis.map_included_delete]
theorem mapIncluded_delete (R : A → A → Prop) (m1 m2 : GMap K A) (k : K) :
    mapIncluded (fun _ => R) m1 m2 →
      mapIncluded (fun _ => R) (m1.erase k) (m2.erase k) := by
  rw [mapIncluded_spec, mapIncluded_spec]
  intro Hle k' v HSome
  rw [getElem?_erase_eq_ite] at HSome ⊢
  split at HSome
  · cases HSome
  · rename_i h
    simpa [h] using Hle k' v HSome

@[rocq_alias trillium.fairis.map_agree_R_dom]
theorem mapAgreeR_dom (R : A → A → Prop) (m1 m2 : GMap K A) :
    mapAgreeR R m1 m2 → ∀ k, k ∈ m1 ↔ k ∈ m2 := by
  rw [mapAgreeR_spec]
  rintro ⟨Hle1, Hle2⟩ k
  rw [mem_iff_exists, mem_iff_exists]
  constructor
  · rintro ⟨v1, HSome1⟩
    obtain ⟨v2, HSome2, -⟩ := Hle1 k v1 HSome1
    exact ⟨v2, HSome2⟩
  · rintro ⟨v2, HSome2⟩
    obtain ⟨v1, HSome1, -⟩ := Hle2 k v2 HSome2
    exact ⟨v1, HSome1⟩

@[rocq_alias trillium.fairis.map_agree_R_insert]
theorem mapAgreeR_insert (R : A → A → Prop) (m1 m2 : GMap K A) (k : K) (v1 v2 : A) :
    R v1 v2 → mapAgreeR R m1 m2 → mapAgreeR R (m1.insert k v1) (m2.insert k v2) := by
  intro HR Hle k'
  simp only [getElem?_insert_eq_ite]
  by_cases h : k = k'
  · simp only [h, ↓reduceIte]; exact HR
  · simp only [h, ↓reduceIte]; exact Hle k'

@[rocq_alias trillium.fairis.map_agree_R_insert_inv]
theorem mapAgreeR_insert_inv (R : A → A → Prop) (m1 m2 : GMap K A) (k : K) (v1 v2 : A) :
    k ∉ m1 → k ∉ m2 → mapAgreeR R (m1.insert k v1) (m2.insert k v2) → mapAgreeR R m1 m2 := by
  intro Hnin1 Hnin2 Hle k'
  have := Hle k'
  simp only [getElem?_insert_eq_ite] at this
  by_cases h : k = k'
  · subst h
    rw [ExtTreeMap.getElem?_eq_none Hnin1, ExtTreeMap.getElem?_eq_none Hnin2]
    trivial
  · simpa [h] using this

@[rocq_alias trillium.fairis.map_agree_R_agree]
theorem mapAgreeR_agree (R : A → A → Prop) (m1 m2 : GMap K A) (k : K) (v1 v2 : A) :
    m1[k]? = some v1 → m2[k]? = some v2 → mapAgreeR R m1 m2 → R v1 v2 := by
  intro HSome1 HSome2 Hle
  have := Hle k
  rw [HSome1, HSome2] at this
  exact this

@[rocq_alias trillium.fairis.map_included_R_agree]
theorem mapIncluded_R_agree (R : A → A → Prop) (m1 m2 : GMap K A) (k : K) (v1 v2 : A) :
    m1[k]? = some v1 → m2[k]? = some v2 → mapIncluded (fun _ => R) m1 m2 → R v1 v2 := by
  intro HSome1 HSome2 Hle
  have := Hle k
  rw [HSome1, HSome2] at this
  exact this

/- The Rocq proof goes by induction on `m2`; here we directly split `m2` into the part whose
keys are in `m1` and the rest. -/
@[rocq_alias trillium.fairis.map_included_map_agree_R]
theorem mapIncluded_mapAgreeR (R : A → A → Prop) (m1 m2 : GMap K A) :
    mapIncluded (fun _ => R) m1 m2 →
      ∃ m21 m22 : GMap K A, m2 = m21 ∪ m22 ∧ (∀ k, k ∈ m21 → k ∉ m22) ∧
        mapAgreeR R m1 m21 := by
  intro Hle
  refine ⟨m2.filter (fun k _ => m1.contains k), m2.filter (fun k _ => !m1.contains k),
    ?_, ?_, ?_⟩
  · ext k : 1
    rw [ExtTreeMap.getElem?_union, ExtTreeMap.getElem?_filter', ExtTreeMap.getElem?_filter']
    cases m2[k]? <;> cases m1.contains k <;> rfl
  · intro k H1 H2
    rw [ExtTreeMap.mem_iff_isSome_getElem?, ExtTreeMap.getElem?_filter'] at H1 H2
    cases h : m2[k]? <;> cases h' : m1.contains k <;> simp_all
  · intro k
    have := Hle k
    rw [ExtTreeMap.getElem?_filter']
    cases h1 : m1[k]? with
    | none =>
      have : m1.contains k = false := by
        rw [ExtTreeMap.contains_eq_isSome_getElem?, h1]; rfl
      cases m2[k]? <;> simp [optionRelation, this]
    | some v1 =>
      have hc : m1.contains k = true := by
        rw [ExtTreeMap.contains_eq_isSome_getElem?, h1]; rfl
      rw [h1] at this
      cases h2 : m2[k]? with
      | none => rw [h2] at this; exact this.elim
      | some v2 => rw [h2] at this; simpa [optionRelation, hc, Option.filter_some] using this

@[rocq_alias trillium.fairis.map_agree_R_map_included]
theorem mapAgreeR_mapIncluded (R : A → A → Prop) (m1 m2 : GMap K A) :
    mapAgreeR R m1 m2 → mapIncluded (fun _ => R) m1 m2 := by
  rw [mapIncluded_spec, mapAgreeR_spec]
  exact fun H => H.1

@[rocq_alias trillium.fairis.map_agree_R_union_inv]
theorem mapAgreeR_union_inv (R : A → A → Prop) (m11 m12 m2 : GMap K A) :
    (∀ k, k ∈ m11 → k ∉ m12) →
      mapAgreeR R (m11 ∪ m12) m2 →
      ∃ m21 m22 : GMap K A, m2 = m21 ∪ m22 ∧ mapAgreeR R m11 m21 ∧ mapAgreeR R m12 m22 := by
  intro Hdisj Hle
  refine ⟨m2.filter (fun k _ => m11.contains k), m2.filter (fun k _ => !m11.contains k),
    ?_, ?_, ?_⟩
  · ext k : 1
    rw [ExtTreeMap.getElem?_union, ExtTreeMap.getElem?_filter', ExtTreeMap.getElem?_filter']
    cases m2[k]? <;> cases m11.contains k <;> rfl
  all_goals
    intro k
    have H := Hle k
    have Hd := Hdisj k
    rw [ExtTreeMap.getElem?_union] at H
    rw [ExtTreeMap.getElem?_filter']
    rw [ExtTreeMap.mem_iff_isSome_getElem?, ExtTreeMap.mem_iff_isSome_getElem?] at Hd
    rw [ExtTreeMap.contains_eq_isSome_getElem?]
    cases h11 : m11[k]? <;> cases h12 : m12[k]? <;> cases h2 : m2[k]? <;>
      simp_all [optionRelation, Option.filter_some]

/-- The Rocq proof goes by induction on `m2`; here we directly construct the preimage map with
choice. -/
@[rocq_alias trillium.fairis.map_agree_R_fmap_inv]
theorem mapAgreeR_fmap_inv (R : A → A → Prop) (m1 m2 : GMap K A) (f : A → A) :
    (∀ v1 v2, R (f v1) v2 → ∃ v2', v2 = f v2') →
      mapAgreeR R (m1.map fun _ => f) m2 →
      ∃ m2' : GMap K A, m2 = m2'.map fun _ => f := by
  classical
  intro Hf Hle
  refine ⟨m2.filterMap fun _ v => if h : ∃ v', v = f v' then some h.choose else none, ?_⟩
  ext k : 1
  rw [ExtTreeMap.getElem?_map, ExtTreeMap.getElem?_filterMap]
  cases h2 : m2[k]? with
  | none => rfl
  | some v2 =>
    obtain ⟨v1, HSome1, HR⟩ := (mapAgreeR_spec R _ _).mp Hle |>.2 k v2 h2
    rw [ExtTreeMap.getElem?_map, Option.map_eq_some_iff] at HSome1
    obtain ⟨v1', -, rfl⟩ := HSome1
    have hex := Hf v1' v2 HR
    simp only [Option.pbind_some, hex, dite_true, Option.map_some]
    exact congrArg some hex.choose_spec

@[rocq_alias trillium.fairis.map_agree_R_fmap]
theorem mapAgreeR_fmap (R : A → A → Prop) (m1 m2 : GMap K A) (f : A → A) :
    (∀ v1 v2, R (f v1) (f v2) → R v1 v2) →
      mapAgreeR R (m1.map fun _ => f) (m2.map fun _ => f) → mapAgreeR R m1 m2 := by
  intro Hf Hle k
  have := Hle k
  rw [ExtTreeMap.getElem?_map, ExtTreeMap.getElem?_map] at this
  revert this
  cases m1[k]? <;> cases m2[k]? <;> intro this <;> first | exact this | exact Hf _ _ this

end

end Fairis

end Trillium
