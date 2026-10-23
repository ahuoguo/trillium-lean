/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.Std.Maps
import Trillium.Fairness.UtilsLogic
import Iris.Std.GenSets
import Mathlib.Data.Multiset.Basic

/-!
# Set helpers
Port of `fairness/utils_sets.v`.

Representation decisions:
* `gset K` is `Trillium.GSet K` (`Std.ExtTreeSet K compare`). We use iris-lean's
  `LawfulSet`/`FiniteSet` interface on it, which supplies stdpp's set vocabulary:
  `⊆`, `X ## Y` (disjointness), `FiniteSet.map` (stdpp's `set_map`), `FiniteSet.filter`
  (stdpp's `filter`, with a `Bool`-valued predicate), `LawfulSet.ofList` (`list_to_set`),
  `FiniteSet.toList` (`elements`, definitionally `Std.ExtTreeSet.toList`) and
  `LawfulSet.setForall` (`set_Forall`). Core `Std.ExtTreeSet` lemmas apply as well.
* stdpp's generic `FinSet A C` lemmas are stated for any `LawfulFiniteSet S A`.
* `gset (gset K)` needs an order on `GSet K`; we provide `Trillium.GSet.instOrd`, comparing the
  sorted element lists.
* `gset_to_gmap b X` is `Trillium.GSet.toGMap b X`.
* `gmultiset A` is Mathlib's `Multiset A`.
-/

namespace Trillium

open Iris.Std

namespace GSet

variable {K : Type _} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]

/-- Order on finite sets, comparing their (sorted) lists of elements lexicographically. This is
used to form sets of sets (`GSet (GSet K)`). -/
instance instOrd : Ord (GSet K) := ⟨fun s t => compare s.toList t.toList⟩

instance instTransOrd : Std.TransOrd (GSet K) where
  eq_swap := Std.OrientedCmp.eq_swap (cmp := (compare : List K → List K → Ordering))
  isLE_trans := Std.TransCmp.isLE_trans (cmp := (compare : List K → List K → Ordering))

instance instLawfulEqOrd : Std.LawfulEqOrd (GSet K) where
  compare_self {s} := Std.ReflCmp.compare_self (cmp := (compare : List K → List K → Ordering))
  eq_of_compare {s t} h := by
    have h' : s.toList = t.toList :=
      Std.LawfulEqCmp.eq_of_compare (cmp := (compare : List K → List K → Ordering)) h
    exact (FiniteSet.toList_eq_iff (s₁ := s) (s₂ := t)) ▸ h'

/-- stdpp's `gset_to_gmap b X`: the map sending every element of `X` to `b`. -/
def toGMap {V : Type _} (b : V) (X : GSet K) : GMap K V := X.inner.map fun _ _ => b

omit [Std.LawfulEqOrd K] in
theorem mem_iff_mem_inner {X : GSet K} {k : K} : k ∈ X ↔ k ∈ X.inner := by
  rw [Std.ExtTreeSet.mem_iff_contains, Std.ExtTreeMap.mem_iff_contains]; rfl

open Classical in
@[simp]
theorem getElem?_toGMap {V : Type _} (b : V) (X : GSet K) (k : K) :
    (toGMap b X)[k]? = if k ∈ X then some b else none := by
  have h := (mem_iff_mem_inner (X := X) (k := k)).trans Std.ExtTreeMap.mem_iff_isSome_getElem?
  rw [toGMap, Std.ExtTreeMap.getElem?_map]
  split <;> rename_i hk
  · obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 (h.1 hk); simp [hu]
  · simp only [Option.map_eq_none_iff]
    exact Option.not_isSome_iff_eq_none.1 fun h' => hk (h.2 h')

end GSet

namespace Fairness

section SetMapProperties

variable {A1 A2 A3 : Type _} [Ord A1] [Std.TransOrd A1] [Std.LawfulEqOrd A1]
  [Ord A2] [Std.TransOrd A2] [Std.LawfulEqOrd A2] [Ord A3] [Std.TransOrd A3] [Std.LawfulEqOrd A3]

@[rocq_alias trillium.fairness.set_map_compose_gset]
theorem set_map_compose_gset (f : A2 → A3) (g : A1 → A2) (m : GSet A1) :
    (FiniteSet.map (f ∘ g) m : GSet A3) = FiniteSet.map f (FiniteSet.map g m : GSet A2) :=
  FiniteSet.map_comp g f m

@[rocq_alias trillium.fairness.elem_of_map_inj_gset]
theorem elem_of_map_inj_gset (f : A1 → A2) (m : GSet A1) (a : A1)
    (INJ : Function.Injective f) :
    a ∈ m ↔ f a ∈ (FiniteSet.map f m : GSet A2) := by
  rw [FiniteSet.mem_map]
  exact ⟨fun h => ⟨a, rfl, h⟩, fun ⟨a', e, h⟩ => INJ e ▸ h⟩

end SetMapProperties

section Powerset

variable {K : Type _} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]

/-- It's easier to perform recursion on lists. -/
@[rocq_alias trillium.fairness.powerlist]
def powerlist : List K → GSet (GSet K)
  | [] => {∅}
  | k :: l' =>
    let p' := powerlist l'
    p' ∪ FiniteSet.map (fun s => {k} ∪ s) p'

@[rocq_alias trillium.fairness.powerset]
def powerset (s : GSet K) : GSet (GSet K) := powerlist (FiniteSet.toList s)

@[rocq_alias trillium.fairness.powerlist_nil]
theorem powerlist_nil (l : List K) : (∅ : GSet K) ∈ powerlist l := by
  induction l with
  | nil => exact LawfulSet.mem_singleton.2 rfl
  | cons k l IH => exact LawfulSet.mem_union.2 (.inl IH)

/-- Membership in `powerlist l` only depends on the elements of `l`. -/
theorem mem_powerlist (l : List K) (e : GSet K) :
    e ∈ powerlist l ↔ ∀ x, x ∈ e → x ∈ l := by
  induction l generalizing e with
  | nil =>
    simp only [powerlist, LawfulSet.mem_singleton, List.not_mem_nil, imp_false]
    exact LawfulSet.eq_empty_iff
  | cons k l IH =>
    simp only [powerlist, LawfulSet.mem_union, FiniteSet.mem_map, IH, List.mem_cons]
    constructor
    · rintro (h | ⟨s, rfl, hs⟩)
      · exact fun x hx => .inr (h x hx)
      · intro x hx
        rcases LawfulSet.mem_union.1 hx with hx | hx
        · exact .inl (LawfulSet.mem_singleton.1 hx)
        · exact .inr (hs x hx)
    · intro h
      by_cases hk : k ∈ e
      · refine .inr ⟨e \ {k}, ?_, fun x hx => ?_⟩
        · ext x
          simp only [LawfulSet.mem_union, LawfulSet.mem_diff, LawfulSet.mem_singleton]
          by_cases hx : x = k
          · subst hx; simp [hk]
          · simp [hx]
        · rw [LawfulSet.mem_diff, LawfulSet.mem_singleton] at hx
          exact (h x hx.1).resolve_left hx.2
      · exact .inl fun x hx => (h x hx).resolve_left fun e' => hk (e' ▸ hx)

/-- Rocq's `Proper (Permutation ==> eq) powerlist`. -/
@[rocq_alias trillium.fairness.powerlist_perm_Proper]
theorem powerlist_perm_Proper {l l' : List K} (h : l.Perm l') : powerlist l = powerlist l' := by
  ext e
  simp only [mem_powerlist, h.mem_iff]

@[rocq_alias trillium.fairness.powerset_spec]
theorem powerset_spec (s : GSet K) : ∀ e, e ⊆ s ↔ e ∈ powerset s := by
  intro e
  rw [powerset, mem_powerlist]
  simp only [FiniteSet.mem_toList]
  rfl

end Powerset

section FinSet

variable {S A : Type _} [LawfulFiniteSet S A]

@[rocq_alias trillium.fairness.set_filter_equiv]
theorem set_filter_equiv (P1 P2 : A → Prop) [DecidablePred P1] [DecidablePred P2]
    (P_EQ : ∀ x, P1 x ↔ P2 x) (c1 c2 : S) (EQUIV : c1 = c2) :
    FiniteSet.filter (fun x => decide (P1 x)) c1 = FiniteSet.filter (fun x => decide (P2 x)) c2 := by
  subst EQUIV
  ext x
  simp [FiniteSet.mem_filter, P_EQ]

@[rocq_alias trillium.fairness.set_filter_and]
theorem set_filter_and (P1 P2 : A → Prop) [DecidablePred P1] [DecidablePred P2] (c : S) :
    FiniteSet.filter (fun x => decide (P1 x)) (FiniteSet.filter (fun x => decide (P2 x)) c) =
      FiniteSet.filter (fun x => decide (P1 x ∧ P2 x)) c := by
  ext x
  simp only [FiniteSet.mem_filter, decide_eq_true_eq]
  tauto

@[rocq_alias trillium.fairness.set_filter_comm]
theorem set_filter_comm (P1 P2 : A → Prop) [DecidablePred P1] [DecidablePred P2] (c : S) :
    FiniteSet.filter (fun x => decide (P1 x)) (FiniteSet.filter (fun x => decide (P2 x)) c) =
      FiniteSet.filter (fun x => decide (P2 x)) (FiniteSet.filter (fun x => decide (P1 x)) c) := by
  ext x
  simp only [FiniteSet.mem_filter, decide_eq_true_eq]
  tauto

@[rocq_alias trillium.fairness.filter_singleton_if]
theorem filter_singleton_if (P : A → Prop) [DecidablePred P] (x : A) :
    FiniteSet.filter (fun x => decide (P x)) ({x} : S) = if P x then {x} else ∅ := by
  rw [FiniteSet.filter_singleton]
  simp

@[rocq_alias trillium.fairness.set_Forall_subseteq]
theorem setForall_subseteq (P : A → Prop) (x y : S) (SUB : y ⊆ x) :
    LawfulSet.setForall P x → LawfulSet.setForall P y :=
  fun h a ha => h a (SUB a ha)

end FinSet

@[rocq_alias trillium.fairness.elements_list_to_set_disj]
theorem elements_list_to_set_disj {A : Type _} (l : List A) :
    (l : Multiset A).toList.Perm l :=
  Multiset.coe_eq_coe.1 (Multiset.coe_toList _)

section GSetLemmas

variable {K : Type _} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]

@[rocq_alias trillium.fairness.gset_filter_subseteq_mono_strong]
theorem gset_filter_subseteq_mono_strong (P Q : K → Prop) [DecidablePred P] [DecidablePred Q]
    (g : GSet K) (IMPL : ∀ x, x ∈ g → P x → Q x) :
    FiniteSet.filter (fun x => decide (P x)) g ⊆ FiniteSet.filter (fun x => decide (Q x)) g := by
  intro x hx
  simp only [FiniteSet.mem_filter, decide_eq_true_eq] at hx ⊢
  exact ⟨hx.1, IMPL x hx.1 hx.2⟩

@[rocq_alias trillium.fairness.gset_filter_True]
theorem gset_filter_true (g : GSet K) (P : K → Prop) [DecidablePred P]
    (TRUE : ∀ k, k ∈ g → P k) :
    FiniteSet.filter (fun x => decide (P x)) g = g := by
  ext x
  simp only [FiniteSet.mem_filter, decide_eq_true_eq]
  exact ⟨And.left, fun h => ⟨h, TRUE x h⟩⟩

#rocq_ignore trillium.fairness.GSet_inj_equiv
  "Setoid `Inj` instance for the `GSet` CMRA constructor; equality is Leibniz in Lean"
#rocq_ignore trillium.fairness.GSet_Proper
  "Setoid `Proper` instance for the `GSet` CMRA constructor; equality is Leibniz in Lean"

@[rocq_alias trillium.fairness.gset_not_elem_of_equiv_not_empty_L]
theorem gset_ne_empty_iff_exists_mem (X : GSet K) : X ≠ ∅ ↔ ∃ x, x ∈ X :=
  LawfulSet.nonempty_iff

@[rocq_alias trillium.fairness.length_size]
theorem length_size (g : GSet K) : (FiniteSet.toList g).length = g.size :=
  Std.ExtTreeSet.length_toList

end GSetLemmas

section FlattenGset

variable {K : Type _} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]

@[rocq_alias trillium.fairness.flatten_gset]
def flattenGSet (ss : GSet (GSet K)) : GSet K :=
  LawfulSet.ofList ((FiniteSet.toList ss).map FiniteSet.toList).flatten

@[rocq_alias trillium.fairness.flatten_gset_spec]
theorem flattenGSet_spec (ss : GSet (GSet K)) :
    ∀ k, k ∈ flattenGSet ss ↔ ∃ s, s ∈ ss ∧ k ∈ s := by
  intro k
  simp [flattenGSet, ← LawfulSet.mem_ofList, FiniteSet.mem_toList]

@[rocq_alias trillium.fairness.flatten_gset_disjoint]
theorem flattenGSet_disjoint (ss : GSet (GSet K)) (s' : GSet K) :
    flattenGSet ss ## s' ↔ ∀ s, s ∈ ss → s ## s' := by
  simp only [Iris.Std.Disjoint.disjoint, flattenGSet_spec]
  constructor
  · intro h s hs x ⟨h1, h2⟩; exact h x ⟨⟨s, hs, h1⟩, h2⟩
  · rintro h x ⟨⟨s, hs, h1⟩, h2⟩; exact h s hs x ⟨h1, h2⟩

@[rocq_alias trillium.fairness.flatten_gset_union]
theorem flattenGSet_union (S1 S2 : GSet (GSet K)) :
    flattenGSet (S1 ∪ S2) = flattenGSet S1 ∪ flattenGSet S2 := by
  ext k
  simp only [flattenGSet_spec, LawfulSet.mem_union]
  constructor
  · rintro ⟨s, hs | hs, hk⟩
    · exact .inl ⟨s, hs, hk⟩
    · exact .inr ⟨s, hs, hk⟩
  · rintro (⟨s, hs, hk⟩ | ⟨s, hs, hk⟩)
    · exact ⟨s, .inl hs, hk⟩
    · exact ⟨s, .inr hs, hk⟩

@[rocq_alias trillium.fairness.flatten_gset_singleton]
theorem flattenGSet_singleton (S : GSet K) : flattenGSet {S} = S := by
  ext k
  simp only [flattenGSet_spec, LawfulSet.mem_singleton]
  exact ⟨fun ⟨s, hs, hk⟩ => hs ▸ hk, fun hk => ⟨S, rfl, hk⟩⟩

@[rocq_alias trillium.fairness.flatten_gset_empty]
theorem flattenGSet_empty : flattenGSet ∅ = (∅ : GSet K) := by
  ext k
  simp only [flattenGSet_spec]
  exact ⟨fun ⟨_, hs, _⟩ => absurd hs LawfulSet.mem_empty, fun h => absurd h LawfulSet.mem_empty⟩

end FlattenGset

section GsetPick

variable {K : Type _} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]

@[rocq_alias trillium.fairness.gset_pick]
def gsetPick (g : GSet K) : Option K :=
  match FiniteSet.toList g with
  | [] => none
  | e :: _ => some e

@[rocq_alias trillium.fairness.gset_pick_None]
theorem gsetPick_none (g : GSet K) : gsetPick g = none ↔ g = ∅ := by
  rw [gsetPick, LawfulSet.eq_empty_iff]
  constructor
  · intro h x hx
    rw [← FiniteSet.mem_toList] at hx
    split at h
    · simp_all
    · simp at h
  · intro h
    split
    · rfl
    · rename_i e _ E
      exact absurd (FiniteSet.mem_toList.1 (E ▸ List.mem_cons_self)) (h e)

@[rocq_alias trillium.fairness.gset_pick_is_Some]
theorem gsetPick_isSome (g : GSet K) : (gsetPick g).isSome ↔ g ≠ ∅ := by
  rw [Option.isSome_iff_ne_none, Ne, Ne, gsetPick_none]

@[rocq_alias trillium.fairness.gset_pick_Some]
theorem gsetPick_some (g : GSet K) (k : K) : gsetPick g = some k → k ∈ g := by
  rw [gsetPick]
  split
  · simp
  · rename_i e _ E
    rintro ⟨⟩
    exact FiniteSet.mem_toList.1 (E ▸ List.mem_cons_self)

@[rocq_alias trillium.fairness.gset_pick_singleton]
theorem gsetPick_singleton (k : K) : gsetPick ({k} : GSet K) = some k := by
  rw [gsetPick, FiniteSet.toList_singleton]

end GsetPick

section ExtractSomes

variable {A : Type _}

@[rocq_alias trillium.fairness.extract_Somes]
def extractSomes (l : List (Option A)) : List A :=
  l.flatMap fun o => o.elim [] fun a => [a]

@[rocq_alias trillium.fairness.extract_Somes_spec]
theorem extractSomes_spec (l : List (Option A)) :
    ∀ a, some a ∈ l ↔ a ∈ extractSomes l := by
  intro a
  simp only [extractSomes, List.mem_flatMap]
  constructor
  · intro h; exact ⟨some a, h, by simp⟩
  · rintro ⟨o, ho, ha⟩
    cases o with
    | none => simp at ha
    | some b => simp at ha; exact ha ▸ ho

variable [Ord A] [Std.TransOrd A] [Std.LawfulEqOrd A]

@[rocq_alias trillium.fairness.extract_Somes_gset]
def extractSomesGSet (s : GSet (Option A)) : GSet A :=
  LawfulSet.ofList (extractSomes (FiniteSet.toList s))

@[rocq_alias trillium.fairness.extract_Somes_gset_spec]
theorem extractSomesGSet_spec (s : GSet (Option A)) :
    ∀ a, some a ∈ s ↔ a ∈ extractSomesGSet s := by
  intro a
  rw [extractSomesGSet, ← LawfulSet.mem_ofList, ← extractSomes_spec, FiniteSet.mem_toList]

@[rocq_alias trillium.fairness.extract_Somes_gset_inv]
theorem extractSomesGSet_inv (s : GSet (Option A)) :
    (FiniteSet.map some (extractSomesGSet s) : GSet (Option A)) = s \ {none} := by
  ext x
  rw [FiniteSet.mem_map, LawfulSet.mem_diff, LawfulSet.mem_singleton]
  simp only [← extractSomesGSet_spec]
  constructor
  · rintro ⟨y, rfl, hy⟩; exact ⟨hy, nofun⟩
  · rintro ⟨hx, hn⟩
    cases x with
    | none => exact absurd rfl hn
    | some y => exact ⟨y, rfl, hx⟩

@[rocq_alias trillium.fairness.extract_Somes_gset_singleton]
theorem extractSomesGSet_singleton (ok : Option A) :
    extractSomesGSet ({ok} : GSet (Option A)) =
      match ok with
      | some k => {k}
      | none => ∅ := by
  ext a
  rw [← extractSomesGSet_spec, LawfulSet.mem_singleton]
  cases ok with
  | none => simp only [reduceCtorEq, false_iff]; exact LawfulSet.mem_empty
  | some k => simp only [Option.some.injEq, LawfulSet.mem_singleton]

end ExtractSomes

@[rocq_alias trillium.fairness.gset_to_gmap_singleton]
theorem toGMap_singleton {K : Type _} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]
    {B : Type _} (b : B) (k : K) :
    GSet.toGMap b ({k} : GSet K) = (∅ : GMap K B).insert k b := by
  apply Std.ExtTreeMap.ext_getElem?
  intro k'
  simp only [GSet.getElem?_toGMap, LawfulSet.mem_singleton, Std.ExtTreeMap.getElem?_insert]
  by_cases h : k' = k
  · subst h; simp
  · simp [Ne.symm h]

section SetMax

/-- Rocq's `listMax`. -/
def listMax (l : List Nat) : Nat := l.foldr Nat.max 0

@[rocq_alias trillium.fairness.set_max]
def setMax (X : GSet Nat) : Nat := listMax (FiniteSet.toList X)

theorem listMax_le (l : List Nat) (n : Nat) : listMax l ≤ n ↔ ∀ x ∈ l, x ≤ n := by
  induction l with
  | nil => simp [listMax]
  | cons a l IH =>
    simp only [listMax] at IH ⊢
    simp only [List.foldr_cons, List.mem_cons, forall_eq_or_imp, ← IH]
    exact Nat.max_le

@[rocq_alias trillium.fairness.set_max_spec]
theorem setMax_spec (X : GSet Nat) (n : Nat) :
    setMax X ≤ n ↔ LawfulSet.setForall (fun k => k ≤ n) X := by
  rw [setMax, listMax_le]
  simp only [FiniteSet.mem_toList]
  rfl

@[rocq_alias trillium.fairness.list_max_elems]
theorem listMax_elems (X : List Nat) : ∀ x, x ∈ X → x ≤ listMax X := by
  intro x hx
  exact (listMax_le X _).1 le_rfl x hx

@[rocq_alias trillium.fairness.set_max_elems]
theorem setMax_elems (X : GSet Nat) : ∀ x, x ∈ X → x ≤ setMax X :=
  fun x hx => listMax_elems _ x (FiniteSet.mem_toList.2 hx)

@[rocq_alias trillium.fairness.set_max_singleton]
theorem setMax_singleton (x : Nat) : setMax ({x} : GSet Nat) = x := by
  rw [setMax, FiniteSet.toList_singleton]
  simp [listMax]

end SetMax

end Fairness

end Trillium
