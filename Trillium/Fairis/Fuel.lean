/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.Fairis.Destuttering
import Trillium.Fairness.Fairness
import Trillium.Fairness.UtilsMaps
import Trillium.ProgramLogic.AdequacyLocales

/-!
# Live models with fuel
Port of `fairis/fuel.v`.

A *live state* (`LiveState Locale M`) of a fair model `M` is a model state `lsUnder` together
with a map `lsMap` assigning to each locale (thread) a finite map from roles to their remaining
fuel. The fuel maps of different locales are disjoint, and each live role of `lsUnder` is owned
by some locale. `lsFuel δ` (the union of all fuel maps) and `lsMapping δ` (the owner of each
role) are derived from `lsMap`.

A *live model* (`LiveModel Locale M`, Rocq `LiveModel Λ M`) is given by a fuel limit
`lmFl : M → ℕ`; its transition relation `lsTrans` (Rocq `ls_trans`) on live states labelled
by `FairLabel` describes how fuel must decrease. `LiveModel.toModel` (Rocq `fair_model_model`
and the coercion `live_model_to_model`) is the corresponding `Trillium.Model`.

The main results are that fair executions matching an auxiliary trace yield fair auxiliary
traces (`fairness_preserved`), that valid auxiliary traces can be destuttered into model
traces (`can_destutter_auxtr`), and that destuttering preserves validity, fairness and
termination (`upto_preserves_validity`, `upto_stutter_fairness`, `upto_stutter_finiteness`).

Representation decisions:
* The language `Λ` only enters through its locale type: the live-state structures are
  parametrised by `Locale` (with the `Ord` instances needed for `GMap` keys, replacing Rocq's
  `Countable (locale Λ)`); the parts that mention expressions (`tidsSmaller`, `liveTids`,
  `exaux_traces_match`, …) take a `Language Expr Val Ectx State Locale` instance.
* `map_fold` is `Std.ExtTreeMap.foldr`. Since core's map union is right-biased (stdpp's is
  left-biased), `lsFuel` folds with `acc ∪ fs` and `addStuff ζ m rs` is `m ∪ toGMap ζ rs`
  (stdpp: `gset_to_gmap ζ rs ∪ m`), which give the same maps.
* `dom m` is `GMap.dom m`; `X ⊆ Y`, `X ∖ Y`, `X ∪ Y` on `GSet` are iris-lean's `LawfulSet`
  operations.
* `auxtrace_valid` (a Rocq `CoInductive`) is `TraceValid` for the transition relation of the
  live model (like `MtraceValid`).
* `Ul` and `Ψ` (the destuttering label map and measure) are `liveUl` and `fuelMeasure`.
-/

set_option linter.unusedSectionVars false

namespace Trillium.Fairis

open Trillium Trillium.Fairness Trace GMap

/-! ## Live states -/

/-- The data of a live state (Rocq `LiveStateData`). -/
@[rocq_alias trillium.fairis.LiveStateData]
structure LiveStateData (Locale : Type _) (M : FairModel) [Ord Locale] [Std.TransOrd Locale]
    [Std.LawfulEqOrd Locale] where
  /-- The underlying model state (Rocq `ls_under`, a coercion). -/
  lsUnder : M.fmstate
  /-- The fuel of the roles owned by each locale (Rocq `ls_map`). -/
  lsMap : GMap Locale (GMap M.fmrole Nat)

/-- A live state (Rocq `LiveState`): the fuel maps of distinct locales are disjoint, and every
live role is owned by some locale. -/
@[rocq_alias trillium.fairis.LiveState]
structure LiveState (Locale : Type _) (M : FairModel) [Ord Locale] [Std.TransOrd Locale]
    [Std.LawfulEqOrd Locale] extends LiveStateData Locale M where
  ls_map_disj : ∀ (ζ ζ' : Locale) (fs fs' : GMap M.fmrole Nat), ζ ≠ ζ' → lsMap[ζ]? = some fs → lsMap[ζ']? = some fs' → fs ##ₘ fs'
  ls_map_live : ∀ ρ, ρ ∈ M.liveRoles lsUnder → ∃ (ζ : Locale) (fs : GMap M.fmrole Nat), lsMap[ζ]? = some fs ∧ ρ ∈ dom fs

instance {Locale : Type _} {M : FairModel} [Ord Locale] [Std.TransOrd Locale]
    [Std.LawfulEqOrd Locale] :
    Coe (LiveState Locale M) (LiveStateData Locale M) := ⟨LiveState.toLiveStateData⟩

section fairness

variable {Locale : Type _} [Ord Locale] [Std.TransOrd Locale] [Std.LawfulEqOrd Locale]
variable {M : FairModel}

/-- The fuel of every role (Rocq `ls_fuel`): the union of the fuel maps of all locales. -/
@[rocq_alias trillium.fairis.ls_fuel]
def lsFuel (δ : LiveStateData Locale M) : GMap M.fmrole Nat :=
  δ.lsMap.foldr (fun _ fs m => m ∪ fs) ∅

/-- Rocq `add_stuff ζ m rs = gset_to_gmap ζ rs ∪ m` (stdpp's left-biased union; core's union is
right-biased, hence the swapped arguments). -/
@[rocq_alias trillium.fairis.add_stuff]
def addStuff (ζ : Locale) (m : GMap M.fmrole Locale) (rs : GSet M.fmrole) :
    GMap M.fmrole Locale :=
  m ∪ GSet.toGMap ζ rs

/-- The locale owning each role (Rocq `ls_mapping`). -/
@[rocq_alias trillium.fairis.ls_mapping]
def lsMapping (δ : LiveStateData Locale M) : GMap M.fmrole Locale :=
  δ.lsMap.foldr (fun ζ fs m => addStuff ζ m (dom fs)) ∅

/-! ### Folds of unions -/

section FoldUnion

variable {K R W V : Type _} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]
  [Ord R] [Std.TransOrd R] [Std.LawfulEqOrd R]

private theorem foldr_union_toList (m : GMap K V) (g : K → V → GMap R W) :
    m.foldr (fun k v acc => acc ∪ g k v) ∅ =
      m.toList.foldr (fun p acc => acc ∪ g p.1 p.2) ∅ :=
  Std.ExtTreeMap.foldr_eq_foldr_toList

private theorem list_foldr_union_none (l : List (K × V)) (g : K → V → GMap R W) (x : R) :
    (l.foldr (fun p acc => acc ∪ g p.1 p.2) ∅)[x]? = none ↔ ∀ p ∈ l, (g p.1 p.2)[x]? = none := by
  induction l with
  | nil => simp
  | cons p l IH =>
    simp only [List.foldr_cons, Std.ExtTreeMap.getElem?_union, Option.or_eq_none_iff, IH,
      List.mem_cons, forall_eq_or_imp]

private theorem list_foldr_union_some (l : List (K × V)) (g : K → V → GMap R W) (x : R) (w : W) :
    (l.foldr (fun p acc => acc ∪ g p.1 p.2) ∅)[x]? = some w → ∃ p ∈ l, (g p.1 p.2)[x]? = some w := by
  induction l with
  | nil => simp
  | cons p l IH =>
    simp only [List.foldr_cons, Std.ExtTreeMap.getElem?_union, List.mem_cons]
    intro h
    cases hp : (g p.1 p.2)[x]? with
    | some w' =>
      rw [hp] at h
      simp only [Option.some_or, Option.some.injEq] at h
      exact ⟨p, .inl rfl, h ▸ hp⟩
    | none =>
      rw [hp, Option.none_or] at h
      obtain ⟨q, hq, h⟩ := IH h
      exact ⟨q, .inr hq, h⟩

/-- Lookup in a fold of unions is `none` iff it is `none` in all the united maps. -/
theorem foldr_union_getElem?_none (m : GMap K V) (g : K → V → GMap R W) (x : R) :
    (m.foldr (fun k v acc => acc ∪ g k v) ∅)[x]? = none ↔
      ∀ k v, m[k]? = some v → (g k v)[x]? = none := by
  rw [foldr_union_toList, list_foldr_union_none]
  simp only [Prod.forall, Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some]

/-- A binding in a fold of unions comes from one of the united maps. -/
theorem foldr_union_getElem?_some (m : GMap K V) (g : K → V → GMap R W) (x : R) (w : W) :
    (m.foldr (fun k v acc => acc ∪ g k v) ∅)[x]? = some w →
      ∃ k v, m[k]? = some v ∧ (g k v)[x]? = some w := by
  rw [foldr_union_toList]
  intro h
  obtain ⟨⟨k, v⟩, hp, h⟩ := list_foldr_union_some _ g x w h
  exact ⟨k, v, Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.1 hp, h⟩

/-- A binding of one of the united maps is in the fold of unions, if no other united map binds
the same key. -/
theorem foldr_union_getElem?_of (m : GMap K V) (g : K → V → GMap R W) (x : R) (w : W) (k : K)
    (v : V) (hk : m[k]? = some v) (hx : (g k v)[x]? = some w)
    (huniq : ∀ k' v', k' ≠ k → m[k']? = some v' → (g k' v')[x]? = none) :
    (m.foldr (fun k v acc => acc ∪ g k v) ∅)[x]? = some w := by
  cases h : (m.foldr (fun k v acc => acc ∪ g k v) ∅)[x]? with
  | none =>
    rw [foldr_union_getElem?_none] at h
    rw [h k v hk] at hx; cases hx
  | some w' =>
    obtain ⟨k', v', hk', hx'⟩ := foldr_union_getElem?_some m g x w' h
    by_cases hkk : k' = k
    · subst hkk
      rw [hk] at hk'; cases hk'
      rw [hx] at hx'; exact hx'.symm ▸ rfl
    · rw [huniq k' v' hkk hk'] at hx'; cases hx'

end FoldUnion

/-! ### Basic properties of `lsFuel` and `lsMapping` -/

omit [Std.TransOrd Locale] [Std.LawfulEqOrd Locale] in
theorem mem_toGMap {K V : Type _} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K] (b : V)
    (X : GSet K) (k : K) : k ∈ GSet.toGMap b X ↔ k ∈ X := by
  rw [Std.ExtTreeMap.mem_iff_isSome_getElem?, GSet.getElem?_toGMap]
  by_cases h : k ∈ X <;> simp [h]

omit [Std.LawfulEqOrd Locale] in
@[rocq_alias trillium.fairis.dom_add_stuff]
theorem dom_add_stuff (ζ : Locale) (m : GMap M.fmrole Locale) (rs : GSet M.fmrole) :
    dom (addStuff ζ m rs) = rs ∪ dom m := by
  apply Iris.Std.LawfulSet.ext
  intro ρ
  simp only [mem_dom, addStuff, Iris.Std.mem_union, Std.ExtTreeMap.mem_union_iff, mem_toGMap]
  exact or_comm

@[rocq_alias trillium.fairis.add_stuff_commute]
theorem add_stuff_commute (ζ1 ζ2 : Locale) (m : GMap M.fmrole Locale) (s1 s2 : GSet M.fmrole) :
    s1 ## s2 → addStuff ζ2 (addStuff ζ1 m s1) s2 = addStuff ζ1 (addStuff ζ2 m s2) s1 := by
  intro Hdisj
  apply Std.ExtTreeMap.ext_getElem?
  intro ρ
  simp only [addStuff, Std.ExtTreeMap.getElem?_union, GSet.getElem?_toGMap]
  by_cases h1 : ρ ∈ s1 <;> by_cases h2 : ρ ∈ s2 <;> simp [h1, h2]
  exact (Hdisj ρ ⟨h1, h2⟩).elim

/-- `lsFuel` as a fold of unions. -/
private theorem lsFuel_eq (δ : LiveStateData Locale M) :
    lsFuel δ = δ.lsMap.foldr (fun _ fs acc => acc ∪ (fun _ fs => fs) () fs) ∅ := rfl

/-- `lsMapping` as a fold of unions. -/
private theorem lsMapping_eq (δ : LiveStateData Locale M) :
    lsMapping δ = δ.lsMap.foldr (fun ζ fs acc => acc ∪ GSet.toGMap ζ (dom fs)) ∅ := rfl

/-- The fuel map of `ρ`'s owner. -/
private theorem lsFuel_getElem?_none (δ : LiveStateData Locale M) (ρ : M.fmrole) :
    (lsFuel δ)[ρ]? = none ↔ ∀ (ζ : Locale) (fs : GMap M.fmrole Nat), δ.lsMap[ζ]? = some fs → fs[ρ]? = none :=
  foldr_union_getElem?_none δ.lsMap (fun _ fs => fs) ρ

private theorem lsMapping_getElem?_none (δ : LiveStateData Locale M) (ρ : M.fmrole) :
    (lsMapping δ)[ρ]? = none ↔ ∀ (ζ : Locale) (fs : GMap M.fmrole Nat), δ.lsMap[ζ]? = some fs → ρ ∉ fs := by
  rw [lsMapping_eq, foldr_union_getElem?_none]
  refine forall_congr' fun ζ => forall_congr' fun fs => imp_congr_right fun _ => ?_
  simp only [GSet.getElem?_toGMap, mem_dom]
  by_cases h : ρ ∈ fs <;> simp [h]

@[rocq_alias trillium.fairis.ls_same_doms]
theorem ls_same_doms (δ : LiveState Locale M) :
    dom (lsMapping (δ : LiveStateData Locale M)) = dom (lsFuel (δ : LiveStateData Locale M)) := by
  apply Iris.Std.LawfulSet.ext
  intro ρ
  simp only [mem_dom]
  rw [Std.ExtTreeMap.mem_iff_isSome_getElem?, Std.ExtTreeMap.mem_iff_isSome_getElem?]
  have h1 := lsMapping_getElem?_none (δ : LiveStateData Locale M) ρ
  have h2 := lsFuel_getElem?_none (δ : LiveStateData Locale M) ρ
  have h3 : (∀ (ζ : Locale) (fs : GMap M.fmrole Nat), δ.lsMap[ζ]? = some fs → ρ ∉ fs) ↔
      (∀ (ζ : Locale) (fs : GMap M.fmrole Nat), δ.lsMap[ζ]? = some fs → fs[ρ]? = none) := by
    simp only [not_mem_iff]
  rw [← Bool.not_eq_false, ← Bool.not_eq_false, Option.isSome_eq_false_iff,
    Option.isSome_eq_false_iff, Option.isNone_iff_eq_none, Option.isNone_iff_eq_none, h1, h2, h3]

@[rocq_alias trillium.fairis.ls_fuel_data]
theorem ls_fuel_data (ρ : M.fmrole) (δ : LiveState Locale M) (ζ : Locale)
    (fs : GMap M.fmrole Nat) (f : Nat) :
    δ.lsMap[ζ]? = some fs → fs[ρ]? = some f → (lsFuel (δ : LiveStateData Locale M))[ρ]? = some f := by
  intro Hζ Hρ
  refine foldr_union_getElem?_of δ.lsMap (fun _ fs => fs) ρ f ζ fs Hζ Hρ ?_
  intro ζ' fs' Hne Hζ'
  rcases δ.ls_map_disj ζ ζ' fs fs' (Ne.symm Hne) Hζ Hζ' ρ with h | h
  · rw [Hρ] at h; cases h
  · exact h

@[rocq_alias trillium.fairis.ls_mapping_data]
theorem ls_mapping_data (ρ : M.fmrole) (δ : LiveState Locale M) (ζ : Locale)
    (fs : GMap M.fmrole Nat) :
    δ.lsMap[ζ]? = some fs → ρ ∈ dom fs → (lsMapping (δ : LiveStateData Locale M))[ρ]? = some ζ := by
  intro Hζ Hρ
  rw [lsMapping_eq]
  refine foldr_union_getElem?_of δ.lsMap (fun ζ fs => GSet.toGMap ζ (dom fs)) ρ ζ ζ fs Hζ
    (by simp [Hρ]) ?_
  intro ζ' fs' Hne Hζ'
  rw [GSet.getElem?_toGMap, ite_eq_right_iff.2 (fun h => absurd h ?_)]
  rw [mem_dom] at Hρ ⊢
  intro Hρ'
  rcases δ.ls_map_disj ζ ζ' fs fs' (Ne.symm Hne) Hζ Hζ' ρ with h | h
  · exact (not_mem_iff.2 h) Hρ
  · exact (not_mem_iff.2 h) Hρ'

@[rocq_alias trillium.fairis.ls_mapping_data_inv]
theorem ls_mapping_data_inv (ρ : M.fmrole) (δ : LiveState Locale M) (ζ : Locale) :
    (lsMapping (δ : LiveStateData Locale M))[ρ]? = some ζ →
      ∃ fs : GMap M.fmrole Nat, δ.lsMap[ζ]? = some fs ∧ ρ ∈ dom fs := by
  rw [lsMapping_eq]
  intro h
  obtain ⟨ζ', fs, Hζ', h⟩ := foldr_union_getElem?_some _ _ ρ ζ h
  rw [GSet.getElem?_toGMap] at h
  split at h
  · cases h; exact ⟨fs, Hζ', by assumption⟩
  · cases h

@[rocq_alias trillium.fairis.ls_fuel_dom_data]
theorem ls_fuel_dom_data (ρ : M.fmrole) (δ : LiveState Locale M) (ζ : Locale)
    (fs : GMap M.fmrole Nat) :
    δ.lsMap[ζ]? = some fs → ρ ∈ dom fs → ρ ∈ dom (lsFuel (δ : LiveStateData Locale M)) := by
  intro Hζ Hρ
  rw [mem_dom_iff] at Hρ ⊢
  obtain ⟨f, Hf⟩ := Hρ
  exact ⟨f, ls_fuel_data ρ δ ζ fs f Hζ Hf⟩

@[rocq_alias trillium.fairis.ls_fuel_data_inv]
theorem ls_fuel_data_inv (ρ : M.fmrole) (δ : LiveState Locale M) (f : Nat) :
    (lsFuel (δ : LiveStateData Locale M))[ρ]? = some f →
      ∃ (ζ : Locale) (fs : GMap M.fmrole Nat), δ.lsMap[ζ]? = some fs ∧ fs[ρ]? = some f :=
  foldr_union_getElem?_some δ.lsMap (fun _ fs => fs) ρ f

@[rocq_alias trillium.fairis.ls_fuel_dom_data_inv]
theorem ls_fuel_dom_data_inv (ρ : M.fmrole) (δ : LiveState Locale M) :
    ρ ∈ dom (lsFuel (δ : LiveStateData Locale M)) → ∃ (ζ : Locale) (fs : GMap M.fmrole Nat), δ.lsMap[ζ]? = some fs ∧ ρ ∈ dom fs := by
  rw [mem_dom_iff]
  rintro ⟨f, Hf⟩
  obtain ⟨ζ, fs, Hζ, Hρ⟩ := ls_fuel_data_inv ρ δ f Hf
  exact ⟨ζ, fs, Hζ, mem_dom_iff.2 ⟨f, Hρ⟩⟩

@[rocq_alias trillium.fairis.ls_fuel_suff]
theorem ls_fuel_suff (δ : LiveState Locale M) (ρ : M.fmrole) :
    ρ ∈ dom (lsFuel (δ : LiveStateData Locale M)) → ∃ (ζ : Locale) (fs : GMap M.fmrole Nat), δ.lsMap[ζ]? = some fs ∧ ρ ∈ dom fs :=
  ls_fuel_dom_data_inv ρ δ

@[rocq_alias trillium.fairis.ls_fuel_dom]
theorem ls_fuel_dom (δ : LiveState Locale M) :
    M.liveRoles δ.lsUnder ⊆ dom (lsFuel (δ : LiveStateData Locale M)) := by
  intro ρ Hρ
  obtain ⟨ζ, fs, Hζ, Hin⟩ := δ.ls_map_live ρ Hρ
  exact ls_fuel_dom_data ρ δ ζ fs Hζ Hin

@[rocq_alias trillium.fairis.ls_mapping_dom]
theorem ls_mapping_dom (m : LiveState Locale M) :
    M.liveRoles m.lsUnder ⊆ dom (lsMapping (m : LiveStateData Locale M)) := by
  rw [ls_same_doms]; exact ls_fuel_dom m

/-! ### Characterisations of `lsFuel` and `lsMapping` -/

theorem lsFuel_getElem?_eq_some_iff (δ : LiveState Locale M) (ρ : M.fmrole) (f : Nat) :
    (lsFuel (δ : LiveStateData Locale M))[ρ]? = some f ↔
      ∃ (ζ : Locale) (fs : GMap M.fmrole Nat), δ.lsMap[ζ]? = some fs ∧ fs[ρ]? = some f :=
  ⟨ls_fuel_data_inv ρ δ f, fun ⟨ζ, fs, h1, h2⟩ => ls_fuel_data ρ δ ζ fs f h1 h2⟩

theorem mem_dom_lsFuel_iff (δ : LiveState Locale M) (ρ : M.fmrole) :
    ρ ∈ dom (lsFuel (δ : LiveStateData Locale M)) ↔
      ∃ (ζ : Locale) (fs : GMap M.fmrole Nat), δ.lsMap[ζ]? = some fs ∧ ρ ∈ dom fs :=
  ⟨ls_fuel_dom_data_inv ρ δ, fun ⟨ζ, fs, h1, h2⟩ => ls_fuel_dom_data ρ δ ζ fs h1 h2⟩

theorem lsMapping_getElem?_eq_some_iff (δ : LiveState Locale M) (ρ : M.fmrole) (ζ : Locale) :
    (lsMapping (δ : LiveStateData Locale M))[ρ]? = some ζ ↔
      ∃ fs : GMap M.fmrole Nat, δ.lsMap[ζ]? = some fs ∧ ρ ∈ dom fs :=
  ⟨ls_mapping_data_inv ρ δ ζ, fun ⟨fs, h1, h2⟩ => ls_mapping_data ρ δ ζ fs h1 h2⟩

/-! ## Labels and transitions -/

end fairness

/-- The labels of live models (Rocq `FairLabel`): a step of role `ρ` by locale `ζ`, a silent
step of locale `ζ`, or a configuration step. -/
@[rocq_alias trillium.fairis.FairLabel]
inductive FairLabel (Role : Type _) (Locale : Type _) where
  | takeStep : Role → Locale → FairLabel Role Locale
  | silentStep : Locale → FairLabel Role Locale
  | configStep : FairLabel Role Locale
  deriving DecidableEq

/-- Strict order on optional naturals (Rocq `less`; the same as `oless`). -/
@[rocq_alias trillium.fairis.less]
def less (x y : Option Nat) : Prop :=
  match x, y with
  | some x, some y => x < y
  | _, _ => False

section fairness

variable {Locale : Type _} [Ord Locale] [Std.TransOrd Locale] [Std.LawfulEqOrd Locale]
variable {M : FairModel}

/-- The fuel of `ρ'` must decrease in a step from `a` to `b` labelled by `oρ` and taken by the
locale `otid` (Rocq `must_decrease`): either the step is taken by the owner of `ρ'` but is
not a step of `ρ'`, or the owner of `ρ'` changes. -/
@[rocq_alias trillium.fairis.must_decrease]
inductive MustDecrease (ρ' : M.fmrole) (oρ : Option M.fmrole) (a b : LiveStateData Locale M) :
    Option Locale → Prop where
  | sameTid (tid : Locale) (Hneqρ : some ρ' ≠ oρ) (Hsametid : some tid = (lsMapping a)[ρ']?) :
      MustDecrease ρ' oρ a b (some tid)
  | changeTid (otid : Option Locale) (Hneqtid : (lsMapping a)[ρ']? ≠ (lsMapping b)[ρ']?)
      (Hissome : ((lsMapping b)[ρ']?).isSome) : MustDecrease ρ' oρ a b otid

/-- Rocq `fuel_decr`. -/
@[rocq_alias trillium.fairis.fuel_decr]
def fuelDecr (tid : Option Locale) (oρ : Option M.fmrole) (a b : LiveStateData Locale M) : Prop :=
  ∀ ρ', ρ' ∈ dom (lsFuel a) → ρ' ∈ dom (lsFuel b) → MustDecrease ρ' oρ a b tid →
    oless (lsFuel b)[ρ']? (lsFuel a)[ρ']?

/-- Rocq `fuel_must_not_incr`. -/
@[rocq_alias trillium.fairis.fuel_must_not_incr]
def fuelMustNotIncr (oρ : Option M.fmrole) (a b : LiveStateData Locale M) : Prop :=
  ∀ ρ', ρ' ∈ dom (lsFuel a) → some ρ' ≠ oρ →
    oleq (lsFuel b)[ρ']? (lsFuel a)[ρ']? ∨
      (ρ' ∉ dom (lsFuel b) ∧ ρ' ∉ M.liveRoles a.lsUnder)

@[rocq_alias trillium.fairis.ls_map_agree]
theorem ls_map_agree {δ : LiveState Locale M} {ρ : M.fmrole} {ζ1 ζ2 : Locale}
    {fs1 fs2 : GMap M.fmrole Nat} :
    δ.lsMap[ζ1]? = some fs1 → δ.lsMap[ζ2]? = some fs2 → ρ ∈ dom fs1 → ρ ∈ dom fs2 →
      ζ1 = ζ2 ∧ fs1 = fs2 := by
  intro Hlk1 Hlk2 Hin1 Hin2
  by_cases Hneq : ζ1 = ζ2
  · subst Hneq; rw [Hlk1] at Hlk2; cases Hlk2; exact ⟨rfl, rfl⟩
  · exfalso
    have := δ.ls_map_disj _ _ _ _ Hneq Hlk1 Hlk2
    rw [disjoint_iff_mem] at this
    exact this ρ (mem_dom.1 Hin1) (mem_dom.1 Hin2)

/-- The transition relation of live states (Rocq `ls_trans`). Configuration steps are not
supported (their case contains `False`, as in Rocq). -/
@[rocq_alias trillium.fairis.ls_trans]
def lsTrans (fuelLimit : M.fmstate → Nat) (a : LiveStateData Locale M)
    (ℓ : FairLabel M.fmrole Locale) (b : LiveStateData Locale M) : Prop :=
  match ℓ with
  | .takeStep ρ tid =>
    M.fmtrans a.lsUnder (some ρ) b.lsUnder ∧
    (lsMapping a)[ρ]? = some tid ∧
    fuelDecr (some tid) (some ρ) a b ∧
    fuelMustNotIncr (some ρ) a b ∧
    oleq (lsFuel b)[ρ]? (some (fuelLimit b.lsUnder)) ∧
    (∀ ρ, ρ ∈ dom (lsFuel b) \ dom (lsFuel a) → oleq (lsFuel b)[ρ]? (some (fuelLimit b.lsUnder))) ∧
    dom (lsFuel b) \ dom (lsFuel a) ⊆ M.liveRoles b.lsUnder \ M.liveRoles a.lsUnder
  | .silentStep tid =>
    (∃ ρ : M.fmrole, (lsMapping a)[ρ]? = some tid) ∧
    fuelDecr (some tid) none a b ∧
    fuelMustNotIncr none a b ∧
    dom (lsFuel b) ⊆ dom (lsFuel a) ∧
    a.lsUnder = b.lsUnder
  | .configStep =>
    M.fmtrans a.lsUnder none b.lsUnder ∧
    fuelDecr none none a b ∧
    fuelMustNotIncr none a b ∧
    (∀ ρ, ρ ∈ M.liveRoles b.lsUnder \ M.liveRoles a.lsUnder →
      oleq (lsFuel b)[ρ]? (some (fuelLimit b.lsUnder))) ∧
    False

/-- Membership in a set of the form `A \ (B ∪ C) ∩ D`. -/
private theorem mem_diff_union_inter {K : Type _} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]
    {A B C D : GSet K} {x : K} :
    x ∈ A \ (B ∪ C) ∩ D ↔ x ∈ A ∧ x ∉ B ∧ x ∉ C ∧ x ∈ D := by
  simp only [Iris.Std.mem_inter, Iris.Std.mem_diff, Iris.Std.mem_union, not_or, and_assoc]

@[rocq_alias trillium.fairis.silent_step_suff_data]
theorem silent_step_suff_data (fl : M.fmstate → Nat) (δ : LiveState Locale M)
    (fs fs' fs'' : GMap M.fmrole Nat) (ζ : Locale) (oζ' : Option Locale) :
    δ.lsMap[ζ]? = some fs → fs ≠ ∅ →
    (∀ (ρ : M.fmrole) (f' : Nat), fs'[ρ]? = some f' → ∃ f, fs[ρ]? = some f ∧ f' < f) →
    (∀ (ρ : M.fmrole) (f' : Nat), fs''[ρ]? = some f' → ∃ f, fs[ρ]? = some f ∧ f' < f) →
    dom fs \ (dom fs' ∪ dom fs'') ∩ M.liveRoles δ.lsUnder = ∅ →
    dom fs' ∩ dom fs'' = ∅ →
    (∀ ζ', oζ' = some ζ' → ζ' ∉ dom δ.lsMap) →
    (oζ' = none → fs'' = ∅) →
    let data' := match oζ' with
      | none => δ.lsMap
      | some ζ' => δ.lsMap.insert ζ' fs''
    let data'' := data'.insert ζ fs'
    ∃ δ' : LiveState Locale M, δ'.toLiveStateData = { lsUnder := δ.lsUnder, lsMap := data'' } ∧
      lsTrans fl δ (.silentStep ζ) δ' := by
  intro Hζ Hnemp Hfs' Hfs'' Hlives Hdisj Hnlocale Hifnone data' data''
  have Hincl' : ∀ ρ, ρ ∈ fs' → ρ ∈ fs := fun ρ h => by
    obtain ⟨f', hf'⟩ := mem_iff_exists.1 h
    obtain ⟨f, hf, -⟩ := Hfs' ρ f' hf'
    exact mem_of_getElem? hf
  have Hincl'' : ∀ ρ, ρ ∈ fs'' → ρ ∈ fs := fun ρ h => by
    obtain ⟨f', hf'⟩ := mem_iff_exists.1 h
    obtain ⟨f, hf, -⟩ := Hfs'' ρ f' hf'
    exact mem_of_getElem? hf
  have Hlives' : ∀ ρ, ρ ∈ fs → ρ ∉ fs' → ρ ∉ fs'' → ρ ∉ M.liveRoles δ.lsUnder := by
    intro ρ h1 h2 h3 h4
    refine Iris.Std.LawfulSet.eq_empty_iff.1 Hlives ρ ?_
    rw [mem_diff_union_inter]
    simp only [mem_dom]
    exact ⟨h1, h2, h3, h4⟩
  have Hdisj' : ∀ ρ, ρ ∈ fs' → ρ ∉ fs'' := by
    intro ρ h1 h2
    refine Iris.Std.LawfulSet.eq_empty_iff.1 Hdisj ρ ?_
    rw [Iris.Std.mem_inter, mem_dom, mem_dom]
    exact ⟨h1, h2⟩
  have Hnew_ne : ∀ ζn, oζ' = some ζn → ζn ≠ ζ := by
    rintro ζn hoζ rfl
    exact Hnlocale ζn hoζ (mem_dom.2 (mem_of_getElem? Hζ))
  have Hlk : ∀ (z : Locale) (g : GMap M.fmrole Nat), data''[z]? = some g ↔
      (z = ζ ∧ g = fs') ∨ (z ≠ ζ ∧ (δ.lsMap[z]? = some g ∨ (oζ' = some z ∧ g = fs''))) := by
    intro z g
    simp only [data'', getElem?_insert_ite]
    by_cases hz : ζ = z
    · subst hz
      simp only [ite_true, Option.some.injEq, true_and, ne_eq, not_true_eq_false, false_and,
        or_false]
      exact eq_comm
    · simp only [hz, ite_false, ne_eq, Ne.symm hz, not_false_eq_true, true_and, false_and,
        false_or]
      rcases Option.eq_none_or_eq_some oζ' with hoζ | ⟨ζn, hoζ⟩
      · simp only [data', hoζ, reduceCtorEq, false_and, or_false]
      · simp only [data', hoζ, getElem?_insert_ite, Option.some.injEq]
        by_cases hn : ζn = z
        · subst hn
          have : δ.lsMap[ζn]? = none := not_mem_iff.1 fun h => Hnlocale ζn hoζ (mem_dom.2 h)
          simp [this, eq_comm]
        · simp [hn]
  have Hdisjδ' : ∀ (z1 z2 : Locale) (fs1 fs2 : GMap M.fmrole Nat), z1 ≠ z2 →
      data''[z1]? = some fs1 → data''[z2]? = some fs2 → fs1 ##ₘ fs2 := by
    intro z1 z2 fs1 fs2 Hneq H1 H2
    rw [disjoint_iff_mem]
    intro ρ Hρ1 Hρ2
    rcases (Hlk _ _).1 H1 with ⟨e1, e1'⟩ | ⟨hz1, O1 | ⟨hn1, e1'⟩⟩ <;>
    rcases (Hlk _ _).1 H2 with ⟨e2, e2'⟩ | ⟨hz2, O2 | ⟨hn2, e2'⟩⟩
    · exact Hneq (e1.trans e2.symm)
    · subst e1 e1'
      exact hz2 (ls_map_agree O2 Hζ (mem_dom.2 Hρ2) (mem_dom.2 (Hincl' ρ Hρ1))).1
    · subst e1' e2'; exact Hdisj' ρ Hρ1 Hρ2
    · subst e2 e2'
      exact hz1 (ls_map_agree O1 Hζ (mem_dom.2 Hρ1) (mem_dom.2 (Hincl' ρ Hρ2))).1
    · exact Hneq (ls_map_agree O1 O2 (mem_dom.2 Hρ1) (mem_dom.2 Hρ2)).1
    · subst e2'
      exact hz1 (ls_map_agree O1 Hζ (mem_dom.2 Hρ1) (mem_dom.2 (Hincl'' ρ Hρ2))).1
    · subst e1' e2'; exact Hdisj' ρ Hρ2 Hρ1
    · subst e1'
      exact hz2 (ls_map_agree O2 Hζ (mem_dom.2 Hρ2) (mem_dom.2 (Hincl'' ρ Hρ1))).1
    · rw [hn1] at hn2; cases hn2; exact Hneq rfl
  have Hliveδ' : ∀ ρ, ρ ∈ M.liveRoles δ.lsUnder →
      ∃ (z : Locale) (g : GMap M.fmrole Nat), data''[z]? = some g ∧ ρ ∈ dom g := by
    intro ρ Hlive
    obtain ⟨ζ0, fs0, H0, Hin0⟩ := δ.ls_map_live ρ Hlive
    by_cases h : ζ0 = ζ
    · subst h
      have e : fs0 = fs := Option.some.inj (H0.symm.trans Hζ)
      subst e
      rw [mem_dom] at Hin0
      by_cases h1 : ρ ∈ fs'
      · exact ⟨ζ0, fs', (Hlk _ _).2 (.inl ⟨rfl, rfl⟩), mem_dom.2 h1⟩
      · by_cases h2 : ρ ∈ fs''
        · rcases Option.eq_none_or_eq_some oζ' with hoζ | ⟨ζn, hoζ⟩
          · rw [Hifnone hoζ] at h2; exact absurd h2 Std.ExtTreeMap.not_mem_empty
          · exact ⟨ζn, fs'', (Hlk _ _).2 (.inr ⟨Hnew_ne ζn hoζ, .inr ⟨hoζ, rfl⟩⟩), mem_dom.2 h2⟩
        · exact absurd Hlive (Hlives' ρ Hin0 h1 h2)
    · exact ⟨ζ0, fs0, (Hlk _ _).2 (.inr ⟨h, .inl H0⟩), Hin0⟩
  let δ' : LiveState Locale M := ⟨⟨δ.lsUnder, data''⟩, Hdisjδ', Hliveδ'⟩
  have Hlk' : ∀ (z : Locale) (g : GMap M.fmrole Nat), δ'.lsMap[z]? = some g ↔
      (z = ζ ∧ g = fs') ∨ (z ≠ ζ ∧ (δ.lsMap[z]? = some g ∨ (oζ' = some z ∧ g = fs''))) := Hlk
  refine ⟨δ', rfl, ?_⟩
  show (∃ ρ : M.fmrole, (lsMapping (δ : LiveStateData Locale M))[ρ]? = some ζ) ∧
    fuelDecr (some ζ) none (δ : LiveStateData Locale M) (δ' : LiveStateData Locale M) ∧
    fuelMustNotIncr none (δ : LiveStateData Locale M) (δ' : LiveStateData Locale M) ∧
    dom (lsFuel (δ' : LiveStateData Locale M)) ⊆ dom (lsFuel (δ : LiveStateData Locale M)) ∧
    δ.lsUnder = δ'.lsUnder
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · -- some role is owned by `ζ`
    have : ¬ ∀ k, fs[k]? = none := fun h => Hnemp (eq_empty_iff.2 h)
    obtain ⟨ρ, hρ⟩ := Classical.not_forall.1 this
    exact ⟨ρ, ls_mapping_data ρ δ ζ fs Hζ (mem_dom.2 (Classical.not_not.1 (mt not_mem_iff.1 hρ)))⟩
  · -- fuel decreases
    intro ρ' Hin Hin' Hmd
    obtain ⟨f, Hf⟩ := mem_dom_iff.1 Hin
    obtain ⟨f', Hf'⟩ := mem_dom_iff.1 Hin'
    rw [Hf, Hf']
    show f' < f
    obtain ⟨ζ1, fs1, H1, Hρ1⟩ := (lsFuel_getElem?_eq_some_iff δ ρ' f).1 Hf
    obtain ⟨ζ2, fs2, H2, Hρ2⟩ := (lsFuel_getElem?_eq_some_iff δ' ρ' f').1 Hf'
    cases Hmd with
    | sameTid tid Hneqρ Hsametid =>
      obtain ⟨fs0, H0, Hin0⟩ := (lsMapping_getElem?_eq_some_iff δ ρ' ζ).1 Hsametid.symm
      have e : fs0 = fs := Option.some.inj (H0.symm.trans Hζ)
      subst e
      obtain ⟨e1, e1'⟩ := ls_map_agree H1 H0 (mem_dom_iff.2 ⟨f, Hρ1⟩) Hin0
      subst e1 e1'
      rcases (Hlk' _ _).1 H2 with ⟨-, e2'⟩ | ⟨hz2, H2 | ⟨-, e2'⟩⟩
      · subst e2'
        obtain ⟨g, hg, hlt⟩ := Hfs' ρ' f' Hρ2
        rw [Hρ1] at hg; cases hg; exact hlt
      · exact absurd (ls_map_agree H2 H0 (mem_dom_iff.2 ⟨f', Hρ2⟩) Hin0).1 hz2
      · subst e2'
        obtain ⟨g, hg, hlt⟩ := Hfs'' ρ' f' Hρ2
        rw [Hρ1] at hg; cases hg; exact hlt
    | changeTid otid Hneqtid Hissome =>
      obtain ⟨ζ0, Hζ0⟩ := Option.isSome_iff_exists.1 Hissome
      rw [Hζ0] at Hneqtid
      obtain ⟨g0, H0, Hin0⟩ := (lsMapping_getElem?_eq_some_iff δ' ρ' ζ0).1 Hζ0
      obtain ⟨e2, e2'⟩ := ls_map_agree H2 H0 (mem_dom_iff.2 ⟨f', Hρ2⟩) Hin0
      subst e2 e2'
      rcases (Hlk' _ _).1 H2 with ⟨e3, e3'⟩ | ⟨hz2, H2o | ⟨-, e3'⟩⟩
      · subst e3 e3'
        exact absurd (ls_mapping_data ρ' δ ζ2 fs Hζ
          (mem_dom.2 (Hincl' ρ' (mem_of_getElem? Hρ2)))) Hneqtid
      · exact absurd (ls_mapping_data ρ' δ ζ2 fs2 H2o Hin0) Hneqtid
      · subst e3'
        obtain ⟨g, hg, hlt⟩ := Hfs'' ρ' f' Hρ2
        obtain ⟨e4, e4'⟩ := ls_map_agree H1 Hζ (mem_dom_iff.2 ⟨f, Hρ1⟩) (mem_dom_iff.2 ⟨g, hg⟩)
        subst e4 e4'
        rw [Hρ1] at hg; cases hg; exact hlt
  · -- fuel does not increase
    intro ρ' Hin' _
    obtain ⟨f, Hf⟩ := mem_dom_iff.1 Hin'
    rw [Hf]
    obtain ⟨ζ1, fs0, H1, Hρ1⟩ := (lsFuel_getElem?_eq_some_iff δ ρ' f).1 Hf
    by_cases hz : ζ1 = ζ
    · subst hz
      have e : fs0 = fs := Option.some.inj (H1.symm.trans Hζ)
      subst e
      by_cases h1 : ρ' ∈ fs'
      · left
        obtain ⟨f', hf'⟩ := mem_iff_exists.1 h1
        obtain ⟨g, hg, hlt⟩ := Hfs' ρ' f' hf'
        rw [Hρ1] at hg; cases hg
        rw [ls_fuel_data ρ' δ' ζ1 fs' f' ((Hlk' _ _).2 (.inl ⟨rfl, rfl⟩)) hf']
        exact Nat.le_of_lt hlt
      · by_cases h2 : ρ' ∈ fs''
        · left
          obtain ⟨f', hf'⟩ := mem_iff_exists.1 h2
          obtain ⟨g, hg, hlt⟩ := Hfs'' ρ' f' hf'
          rw [Hρ1] at hg; cases hg
          rcases Option.eq_none_or_eq_some oζ' with hoζ | ⟨ζn, hoζ⟩
          · rw [Hifnone hoζ] at h2; exact absurd h2 Std.ExtTreeMap.not_mem_empty
          · rw [ls_fuel_data ρ' δ' ζn fs'' f'
              ((Hlk' _ _).2 (.inr ⟨Hnew_ne ζn hoζ, .inr ⟨hoζ, rfl⟩⟩)) hf']
            exact Nat.le_of_lt hlt
        · right
          refine ⟨?_, Hlives' ρ' (mem_of_getElem? Hρ1) h1 h2⟩
          intro Habs
          obtain ⟨za, ga, Ha, Hina⟩ := (mem_dom_lsFuel_iff δ' ρ').1 Habs
          rcases (Hlk' _ _).1 Ha with ⟨-, e⟩ | ⟨hza, Ha' | ⟨-, e⟩⟩
          · subst e; exact h1 (mem_dom.1 Hina)
          · exact hza (ls_map_agree Ha' H1 Hina (mem_dom.2 (mem_of_getElem? Hρ1))).1
          · subst e; exact h2 (mem_dom.1 Hina)
    · left
      rw [ls_fuel_data ρ' δ' ζ1 fs0 f ((Hlk' _ _).2 (.inr ⟨hz, .inl H1⟩)) Hρ1]
      exact Nat.le_refl f
  · -- the domain of the fuel does not grow
    intro ρ Hin
    obtain ⟨z, g, Hz, Hinz⟩ := (mem_dom_lsFuel_iff δ' ρ).1 Hin
    rcases (Hlk' _ _).1 Hz with ⟨-, e⟩ | ⟨-, Hz' | ⟨-, e⟩⟩
    · subst e; exact ls_fuel_dom_data ρ δ ζ fs Hζ (mem_dom.2 (Hincl' ρ (mem_dom.1 Hinz)))
    · exact ls_fuel_dom_data ρ δ z g Hz' Hinz
    · subst e; exact ls_fuel_dom_data ρ δ ζ fs Hζ (mem_dom.2 (Hincl'' ρ (mem_dom.1 Hinz)))

@[rocq_alias trillium.fairis.model_step_suff_data]
theorem model_step_suff_data (fl : M.fmstate → Nat) (δ : LiveState Locale M) (ρ0 : M.fmrole)
    (m' : M.fmstate) (fs fs' : GMap M.fmrole Nat) (ζ : Locale) :
    M.fmtrans δ.lsUnder (some ρ0) m' →
    δ.lsMap[ζ]? = some fs →
    ρ0 ∈ dom fs →
    (∀ (ρ : M.fmrole) (f f' : Nat), fs'[ρ]? = some f' → ρ ≠ ρ0 → fs[ρ]? = some f → f' < f) →
    (∀ f'0, fs'[ρ0]? = some f'0 → f'0 ≤ fl m') →
    (∀ ρ, ρ ∈ dom fs' \ dom fs → ∀ f', fs'[ρ]? = some f' → f' ≤ fl m') →
    M.liveRoles m' \ M.liveRoles δ.lsUnder = dom fs' \ dom fs →
    (∀ ρ, ρ ∈ M.liveRoles m' \ M.liveRoles δ.lsUnder →
      ∀ (ζ' : Locale) (fs' : GMap M.fmrole Nat), δ.lsMap[ζ']? = some fs' → ρ ∉ dom fs') →
    dom fs \ dom fs' ∩ M.liveRoles δ.lsUnder = ∅ →
    let data' := δ.lsMap.insert ζ fs'
    ∃ δ' : LiveState Locale M, δ'.toLiveStateData = { lsUnder := m', lsMap := data' } ∧
      lsTrans fl δ (.takeStep ρ0 ζ) δ' := by
  intro Htrans Hζ Hρ0in Hfs' Hfl0 Hfln Hborn Hnew Hdead data'
  have Hborn' : ∀ ρ, (ρ ∈ M.liveRoles m' ∧ ρ ∉ M.liveRoles δ.lsUnder) ↔ (ρ ∈ fs' ∧ ρ ∉ fs) := by
    intro ρ
    have := congrArg (ρ ∈ ·) Hborn
    simp only [Iris.Std.mem_diff, mem_dom, eq_iff_iff] at this
    exact this
  have Hdead' : ∀ ρ, ρ ∈ fs → ρ ∉ fs' → ρ ∉ M.liveRoles δ.lsUnder := by
    intro ρ h1 h2 h3
    refine Iris.Std.LawfulSet.eq_empty_iff.1 Hdead ρ ?_
    rw [Iris.Std.mem_inter, Iris.Std.mem_diff, mem_dom, mem_dom]
    exact ⟨⟨h1, h2⟩, h3⟩
  have Hnew' : ∀ ρ, ρ ∈ fs' → ρ ∉ fs →
      ∀ (ζ' : Locale) (g : GMap M.fmrole Nat), δ.lsMap[ζ']? = some g → ρ ∉ g := by
    intro ρ h1 h2 ζ' g hg hρ
    refine Hnew ρ ?_ ζ' g hg (mem_dom.2 hρ)
    rw [Iris.Std.mem_diff]
    exact (Hborn' ρ).2 ⟨h1, h2⟩
  have Hlk : ∀ (z : Locale) (g : GMap M.fmrole Nat), data'[z]? = some g ↔
      (z = ζ ∧ g = fs') ∨ (z ≠ ζ ∧ δ.lsMap[z]? = some g) := by
    intro z g
    simp only [data', getElem?_insert_ite]
    by_cases hz : ζ = z
    · subst hz
      simp only [ite_true, Option.some.injEq, true_and, ne_eq, not_true_eq_false, false_and,
        or_false]
      exact eq_comm
    · simp [hz, Ne.symm hz]
  have Hdisjδ' : ∀ (z1 z2 : Locale) (fs1 fs2 : GMap M.fmrole Nat), z1 ≠ z2 →
      data'[z1]? = some fs1 → data'[z2]? = some fs2 → fs1 ##ₘ fs2 := by
    intro z1 z2 fs1 fs2 Hneq H1 H2
    rw [disjoint_iff_mem]
    intro ρ Hρ1 Hρ2
    rcases (Hlk _ _).1 H1 with ⟨e1, e1'⟩ | ⟨hz1, O1⟩ <;>
    rcases (Hlk _ _).1 H2 with ⟨e2, e2'⟩ | ⟨hz2, O2⟩
    · exact Hneq (e1.trans e2.symm)
    · subst e1 e1'
      by_cases h : ρ ∈ fs
      · exact hz2 (ls_map_agree O2 Hζ (mem_dom.2 Hρ2) (mem_dom.2 h)).1
      · exact Hnew' ρ Hρ1 h z2 fs2 O2 Hρ2
    · subst e2 e2'
      by_cases h : ρ ∈ fs
      · exact hz1 (ls_map_agree O1 Hζ (mem_dom.2 Hρ1) (mem_dom.2 h)).1
      · exact Hnew' ρ Hρ2 h z1 fs1 O1 Hρ1
    · exact Hneq (ls_map_agree O1 O2 (mem_dom.2 Hρ1) (mem_dom.2 Hρ2)).1
  have Hliveδ' : ∀ ρ, ρ ∈ M.liveRoles m' →
      ∃ (z : Locale) (g : GMap M.fmrole Nat), data'[z]? = some g ∧ ρ ∈ dom g := by
    intro ρ Hlive
    by_cases Hwaslive : ρ ∈ M.liveRoles δ.lsUnder
    · obtain ⟨ζ', fs'', Hlk', Hdom⟩ := δ.ls_map_live ρ Hwaslive
      by_cases h : ζ' = ζ
      · subst h
        have e : fs'' = fs := Option.some.inj (Hlk'.symm.trans Hζ)
        subst e
        refine ⟨ζ', fs', (Hlk _ _).2 (.inl ⟨rfl, rfl⟩), mem_dom.2 ?_⟩
        exact Classical.byContradiction fun h => Hdead' ρ (mem_dom.1 Hdom) h Hwaslive
      · exact ⟨ζ', fs'', (Hlk _ _).2 (.inr ⟨h, Hlk'⟩), Hdom⟩
    · exact ⟨ζ, fs', (Hlk _ _).2 (.inl ⟨rfl, rfl⟩), mem_dom.2 ((Hborn' ρ).1 ⟨Hlive, Hwaslive⟩).1⟩
  have H0live : ρ0 ∈ M.liveRoles δ.lsUnder := M.fm_live_spec _ _ _ Htrans
  let δ' : LiveState Locale M := ⟨⟨m', data'⟩, Hdisjδ', Hliveδ'⟩
  have Hlk' : ∀ (z : Locale) (g : GMap M.fmrole Nat), δ'.lsMap[z]? = some g ↔
      (z = ζ ∧ g = fs') ∨ (z ≠ ζ ∧ δ.lsMap[z]? = some g) := Hlk
  have Hζ' : δ'.lsMap[ζ]? = some fs' := (Hlk' _ _).2 (.inl ⟨rfl, rfl⟩)
  -- the roles which have fuel in `δ'` but not in `δ` are new roles of `fs'`
  have Hnewdom : ∀ ρ, ρ ∈ dom (lsFuel (δ' : LiveStateData Locale M)) →
      ρ ∉ dom (lsFuel (δ : LiveStateData Locale M)) → ρ ∈ fs' ∧ ρ ∉ fs := by
    intro ρ Hin Hnin
    obtain ⟨z, g, Hz, Hinz⟩ := (mem_dom_lsFuel_iff δ' ρ).1 Hin
    rcases (Hlk' _ _).1 Hz with ⟨-, e⟩ | ⟨-, Oz⟩
    · subst e
      exact ⟨mem_dom.1 Hinz, fun h => Hnin (ls_fuel_dom_data ρ δ ζ fs Hζ (mem_dom.2 h))⟩
    · exact absurd (ls_fuel_dom_data ρ δ z g Oz Hinz) Hnin
  have H0dom : ρ0 ∈ fs' :=
    Classical.byContradiction fun h => Hdead' ρ0 (mem_dom.1 Hρ0in) h H0live
  refine ⟨δ', rfl, ?_⟩
  show M.fmtrans δ.lsUnder (some ρ0) m' ∧
    (lsMapping (δ : LiveStateData Locale M))[ρ0]? = some ζ ∧
    fuelDecr (some ζ) (some ρ0) (δ : LiveStateData Locale M) (δ' : LiveStateData Locale M) ∧
    fuelMustNotIncr (some ρ0) (δ : LiveStateData Locale M) (δ' : LiveStateData Locale M) ∧
    oleq (lsFuel (δ' : LiveStateData Locale M))[ρ0]? (some (fl m')) ∧
    (∀ ρ, ρ ∈ dom (lsFuel (δ' : LiveStateData Locale M)) \ dom (lsFuel (δ : LiveStateData Locale M)) →
      oleq (lsFuel (δ' : LiveStateData Locale M))[ρ]? (some (fl m'))) ∧
    dom (lsFuel (δ' : LiveStateData Locale M)) \ dom (lsFuel (δ : LiveStateData Locale M)) ⊆
      M.liveRoles m' \ M.liveRoles δ.lsUnder
  refine ⟨Htrans, ls_mapping_data ρ0 δ ζ fs Hζ Hρ0in, ?_, ?_, ?_, ?_, ?_⟩
  · -- fuel decreases
    intro ρ Hin Hin' Hmd
    obtain ⟨f, Hf⟩ := mem_dom_iff.1 Hin
    obtain ⟨f', Hf'⟩ := mem_dom_iff.1 Hin'
    rw [Hf, Hf']
    show f' < f
    obtain ⟨ζ1, fs1, H1, Hρ1⟩ := (lsFuel_getElem?_eq_some_iff δ ρ f).1 Hf
    cases Hmd with
    | sameTid tid Hneqρ Hsametid =>
      obtain ⟨fs0, H0, Hin0⟩ := (lsMapping_getElem?_eq_some_iff δ ρ ζ).1 Hsametid.symm
      have e : fs0 = fs := Option.some.inj (H0.symm.trans Hζ)
      subst e
      obtain ⟨e1, e1'⟩ := ls_map_agree H1 H0 (mem_dom_iff.2 ⟨f, Hρ1⟩) Hin0
      subst e1 e1'
      obtain ⟨ζ2, fs2, H2, Hρ2⟩ := (lsFuel_getElem?_eq_some_iff δ' ρ f').1 Hf'
      rcases (Hlk' _ _).1 H2 with ⟨-, e2'⟩ | ⟨hz2, O2⟩
      · subst e2'
        exact Hfs' ρ f f' Hρ2 (fun h => Hneqρ (congrArg some h)) Hρ1
      · exact absurd (ls_map_agree O2 H0 (mem_dom_iff.2 ⟨f', Hρ2⟩) Hin0).1 hz2
    | changeTid otid Hneqtid Hissome =>
      exfalso
      obtain ⟨ζ0, Hζ0⟩ := Option.isSome_iff_exists.1 Hissome
      rw [Hζ0] at Hneqtid
      obtain ⟨g0, H0, Hin0⟩ := (lsMapping_getElem?_eq_some_iff δ' ρ ζ0).1 Hζ0
      rcases (Hlk' _ _).1 H0 with ⟨e3, e3'⟩ | ⟨hz0, O0⟩
      · subst e3 e3'
        have : ρ ∈ fs := Classical.byContradiction fun h =>
          Hnew' ρ (mem_dom.1 Hin0) h ζ1 fs1 H1 (mem_of_getElem? Hρ1)
        exact Hneqtid (ls_mapping_data ρ δ ζ0 fs Hζ (mem_dom.2 this))
      · exact Hneqtid (ls_mapping_data ρ δ ζ0 g0 O0 Hin0)
  · -- fuel does not increase
    intro ρ Hin _
    obtain ⟨f, Hf⟩ := mem_dom_iff.1 Hin
    rw [Hf]
    obtain ⟨ζ1, fs1, H1, Hρ1⟩ := (lsFuel_getElem?_eq_some_iff δ ρ f).1 Hf
    by_cases hz : ζ1 = ζ
    · subst hz
      have e : fs1 = fs := Option.some.inj (H1.symm.trans Hζ)
      subst e
      by_cases h : ρ ∈ fs'
      · left
        obtain ⟨f', hf'⟩ := mem_iff_exists.1 h
        rw [ls_fuel_data ρ δ' ζ1 fs' f' Hζ' hf']
        refine Nat.le_of_lt (Hfs' ρ f f' hf' ?_ Hρ1)
        rintro rfl; contradiction
      · right
        refine ⟨fun Ha => ?_, Hdead' ρ (mem_of_getElem? Hρ1) h⟩
        obtain ⟨za, ga, Ha, Hina⟩ := (mem_dom_lsFuel_iff δ' ρ).1 Ha
        rcases (Hlk' _ _).1 Ha with ⟨-, e⟩ | ⟨hza, Oa⟩
        · subst e; exact h (mem_dom.1 Hina)
        · exact hza (ls_map_agree Oa H1 Hina (mem_dom.2 (mem_of_getElem? Hρ1))).1
    · left
      rw [ls_fuel_data ρ δ' ζ1 fs1 f ((Hlk' _ _).2 (.inr ⟨hz, H1⟩)) Hρ1]
      exact Nat.le_refl f
  · -- the fuel of `ρ0` is bounded
    obtain ⟨f'0, hf'0⟩ := mem_iff_exists.1 H0dom
    rw [ls_fuel_data ρ0 δ' ζ fs' f'0 Hζ' hf'0]
    exact Hfl0 f'0 hf'0
  · -- the fuel of new roles is bounded
    intro ρ Hρ
    rw [Iris.Std.mem_diff] at Hρ
    obtain ⟨Hn1, Hn2⟩ := Hnewdom ρ Hρ.1 Hρ.2
    obtain ⟨f', hf'⟩ := mem_iff_exists.1 Hn1
    rw [ls_fuel_data ρ δ' ζ fs' f' Hζ' hf']
    refine Hfln ρ ?_ f' hf'
    rw [Iris.Std.mem_diff, mem_dom, mem_dom]
    exact ⟨Hn1, Hn2⟩
  · -- new roles are born
    intro ρ Hρ
    rw [Iris.Std.mem_diff] at Hρ ⊢
    exact (Hborn' ρ).2 (Hnewdom ρ Hρ.1 Hρ.2)

end fairness

/-! ## Live models -/

/-- A live model (Rocq `LiveModel`), given by a fuel limit. The Rocq let-fields `lm_ls`,
`lm_lbl` and `lm_ls_trans` are `LiveModel.lmLs`, `LiveModel.lmLbl` and
`LiveModel.lmLsTrans`. -/
@[rocq_alias trillium.fairis.LiveModel]
structure LiveModel (Locale : Type _) (M : FairModel) where
  /-- The maximal fuel given to roles (Rocq `lm_fl`). -/
  lmFl : M.fmstate → Nat

namespace LiveModel

variable {Locale : Type _} [Ord Locale] [Std.TransOrd Locale] [Std.LawfulEqOrd Locale]
variable {M : FairModel}

/-- The states of a live model (Rocq `lm_ls`). -/
abbrev lmLs (_LM : LiveModel Locale M) : Type _ := LiveState Locale M

/-- The labels of a live model (Rocq `lm_lbl`). -/
abbrev lmLbl (_LM : LiveModel Locale M) : Type _ := FairLabel M.fmrole Locale

/-- The transition relation of a live model (Rocq `lm_ls_trans`). -/
abbrev lmLsTrans (LM : LiveModel Locale M) (δ : LiveState Locale M)
    (ℓ : FairLabel M.fmrole Locale) (δ' : LiveState Locale M) : Prop :=
  lsTrans LM.lmFl (δ : LiveStateData Locale M) ℓ (δ' : LiveStateData Locale M)

/-- The model of a live model (Rocq `fair_model_model`, and the coercion
`live_model_to_model`). -/
@[rocq_alias trillium.fairis.fair_model_model, rocq_alias trillium.fairis.live_model_to_model]
abbrev toModel (LM : LiveModel Locale M) : Model where
  mstate := LiveState Locale M
  mlabel := FairLabel M.fmrole Locale
  mtrans := LM.lmLsTrans

instance : CoeOut (LiveModel Locale M) Model := ⟨LiveModel.toModel⟩

end LiveModel

section fairness

variable {Locale : Type _} [Ord Locale] [Std.TransOrd Locale] [Std.LawfulEqOrd Locale]
variable {M : FairModel}

/-- All the locales owning roles are threads of `c` (Rocq `tids_smaller`). -/
@[rocq_alias trillium.fairis.tids_smaller]
def tidsSmaller {Expr State : Type _} [LanguageCore Expr State Locale] [DecidableEq Locale]
    (c : List Expr) (δ : LiveState Locale M) : Prop :=
  ∀ ζ, ζ ∈ dom δ.lsMap → (fromLocale c ζ).isSome

/-- The initial live state: the locale `ζ0` owns all live roles, with maximal fuel (Rocq
`initial_ls`). -/
@[rocq_alias trillium.fairis.initial_ls]
def initialLs (LM : LiveModel Locale M) (s0 : M.fmstate) (ζ0 : Locale) : LM.lmLs where
  lsUnder := s0
  lsMap := GMap.singleton ζ0 (GSet.toGMap (LM.lmFl s0) (M.liveRoles s0))
  ls_map_disj := by
    intro z1 z2 fs1 fs2 Hneq H1 H2
    rw [getElem?_singleton] at H1 H2
    split at H1 <;> split at H2 <;> simp_all
  ls_map_live := by
    intro ρ Hρ
    refine ⟨ζ0, GSet.toGMap (LM.lmFl s0) (M.liveRoles s0), by simp [getElem?_singleton], ?_⟩
    rw [mem_dom, mem_toGMap]
    exact Hρ

/-- The label of an execution step matches the label of a live-model step (Rocq
`labels_match`). -/
@[rocq_alias trillium.fairis.labels_match]
def labelsMatch {Role : Type _} (oζ : Option Locale) (ℓ : FairLabel Role Locale) : Prop :=
  match oζ, ℓ with
  | none, .configStep => True
  | some ζ, .silentStep ζ' => ζ = ζ'
  | some ζ, .takeStep _ ζ' => ζ = ζ'
  | _, _ => False

end fairness

/-- Traces of a live model (Rocq `auxtrace`). -/
@[rocq_alias trillium.fairis.auxtrace]
abbrev Auxtrace {Locale : Type _} [Ord Locale] [Std.TransOrd Locale] [Std.LawfulEqOrd Locale]
    {M : FairModel} (_LM : LiveModel Locale M) : Type _ :=
  Trace (LiveState Locale M) (FairLabel M.fmrole Locale)

section aux_trace

variable {Locale : Type _} [Ord Locale] [Std.TransOrd Locale] [Std.LawfulEqOrd Locale]
variable {M : FairModel} {LM : LiveModel Locale M}

/-- Rocq `role_enabled`. -/
@[rocq_alias trillium.fairis.role_enabled]
def roleEnabled (ρ : M.fmrole) (δ : LiveState Locale M) : Prop := ρ ∈ M.liveRoles δ.lsUnder

/-- Fairness of an auxiliary trace w.r.t. the role `ρ` (Rocq `fair_aux`). -/
@[rocq_alias trillium.fairis.fair_aux]
def fairAux (ρ : M.fmrole) (auxtr : Auxtrace LM) : Prop :=
  ∀ n, predAt auxtr n (fun δ _ => roleEnabled ρ δ) →
    ∃ m, predAt auxtr (n + m) (fun δ _ => ¬ roleEnabled ρ δ) ∨
      predAt auxtr (n + m) (fun _ ℓ => ∃ tid, ℓ = some (.takeStep ρ tid))

@[rocq_alias trillium.fairis.fair_aux_after]
theorem fair_aux_after (ρ : M.fmrole) (auxtr : Auxtrace LM) (n : Nat) (auxtr' : Auxtrace LM) :
    fairAux ρ auxtr → after n auxtr = some auxtr' → fairAux ρ auxtr' := by
  intro Hfair Hafter m Hpa
  have Hpa' : predAt auxtr (n + m) (fun δ _ => roleEnabled ρ δ) := by
    rw [pred_at_sum, Hafter]; exact Hpa
  obtain ⟨p, Hp⟩ := Hfair (n + m) Hpa'
  refine ⟨p, ?_⟩
  rw [Nat.add_assoc, pred_at_sum, pred_at_sum, Hafter] at Hp
  exact Hp

variable (LM) in
/-- Every step of the auxiliary trace is a transition of the live model (Rocq's coinductive
`auxtrace_valid`, here `TraceValid` of the transition relation). -/
@[rocq_alias trillium.fairis.auxtrace_valid]
abbrev AuxtraceValid (tr : Auxtrace LM) : Prop := TraceValid LM.lmLsTrans tr

/-- Rocq `auxtrace_valid_forall` (the `match` on `after n tr` is stated for its `cons`
case). -/
@[rocq_alias trillium.fairis.auxtrace_valid_forall]
theorem auxtrace_valid_forall (tr : Auxtrace LM) :
    AuxtraceValid LM tr → ∀ n δ ℓ tr', after n tr = some (δ -[ℓ]-> tr') →
      LM.lmLsTrans δ ℓ tr'.first := by
  intro Hval n δ ℓ tr' Hafter
  exact (trace_valid_cons_inv _ _ _ (trace_valid_after _ _ n Hafter Hval)).2

end aux_trace

section live_tids

variable {Locale : Type _} [Ord Locale] [Std.TransOrd Locale] [Std.LawfulEqOrd Locale]
  [DecidableEq Locale]
variable {M : FairModel}
variable {Expr Val Ectx State : Type _} [Language Expr Val Ectx State Locale]

/-- The owners of roles are threads of the configuration, and roles owned by finished threads
are not live (Rocq `live_tids`). -/
@[rocq_alias trillium.fairis.live_tids]
def liveTids (c : List Expr × State) (δ : LiveState Locale M) : Prop :=
  (∀ (ρ : M.fmrole) (ζ : Locale), (lsMapping (δ : LiveStateData Locale M))[ρ]? = some ζ → (fromLocale c.1 ζ).isSome) ∧
  ∀ ζ e, fromLocale c.1 ζ = some e → toVal e ≠ none →
    ∀ ρ : M.fmrole, (lsMapping (δ : LiveStateData Locale M))[ρ]? = some ζ → ρ ∉ M.liveRoles δ.lsUnder

variable (Expr) in
/-- An execution trace and an auxiliary trace match (Rocq `exaux_traces_match`). -/
@[rocq_alias trillium.fairis.exaux_traces_match]
abbrev ExauxTracesMatch (LM : LiveModel Locale M) : Extrace Expr → Auxtrace LM → Prop :=
  TracesMatch labelsMatch liveTids (Language.LocaleStep (Expr := Expr)) LM.lmLsTrans

end live_tids

section fairness_preserved

variable {Locale : Type _} [Ord Locale] [Std.TransOrd Locale] [Std.LawfulEqOrd Locale]
  [DecidableEq Locale]
variable {M : FairModel} {LM : LiveModel Locale M}
variable {Expr Val Ectx State : Type _} [Language Expr Val Ectx State Locale]

@[rocq_alias trillium.fairis.exaux_preserves_validity]
theorem exaux_preserves_validity (extr : Extrace Expr) (auxtr : Auxtrace LM) :
    ExauxTracesMatch Expr LM extr auxtr → AuxtraceValid LM auxtr :=
  traces_match_valid2 extr auxtr

@[rocq_alias trillium.fairis.exaux_preserves_termination]
theorem exaux_preserves_termination (extr : Extrace Expr) (auxtr : Auxtrace LM) :
    ExauxTracesMatch Expr LM extr auxtr → terminatingTrace auxtr → terminatingTrace extr :=
  traces_match_preserves_termination extr auxtr

@[rocq_alias trillium.fairis.traces_match_labels]
theorem traces_match_labels (tid : Locale) (ℓ : FairLabel M.fmrole Locale)
    (c : List Expr × State) (δ : LiveState Locale M) (rex : Extrace Expr) (raux : Auxtrace LM) :
    ExauxTracesMatch Expr LM (c -[some tid]-> rex) (δ -[ℓ]-> raux) →
      (∃ ρ, ℓ = .takeStep ρ tid) ∨ ℓ = .silentStep tid := by
  intro Hm
  have Hl := Hm.cons_inv.1
  cases ℓ with
  | takeStep ρ ζ => exact .inl ⟨ρ, by rw [show ζ = tid from Hl.symm]⟩
  | silentStep ζ => exact .inr (by rw [show ζ = tid from Hl.symm])
  | configStep => exact Hl.elim

@[rocq_alias trillium.fairis.mapping_live_role]
theorem mapping_live_role (δ : LiveState Locale M) (ρ : M.fmrole) :
    ρ ∈ M.liveRoles δ.lsUnder → ((lsMapping (δ : LiveStateData Locale M))[ρ]?).isSome := by
  intro H
  have := ls_mapping_dom δ ρ H
  rw [mem_dom, Std.ExtTreeMap.mem_iff_isSome_getElem?] at this
  exact this

@[rocq_alias trillium.fairis.fuel_live_role]
theorem fuel_live_role (δ : LiveState Locale M) (ρ : M.fmrole) :
    ρ ∈ M.liveRoles δ.lsUnder → ((lsFuel (δ : LiveStateData Locale M))[ρ]?).isSome := by
  intro H
  have := ls_fuel_dom δ ρ H
  rw [mem_dom, Std.ExtTreeMap.mem_iff_isSome_getElem?] at this
  exact this

@[rocq_alias trillium.fairis.match_locale_enabled]
theorem match_locale_enabled (extr : Extrace Expr) (auxtr : Auxtrace LM) (ζ : Locale)
    (ρ : M.fmrole) :
    ρ ∈ M.liveRoles auxtr.first.lsUnder → ExauxTracesMatch Expr LM extr auxtr →
      (lsMapping (auxtr.first : LiveStateData Locale M))[ρ]? = some ζ →
      localeEnabled ζ extr.first := by
  intro Hlive Hm Hloc
  obtain ⟨HiS, Hneqloc⟩ := traces_match_first _ _ Hm
  obtain ⟨e, Hein⟩ := Option.isSome_iff_exists.1 (HiS _ _ Hloc)
  refine ⟨e, Hein, ?_⟩
  cases Heqe : toVal e with
  | none => rfl
  | some v => exact absurd Hlive (Hneqloc ζ e Hein (by rw [Heqe]; simp) ρ Hloc)

/-- The statement proved by well-founded induction in `fairness_preserved_ind` (Rocq
`fairness_induction_stmt`). -/
@[rocq_alias trillium.fairis.fairness_induction_stmt]
def FairnessInductionStmt (ρ : M.fmrole) (fm : ℕ × ℕ) (f m : Nat) (ζ : Locale)
    (extr : Extrace Expr) (auxtr : Auxtrace LM) (δ : LiveState Locale M)
    (c : List Expr × State) : Prop :=
  infiniteTrace extr → (∀ ζ, fairEx ζ extr) → fm = (f, m) →
    ExauxTracesMatch Expr LM extr auxtr → c = extr.first → δ = auxtr.first →
    (lsFuel (δ : LiveStateData Locale M))[ρ]? = some f →
    (lsMapping (δ : LiveStateData Locale M))[ρ]? = some ζ →
    (predAt extr m (fun c _ => ¬ localeEnabled ζ c) ∨
      predAt extr m (fun _ oζ => oζ = some (some ζ))) →
    ∃ M0, predAt auxtr M0 (fun δ _ => ¬ roleEnabled ρ δ) ∨
      predAt auxtr M0 (fun _ ℓ => ∃ ζ0, ℓ = some (.takeStep ρ ζ0))

@[rocq_alias trillium.fairis.pred_at_step_helper]
theorem pred_at_step_helper (extr' : Extrace Expr) (p : Nat) (ζ' : Locale) :
    predAt extr' p (fairnessSat (localeEnabled (Expr := Expr)) tidMatch ζ') ↔
      predAt extr' p (fun x y => ¬ localeEnabled ζ' x ∨ y = some (some ζ')) := by
  apply pred_at_iff
  intro x y
  unfold fairnessSat tidMatch
  refine or_congr .rfl ⟨?_, ?_⟩
  · rintro ⟨_, rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨_, rfl, rfl⟩

@[rocq_alias trillium.fairis.case1]
theorem case1 (ρ : M.fmrole) (f m : Nat) (extr' : Extrace Expr) (auxtr' : Auxtrace LM)
    (δ : LiveState Locale M) (ℓ : FairLabel M.fmrole Locale) :
    (∀ m0 : ℕ × ℕ, strict ltLex m0 (f, m) →
      ∀ (f m : Nat) (ζ : Locale) (extr : Extrace Expr) (auxtr : Auxtrace LM)
        (δ : LiveState Locale M) (c : List Expr × State),
        FairnessInductionStmt ρ m0 f m ζ extr auxtr δ c) →
    (ρ ∈ dom (lsFuel (auxtr'.first : LiveStateData Locale M)) →
      oless (lsFuel (auxtr'.first : LiveStateData Locale M))[ρ]?
        (lsFuel (δ : LiveStateData Locale M))[ρ]?) →
    ExauxTracesMatch Expr LM extr' auxtr' → infiniteTrace extr' →
    (lsFuel (δ : LiveStateData Locale M))[ρ]? = some f → (∀ ζ, fairEx ζ extr') →
    ∃ M0, predAt (δ -[ℓ]-> auxtr') M0 (fun δ0 _ => ¬ roleEnabled ρ δ0) ∨
      predAt (δ -[ℓ]-> auxtr') M0 (fun _ ℓ => ∃ ζ0, ℓ = some (.takeStep ρ ζ0)) := by
  intro IH Hdec Hmatch Hinf Hsome Hfair
  rw [Hsome] at Hdec
  cases Heq : (lsFuel (auxtr'.first : LiveStateData Locale M))[ρ]? with
  | some f' =>
    by_cases Hρlive' : ρ ∈ M.liveRoles auxtr'.first.lsUnder
    swap
    · refine ⟨1, .inl ?_⟩
      rw [show (1 : Nat) = 0 + 1 from rfl, pred_at_S, pred_at_state_trfirst (P := fun δ0 => ¬ roleEnabled ρ δ0)]
      exact Hρlive'
    obtain ⟨ζ', Hζ'⟩ := Option.isSome_iff_exists.1 (mapping_live_role _ ρ Hρlive')
    have Hloc'en : predAt extr' 0 (fun c _ => localeEnabled ζ' c) := by
      rw [pred_at_state_trfirst (P := fun c => localeEnabled ζ' c)]
      exact match_locale_enabled extr' auxtr' ζ' ρ Hρlive' Hmatch Hζ'
    obtain ⟨p, Hp⟩ := Hfair ζ' 0 Hloc'en
    rw [Nat.zero_add] at Hp
    have Hlt : f' < f := by
      have := Hdec (mem_dom_iff.2 ⟨f', Heq⟩)
      rw [Heq] at this
      exact this
    obtain ⟨P, Hind⟩ := IH (f', p) ⟨.inl Hlt, fun h => by simp only [ltLex] at h; omega⟩
      f' p ζ' extr' auxtr' auxtr'.first extr'.first Hinf Hfair rfl Hmatch rfl rfl Heq Hζ'
      (by rw [pred_at_or]; exact (pred_at_step_helper extr' p ζ').1 Hp)
    exact ⟨P + 1, by simpa only [pred_at_S] using Hind⟩
  | none =>
    refine ⟨1, .inl ?_⟩
    rw [show (1 : Nat) = 0 + 1 from rfl, pred_at_S, pred_at_state_trfirst (P := fun δ0 => ¬ roleEnabled ρ δ0)]
    intro Hlive
    have := fuel_live_role _ ρ Hlive
    rw [Heq] at this
    cases this

/-- In a step of a locale which is not the owner `ζ` of `ρ`, the fuel of `ρ` does not
increase, and it decreases if `ρ` changes owner. -/
private theorem other_step_fuel {fl : M.fmstate → Nat} {δ δ' : LiveState Locale M}
    {ℓ : FairLabel M.fmrole Locale} {oζ : Option Locale} {ρ : M.fmrole} {ζ : Locale}
    (Hl : labelsMatch oζ ℓ) (Hls : lsTrans fl (δ : LiveStateData Locale M) ℓ δ')
    (Hne : some ζ ≠ oζ) (Hmap : (lsMapping (δ : LiveStateData Locale M))[ρ]? = some ζ) :
    ∃ oρ, some ρ ≠ oρ ∧ fuelMustNotIncr oρ (δ : LiveStateData Locale M) δ' ∧
      fuelDecr oζ oρ (δ : LiveStateData Locale M) δ' := by
  cases ℓ with
  | takeStep ρ0 ζ0 =>
    cases oζ with
    | none => exact Hl.elim
    | some ζ1 =>
      obtain rfl : ζ1 = ζ0 := Hl
      obtain ⟨-, Hmap0, Hdec, Hni, -⟩ := Hls
      refine ⟨some ρ0, ?_, Hni, Hdec⟩
      intro h
      cases h
      rw [Hmap] at Hmap0
      exact Hne (by rw [Hmap0])
  | silentStep ζ0 =>
    cases oζ with
    | none => exact Hl.elim
    | some ζ1 =>
      obtain rfl : ζ1 = ζ0 := Hl
      obtain ⟨-, Hdec, Hni, -⟩ := Hls
      exact ⟨none, by simp, Hni, Hdec⟩
  | configStep => exact Hls.2.2.2.2.elim

@[rocq_alias trillium.fairis.fairness_preserved_ind]
theorem fairness_preserved_ind (ρ : M.fmrole) :
    ∀ fm f m ζ (extr : Extrace Expr) (auxtr : Auxtrace LM) δ c,
      FairnessInductionStmt ρ fm f m ζ extr auxtr δ c := by
  intro fm
  refine lex_ind fm (fun fm => ∀ f m ζ (extr : Extrace Expr) (auxtr : Auxtrace LM) δ c,
    FairnessInductionStmt ρ fm f m ζ extr auxtr δ c) ?_
  intro fm IH f m ζ extr auxtr δ c Hexinfin Hfair Hfm Htm Hc Hδ Hfuel Hmapping Hexen
  subst Hfm Hc Hδ
  cases extr using Trace.casesOn' with
  | singl c => simpa using Hexinfin 1
  | cons c ζ' extr' =>
  have Hfair' : ∀ ζ, fairEx ζ extr' := fun ζ => fair_by_cons _ _ ζ c ζ' extr' (Hfair ζ)
  have Hinf' : infiniteTrace extr' := infinite_cons _ _ _ Hexinfin
  cases auxtr using Trace.casesOn' with
  | singl δ => exact Htm.cons_singl_false.elim
  | cons δ ℓ auxtr' =>
  obtain ⟨Hl, Hs, -, Hls, Hmatchrest⟩ := Htm.cons_inv
  simp only [first_cons] at Hfuel Hmapping
  by_cases Hρlive : ρ ∈ M.liveRoles δ.lsUnder
  swap
  · exact ⟨0, .inl (by rw [pred_at_0]; exact Hρlive)⟩
  have Hρdom : ρ ∈ dom (lsFuel (δ : LiveStateData Locale M)) := ls_fuel_dom δ ρ Hρlive
  by_cases Hζ : some ζ = ζ'
  · subst Hζ
    rcases traces_match_labels ζ ℓ c δ extr' auxtr' Htm with ⟨ρ', rfl⟩ | rfl
    · by_cases Hρeq : ρ = ρ'
      · subst Hρeq
        exact ⟨0, .inr (by rw [pred_at_0]; exact ⟨ζ, rfl⟩)⟩
      · obtain ⟨-, Hsame, Hdec, -, -⟩ := Hls
        have Hmustdec : MustDecrease ρ (some ρ') (δ : LiveStateData Locale M)
            (auxtr'.first : LiveStateData Locale M) (some ζ) :=
          .sameTid ζ (fun h => Hρeq (Option.some.inj h)) Hmapping.symm
        exact case1 ρ f m extr' auxtr' δ _ IH (fun Hin => Hdec ρ Hρdom Hin Hmustdec)
          Hmatchrest Hinf' Hfuel Hfair'
    · obtain ⟨-, Hlsdec, -, -⟩ := Hls
      have Hmustdec : MustDecrease ρ none (δ : LiveStateData Locale M)
          (auxtr'.first : LiveStateData Locale M) (some ζ) :=
        .sameTid ζ (by simp) Hmapping.symm
      exact case1 ρ f m extr' auxtr' δ _ IH (fun Hin => Hlsdec ρ Hρdom Hin Hmustdec)
        Hmatchrest Hinf' Hfuel Hfair'
  · -- another locale takes a step
    by_cases Hρlive' : ρ ∈ M.liveRoles auxtr'.first.lsUnder
    swap
    · refine ⟨1, .inl ?_⟩
      rw [show (1 : Nat) = 0 + 1 from rfl, pred_at_S,
        pred_at_state_trfirst (P := fun δ0 => ¬ roleEnabled ρ δ0)]
      exact Hρlive'
    have Hρdom' : ρ ∈ dom (lsFuel (auxtr'.first : LiveStateData Locale M)) :=
      ls_fuel_dom _ ρ Hρlive'
    obtain ⟨ζ'', Hζ''⟩ := Option.isSome_iff_exists.1 (mapping_live_role _ ρ Hρlive')
    obtain ⟨oρ, Hneqρ, Hni, Hdec⟩ := other_step_fuel Hl Hls Hζ Hmapping
    have Hζ''en : predAt extr' 0 (fun c _ => localeEnabled ζ'' c) := by
      rw [pred_at_state_trfirst (P := fun c => localeEnabled ζ'' c)]
      exact match_locale_enabled extr' auxtr' ζ'' ρ Hρlive' Hmatchrest Hζ''
    by_cases Hchange : ζ = ζ''
    · subst Hchange
      obtain ⟨f', Hfuel', Hff'⟩ : ∃ f', (lsFuel (auxtr'.first : LiveStateData Locale M))[ρ]? =
          some f' ∧ f' ≤ f := by
        rcases Hni ρ Hρdom Hneqρ with Hni | ⟨Hni, -⟩
        · rw [Hfuel] at Hni
          obtain ⟨f', Hf'⟩ := mem_dom_iff.1 Hρdom'
          rw [Hf'] at Hni
          exact ⟨f', Hf', Hni⟩
        · exact absurd Hρdom' Hni
      cases m with
      | zero =>
        exfalso
        rw [pred_at_0, pred_at_0] at Hexen
        rcases Hexen with Hexen | Hexen
        · exact Hexen (match_locale_enabled _ (δ -[ℓ]-> auxtr') ζ ρ Hρlive Htm Hmapping)
        · exact Hζ (Option.some.inj Hexen).symm
      | succ m' =>
        rw [pred_at_S, pred_at_S] at Hexen
        obtain ⟨P, Hind⟩ := IH (f', m') ⟨by simp only [ltLex]; omega,
            fun h => by simp only [ltLex] at h; omega⟩
          f' m' ζ extr' auxtr' auxtr'.first extr'.first Hinf' Hfair' rfl Hmatchrest rfl rfl
          Hfuel' Hζ'' Hexen
        exact ⟨P + 1, by simpa only [pred_at_S] using Hind⟩
    · obtain ⟨f', Hfuel', Hff'⟩ : ∃ f', (lsFuel (auxtr'.first : LiveStateData Locale M))[ρ]? =
          some f' ∧ f' < f := by
        have Hmd : MustDecrease ρ oρ (δ : LiveStateData Locale M)
            (auxtr'.first : LiveStateData Locale M) ζ' :=
          .changeTid ζ' (by rw [Hmapping, Hζ'']; exact fun h => Hchange (Option.some.inj h))
            (by rw [Hζ'']; rfl)
        have := Hdec ρ Hρdom Hρdom' Hmd
        rw [Hfuel] at this
        obtain ⟨f', Hf'⟩ := mem_dom_iff.1 Hρdom'
        rw [Hf'] at this
        exact ⟨f', Hf', this⟩
      obtain ⟨p, Hp⟩ := Hfair' ζ'' 0 Hζ''en
      rw [Nat.zero_add] at Hp
      obtain ⟨P, Hind⟩ := IH (f', p) ⟨.inl Hff', fun h => by simp only [ltLex] at h; omega⟩
        f' p ζ'' extr' auxtr' auxtr'.first extr'.first Hinf' Hfair' rfl Hmatchrest rfl rfl
        Hfuel' Hζ'' (by rw [pred_at_or]; exact (pred_at_step_helper extr' p ζ'').1 Hp)
      exact ⟨P + 1, by simpa only [pred_at_S] using Hind⟩

@[rocq_alias trillium.fairis.fairness_preserved]
theorem fairness_preserved (extr : Extrace Expr) (auxtr : Auxtrace LM) :
    infiniteTrace extr → ExauxTracesMatch Expr LM extr auxtr →
      (∀ ζ, fairEx ζ extr) → ∀ ρ, fairAux ρ auxtr := by
  intro Hinfin Hmatch Hex ρ n Hn
  cases Heq : after n auxtr with
  | none => rw [predAt, Heq] at Hn; exact Hn.elim
  | some tr =>
  rw [predAt_some Heq] at Hn
  have Hen : roleEnabled ρ tr.first := Hn
  obtain ⟨ζ, Hζ⟩ := Option.isSome_iff_exists.1 (mapping_live_role _ ρ Hen)
  obtain ⟨f, Hfuel⟩ := Option.isSome_iff_exists.1 (fuel_live_role _ ρ Hen)
  obtain ⟨tr1', Heq', Htr⟩ := traces_match_after extr auxtr n tr Hmatch Heq
  have Hpa : predAt extr n (fun c _ => localeEnabled ζ c) := by
    rw [predAt_some Heq']
    exact match_locale_enabled tr1' tr ζ ρ Hen Htr Hζ
  obtain ⟨m, Hm⟩ := Hex ζ n Hpa
  rw [pred_at_sum, Heq'] at Hm
  have Hinf' : infiniteTrace tr1' := by
    have := infinite_trace_after n extr
    rw [Heq'] at this
    exact this Hinfin
  obtain ⟨M0, HM0⟩ := fairness_preserved_ind ρ (f, m) f m ζ tr1' tr tr.first tr1'.first Hinf'
    (fun ζ => fair_by_after _ _ ζ extr tr1' n Heq' (Hex ζ)) rfl Htr rfl rfl Hfuel Hζ
    (by rw [pred_at_or]; exact (pred_at_step_helper tr1' m ζ).1 Hm)
  refine ⟨M0, ?_⟩
  rw [pred_at_sum, pred_at_sum, Heq]
  exact HM0

end fairness_preserved

section valid_lift

variable {Locale : Type _} [Ord Locale] [Std.TransOrd Locale] [Std.LawfulEqOrd Locale]
  [DecidableEq Locale]
variable {M : FairModel}
variable {Expr Val Ectx State : Type _} [Language Expr Val Ectx State Locale]

variable (LM : LiveModel Locale M) in
/-- The last steps of the execution and of the auxiliary trace match (Rocq
`valid_state_evolution_fairness`). -/
@[rocq_alias trillium.fairis.valid_state_evolution_fairness]
def validStateEvolutionFairness (extr : ExecutionTrace Expr)
    (auxtr : AuxiliaryTrace LM.toModel) : Prop :=
  match extr, auxtr with
  | .extend _ oζ c, .extend auxtr ℓ δ =>
    labelsMatch oζ ℓ ∧ LM.lmLsTrans auxtr.last ℓ δ ∧ tidsSmaller c.1 δ
  | _, _ => True

variable (LM : LiveModel Locale M) in
/-- Rocq `valid_lift_fairness`. -/
@[rocq_alias trillium.fairis.valid_lift_fairness]
def validLiftFairness (φ : ExecutionTrace Expr → AuxiliaryTrace LM.toModel → Prop)
    (extr : ExecutionTrace Expr) (auxtr : AuxiliaryTrace LM.toModel) : Prop :=
  validStateEvolutionFairness LM extr auxtr ∧ φ extr auxtr

/-- The first state of a trace matching an execution is the last state of the execution. -/
private theorem execTraceMatch_first {S L : Type _} {ft : FiniteTrace S L} {il : Stream'.Seq (L × S)}
    {tr : Trace S L} (h : ExecTraceMatch ft il tr) : tr.first = ft.last := by
  rcases h.inv with ⟨s, hs, -, rfl⟩ | ⟨s, ℓ, ift, tr', -, -, rfl⟩
  · exact hs.symm
  · rfl

@[rocq_alias trillium.fairis.valid_inf_system_trace_implies_traces_match_strong]
theorem valid_inf_system_trace_implies_traces_match_strong (LM : LiveModel Locale M)
    (φ : ExecutionTrace Expr → AuxiliaryTrace LM.toModel → Prop)
    (ψ : List Expr × State → LiveState Locale M → Prop)
    (ex : ExecutionTrace Expr) (atr : AuxiliaryTrace LM.toModel) (iex : InfExecutionTrace Expr)
    (iatr : InfAuxiliaryTrace LM.toModel) (progtr : Extrace Expr) (auxtr : Auxtrace LM) :
    (∀ (ex : ExecutionTrace Expr) (atr : AuxiliaryTrace LM.toModel), φ ex atr →
      liveTids (M := M) ex.last atr.last) →
    (∀ (ex : ExecutionTrace Expr) (atr : AuxiliaryTrace LM.toModel), φ ex atr →
      validStateEvolutionFairness LM ex atr) →
    (∀ extr auxtr, φ extr auxtr → ψ extr.last auxtr.last) →
    ExecTraceMatch ex iex progtr → ExecTraceMatch atr iatr auxtr →
    ValidInfSystemTrace φ ex atr iex iatr →
    TracesMatch labelsMatch (fun σ δ => liveTids σ δ ∧ ψ σ δ)
      (Language.LocaleStep (Expr := Expr)) LM.lmLsTrans progtr auxtr := by
  intro Hφ1 Hφ2 Hφψ Hem Ham Hval
  refine TracesMatch.coinduct _ _ _ _ (fun progtr auxtr => ∃ ex atr iex iatr,
    ExecTraceMatch ex iex progtr ∧ ExecTraceMatch atr iatr auxtr ∧
      ValidInfSystemTrace φ ex atr iex iatr) ?_ progtr auxtr ⟨ex, atr, iex, iatr, Hem, Ham, Hval⟩
  rintro progtr auxtr ⟨ex, atr, iex, iatr, Hem, Ham, Hval⟩
  rw [ValidInfSystemTrace.eq_def] at Hval
  rcases Hval with ⟨Hphi, rfl, rfl⟩ |
    ⟨c, c', δ', iex', iatr', ζ, ℓ, Hphi, Hends, Hstep, Hval', rfl, rfl⟩
  · rcases Hem.inv with ⟨s, Hs, -, rfl⟩ | ⟨_, _, _, _, -, Hnil, -⟩
    · rcases Ham.inv with ⟨s', Hs', -, rfl⟩ | ⟨_, _, _, _, -, Hnil', -⟩
      · subst Hs Hs'
        exact .inl ⟨_, _, ⟨Hφ1 ex atr Hphi, Hφψ ex atr Hphi⟩, rfl, rfl⟩
      · exact absurd Hnil'.symm Stream'.Seq.cons_ne_nil
    · exact absurd Hnil.symm Stream'.Seq.cons_ne_nil
  · rcases Hem.inv with ⟨_, _, Hnil, -⟩ | ⟨s, ζ1, ift, tr', Hem', Hcons, rfl⟩
    · exact absurd Hnil Stream'.Seq.cons_ne_nil
    rcases Ham.inv with ⟨_, _, Hnil, -⟩ | ⟨s', ℓ1, iatr1, auxtr', Ham', Hcons', rfl⟩
    · exact absurd Hnil Stream'.Seq.cons_ne_nil
    obtain ⟨h1, rfl⟩ := Stream'.Seq.cons_injective2 Hcons
    obtain ⟨h1', rfl⟩ := Stream'.Seq.cons_injective2 Hcons'
    simp only [Prod.mk.injEq] at h1 h1'
    obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨rfl, rfl⟩ := h1'
    have Hphi' := Hval'.inv
    obtain ⟨Hlab, Htrans, -⟩ := Hφ2 _ _ Hphi'
    refine .inr ⟨ex.last, _, tr', atr.last, _, auxtr', Hlab,
      ⟨Hφ1 ex atr Hphi, Hφψ ex atr Hphi⟩, ?_, ?_, ⟨_, _, _, _, Hem', Ham', Hval'⟩, rfl, rfl⟩
    · rw [execTraceMatch_first Hem', FiniteTrace.endsIn_iff.1 Hends]
      exact Hstep
    · rw [execTraceMatch_first Ham']
      exact Htrans

@[rocq_alias trillium.fairis.valid_inf_system_trace_implies_traces_match]
theorem valid_inf_system_trace_implies_traces_match (LM : LiveModel Locale M)
    (φ : ExecutionTrace Expr → AuxiliaryTrace LM.toModel → Prop)
    (ex : ExecutionTrace Expr) (atr : AuxiliaryTrace LM.toModel) (iex : InfExecutionTrace Expr)
    (iatr : InfAuxiliaryTrace LM.toModel) (progtr : Extrace Expr) (auxtr : Auxtrace LM) :
    (∀ (ex : ExecutionTrace Expr) (atr : AuxiliaryTrace LM.toModel), φ ex atr →
      liveTids (M := M) ex.last atr.last) →
    (∀ (ex : ExecutionTrace Expr) (atr : AuxiliaryTrace LM.toModel), φ ex atr →
      validStateEvolutionFairness LM ex atr) →
    ExecTraceMatch ex iex progtr → ExecTraceMatch atr iatr auxtr →
    ValidInfSystemTrace φ ex atr iex iatr →
    ExauxTracesMatch Expr LM progtr auxtr := by
  intro Hφ1 Hφ2 Hem Ham Hval
  have H := valid_inf_system_trace_implies_traces_match_strong LM φ (fun _ _ => True) ex atr iex
    iatr progtr auxtr Hφ1 Hφ2 (fun _ _ _ => trivial) Hem Ham Hval
  refine TracesMatch.coinduct _ _ _ _ (fun progtr auxtr =>
    TracesMatch labelsMatch (fun σ δ => liveTids σ δ ∧ True)
      (Language.LocaleStep (Expr := Expr)) LM.lmLsTrans progtr auxtr) ?_ progtr auxtr H
  intro tr1 tr2 Hm
  rcases Hm.inv with ⟨s1, s2, h, rfl, rfl⟩ |
    ⟨s1, ℓ1, r1, s2, ℓ2, r2, h1, h2, h3, h4, h5, rfl, rfl⟩
  · exact .inl ⟨s1, s2, h.1, rfl, rfl⟩
  · exact .inr ⟨s1, ℓ1, r1, s2, ℓ2, r2, h1, h2.1, h3, h4, h5, rfl, rfl⟩

end valid_lift

/-! ## Destuttering auxiliary traces -/

/-- The visible label of a live-model step (Rocq `Ul`): the role of a model step. -/
@[rocq_alias trillium.fairis.Ul]
def liveUl {Role Locale : Type _} (ℓ : FairLabel Role Locale) : Option (Option Role) :=
  match ℓ with
  | .takeStep ρ _ => some (some ρ)
  | _ => none

section fuel_dec_unless

variable {Locale : Type _} [Ord Locale] [Std.TransOrd Locale] [Std.LawfulEqOrd Locale]
variable {M : FairModel} {LM : LiveModel Locale M}

/-- The measure decreasing along silent steps (Rocq `Ψ`): the number of roles with fuel plus
the total fuel. -/
@[rocq_alias trillium.fairis.Ψ]
def fuelMeasure (δ : LiveState Locale M) : Nat :=
  (lsFuel (δ : LiveStateData Locale M)).size +
    Iris.Algebra.bigOpM (M' := (Std.ExtTreeMap M.fmrole · compare)) Nat.add (fun _ f => f)
      (lsFuel (δ : LiveStateData Locale M))

omit [Std.LawfulEqOrd Locale] in
/-- Maps with the same keys have the same size. -/
private theorem size_eq_of_mem_iff {K V : Type _} [Ord K] [Std.TransOrd K] {A B : GMap K V}
    (h : ∀ k, k ∈ B ↔ k ∈ A) : B.size = A.size := by
  have h1 : (B ∩ A).size = B.size := Std.ExtTreeMap.size_inter_eq_size_left fun k hk => (h k).1 hk
  have h2 : (A ∩ B).size = A.size := Std.ExtTreeMap.size_inter_eq_size_left fun k hk => (h k).2 hk
  have h3 := Std.ExtTreeMap.size_inter_le_size_right (t₁ := B) (t₂ := A)
  have h4 := Std.ExtTreeMap.size_inter_le_size_right (t₁ := A) (t₂ := B)
  omega

omit [Std.LawfulEqOrd Locale] in
/-- A map whose keys are strictly included in the keys of another map is smaller. -/
private theorem size_lt_of_subset {K V : Type _} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]
    {A B : GMap K V} {ρ : K} (h : ∀ k, k ∈ B → k ∈ A) (hA : ρ ∈ A) (hB : ρ ∉ B) :
    B.size < A.size := by
  have h1 : (B ∩ A.erase ρ).size = B.size := by
    refine Std.ExtTreeMap.size_inter_eq_size_left fun k hk => ?_
    rw [Std.ExtTreeMap.mem_erase, Ne, Std.LawfulEqCmp.compare_eq_iff_eq]
    exact ⟨fun e => hB (e ▸ hk), h k hk⟩
  have h2 := Std.ExtTreeMap.size_inter_le_size_right (t₁ := B) (t₂ := A.erase ρ)
  have h3 : (A.erase ρ).size = A.size - 1 := by
    rw [Std.ExtTreeMap.size_erase]
    simp [Std.ExtTreeMap.contains_iff_mem.2 hA]
  have h4 : A.size ≠ 0 := by
    intro h0
    have : A.isEmpty = true := by rw [Std.ExtTreeMap.isEmpty_eq_size_beq_zero, h0]; rfl
    rw [Std.ExtTreeMap.isEmpty_iff] at this
    subst this
    exact Std.ExtTreeMap.not_mem_empty hA
  omega

open Iris.Algebra in
/-- The big sum of a map with one binding removed. -/
private theorem bigSum_delete {K : Type _} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]
    (A : GMap K Nat) {ρ : K} {f : Nat} (h : A[ρ]? = some f) :
    bigOpM (M' := (Std.ExtTreeMap K · compare)) Nat.add (fun _ f => f) A =
      f + bigOpM (M' := (Std.ExtTreeMap K · compare)) Nat.add (fun _ f => f)
        (Iris.Std.delete (M := (Std.ExtTreeMap K · compare)) A ρ) :=
  BigOpM.bigOpM_delete_eq (op := Nat.add) (fun _ f => f) (M' := (Std.ExtTreeMap K · compare)) h

@[rocq_alias trillium.fairis.fuel_dec_unless]
theorem fuel_dec_unless (auxtr : Auxtrace LM) :
    AuxtraceValid LM auxtr →
      decUnless (fun x : LiveState Locale M => x.lsUnder) liveUl fuelMeasure auxtr := by
  intro Hval n δ ℓ auxtr' Hafter
  have Htrans := auxtrace_valid_forall auxtr Hval n δ ℓ auxtr' Hafter
  cases ℓ with
  | takeStep ρ tid => exact .inl ⟨some ρ, rfl⟩
  | configStep => exact Htrans.2.2.2.2.elim
  | silentStep tid =>
  right
  obtain ⟨Hne, Hdec, Hni, Hincl, Heq⟩ := Htrans
  refine ⟨?_, Heq⟩
  set A := lsFuel (δ : LiveStateData Locale M) with hA
  set B := lsFuel (auxtr'.first : LiveStateData Locale M) with hB
  -- every role with fuel in `B` has at most as much fuel as in `A`
  have Hle : ∀ ρ', ρ' ∈ B → oleq B[ρ']? A[ρ']? := by
    intro ρ' hρ'
    have hA' : ρ' ∈ dom A := Hincl ρ' (mem_dom.2 hρ')
    rcases Hni ρ' hA' (by simp) with h | ⟨h, -⟩
    · exact h
    · exact absurd (mem_dom.2 hρ') h
  have HsumLe : ∀ C D : GMap M.fmrole Nat, (∀ ρ', ρ' ∈ D → oleq D[ρ']? C[ρ']?) →
      Iris.Algebra.bigOpM (M' := (Std.ExtTreeMap M.fmrole · compare)) Nat.add (fun _ f => f) D ≤
        Iris.Algebra.bigOpM (M' := (Std.ExtTreeMap M.fmrole · compare)) Nat.add (fun _ f => f) C := by
    intro C D h
    refine big_addM_leq_forall (M := (Std.ExtTreeMap M.fmrole · compare)) D C fun k hk => ?_
    exact h k (Std.ExtTreeMap.mem_iff_isSome_getElem?.2 hk)
  unfold fuelMeasure
  rw [← hA, ← hB]
  by_cases Hdomeq : ∀ ρ', ρ' ∈ B ↔ ρ' ∈ A
  · obtain ⟨ρ, Hρtid⟩ := Hne
    have Hin : ρ ∈ dom A := by
      rw [hA, ← ls_same_doms, mem_dom_iff]; exact ⟨_, Hρtid⟩
    obtain ⟨f, Hf⟩ := mem_dom_iff.1 Hin
    obtain ⟨f', Hf'⟩ := mem_iff_exists.1 ((Hdomeq ρ).2 (mem_dom.1 Hin))
    have Hlt : f' < f := by
      have := Hdec ρ Hin (mem_dom.2 (mem_of_getElem? Hf'))
        (.sameTid tid (by simp) Hρtid.symm)
      rw [← hA, ← hB, Hf, Hf'] at this
      exact this
    rw [size_eq_of_mem_iff Hdomeq, bigSum_delete A Hf, bigSum_delete B Hf']
    have : Iris.Algebra.bigOpM (M' := (Std.ExtTreeMap M.fmrole · compare)) Nat.add (fun _ f => f)
          (Iris.Std.delete (M := (Std.ExtTreeMap M.fmrole · compare)) B ρ) ≤
        Iris.Algebra.bigOpM (M' := (Std.ExtTreeMap M.fmrole · compare)) Nat.add (fun _ f => f)
          (Iris.Std.delete (M := (Std.ExtTreeMap M.fmrole · compare)) A ρ) := by
      refine HsumLe _ _ fun ρ' hρ' => ?_
      have hne : ρ ≠ ρ' := by
        rintro rfl
        rw [Std.ExtTreeMap.mem_iff_isSome_getElem?] at hρ'
        have : Iris.Std.get? (M := (Std.ExtTreeMap M.fmrole · compare)) (Iris.Std.delete (M := (Std.ExtTreeMap M.fmrole · compare)) B ρ) ρ = none := Iris.Std.get?_delete_eq (M := (Std.ExtTreeMap M.fmrole · compare)) rfl
        change (Iris.Std.get? (M := (Std.ExtTreeMap M.fmrole · compare)) (Iris.Std.delete (M := (Std.ExtTreeMap M.fmrole · compare)) B ρ) ρ).isSome at hρ'
        rw [this] at hρ'; cases hρ'
      have e1 : (Iris.Std.delete (M := (Std.ExtTreeMap M.fmrole · compare)) B ρ)[ρ']? = B[ρ']? := Iris.Std.get?_delete_ne (M := (Std.ExtTreeMap M.fmrole · compare)) hne
      have e2 : (Iris.Std.delete (M := (Std.ExtTreeMap M.fmrole · compare)) A ρ)[ρ']? = A[ρ']? := Iris.Std.get?_delete_ne (M := (Std.ExtTreeMap M.fmrole · compare)) hne
      rw [Std.ExtTreeMap.mem_iff_isSome_getElem?, e1, ← Std.ExtTreeMap.mem_iff_isSome_getElem?]
        at hρ'
      rw [e1, e2]
      exact Hle ρ' hρ'
    omega
  · obtain ⟨ρ, Hρ⟩ := Classical.not_forall.1 Hdomeq
    have HBA : ∀ k, k ∈ B → k ∈ A := fun k hk => mem_dom.1 (Hincl k (mem_dom.2 hk))
    have hρA : ρ ∈ A := by
      by_contra h
      exact Hρ ⟨fun hb => absurd (HBA ρ hb) h, fun ha => absurd ha h⟩
    have hρB : ρ ∉ B := fun hb => Hρ ⟨fun _ => hρA, fun _ => hb⟩
    have := size_lt_of_subset HBA hρA hρB
    have := HsumLe A B Hle
    omega

end fuel_dec_unless

section destuttering_auxtr

variable {Locale : Type _} [Ord Locale] [Std.TransOrd Locale] [Std.LawfulEqOrd Locale]
variable {M : FairModel}

variable (LM : LiveModel Locale M) in
/-- An auxiliary trace is, up to stuttering, a model trace (Rocq `upto_stutter_auxtr`). -/
@[rocq_alias trillium.fairis.upto_stutter_auxtr]
abbrev UptoStutterAuxtr : Auxtrace LM → Mtrace M → Prop :=
  UptoStutter (fun x : LiveState Locale M => x.lsUnder) (liveUl (Role := M.fmrole) (Locale := Locale))

variable {LM : LiveModel Locale M}

@[rocq_alias trillium.fairis.can_destutter_auxtr]
theorem can_destutter_auxtr (auxtr : Auxtrace LM) :
    AuxtraceValid LM auxtr → ∃ mtr, UptoStutterAuxtr LM auxtr mtr :=
  fun Hval => can_destutter _ _ fuelMeasure auxtr (fuel_dec_unless auxtr Hval)

/-- Monotonicity of the generating functor of `UptoStutterAuxtr` (Rocq `upto_stutter_mono'`
and its duplicate `upto_stutter_mono''`; an instance of `upto_stutter_mono`). -/
@[rocq_alias trillium.fairis.upto_stutter_mono', rocq_alias trillium.fairis.upto_stutter_mono'']
theorem upto_stutter_auxtr_mono {R R' : Auxtrace LM → Mtrace M → Prop}
    (LE : ∀ b s, R b s → R' b s) {btr : Auxtrace LM} {str : Mtrace M}
    (IN : UptoStutterInd (fun x : LiveState Locale M => x.lsUnder)
      (liveUl (Role := M.fmrole) (Locale := Locale)) R btr str) :
    UptoStutterInd (fun x : LiveState Locale M => x.lsUnder)
      (liveUl (Role := M.fmrole) (Locale := Locale)) R' btr str :=
  upto_stutter_mono LE IN

@[rocq_alias trillium.fairis.upto_preserves_validity]
theorem upto_preserves_validity (auxtr : Auxtrace LM) (mtr : Mtrace M) :
    UptoStutterAuxtr LM auxtr mtr → AuxtraceValid LM auxtr → MtraceValid mtr := by
  intro Hupto Hval
  refine TraceValid.coinduct _ (fun mtr => ∃ auxtr : Auxtrace LM, UptoStutterAuxtr LM auxtr mtr ∧
    AuxtraceValid LM auxtr) ?_ mtr ⟨auxtr, Hupto, Hval⟩
  rintro mtr ⟨auxtr, Hupto, Hval⟩
  have Hind := Hupto.unfold
  clear Hupto
  induction Hind with
  | singleton s => exact .inl ⟨_, rfl⟩
  | stutter btr str s ℓ _ _ _ _ IH => exact IH (trace_valid_tail _ _ _ Hval)
  | step btr str s ℓ s' ℓ' Hs HUl Hrest =>
    obtain ⟨Hval', Htrans⟩ := trace_valid_cons_inv _ _ _ Hval
    cases ℓ with
    | takeStep ρ tid =>
      obtain rfl : some ρ = ℓ' := Option.some.inj HUl
      subst Hs
      refine .inr ⟨_, _, str, ?_, ⟨btr, Hrest, Hval'⟩, rfl⟩
      rw [upto_stutter_trfirst _ _ Hrest]
      exact Htrans.1
    | silentStep _ => cases HUl
    | configStep => cases HUl

end destuttering_auxtr

section upto_stutter_preserves_fairness_and_termination

variable {Locale : Type _} [Ord Locale] [Std.TransOrd Locale] [Std.LawfulEqOrd Locale]
variable {M : FairModel} {LM : LiveModel Locale M}

@[rocq_alias trillium.fairis.upto_stutter_fairness_0]
theorem upto_stutter_fairness_0 (ρ : M.fmrole) (auxtr : Auxtrace LM) (mtr : Mtrace M) :
    UptoStutterAuxtr LM auxtr mtr →
    (∃ n, predAt auxtr n (fun δ _ => ¬ roleEnabled ρ δ) ∨
      predAt auxtr n (fun _ ℓ => ∃ ζ, ℓ = some (.takeStep ρ ζ))) →
    ∃ m, predAt mtr m (fun δ _ => ¬ roleEnabledModel ρ δ) ∨
      predAt mtr m (fun _ ℓ => ℓ = some (some ρ)) := by
  rintro Hupto ⟨n, Hstep⟩
  induction n generalizing auxtr mtr with
  | zero =>
    cases auxtr using Trace.casesOn' with
    | singl s =>
      rw [Hupto.unfold.singl_inv]
      rcases Hstep with Hpa | Hpa
      · exact ⟨0, .inl (by simpa [roleEnabled, roleEnabledModel] using Hpa)⟩
      · simp at Hpa
    | cons s ℓ btr =>
      rw [pred_at_0, pred_at_0] at Hstep
      rcases Hupto.unfold.cons_inv with ⟨HUl, -, Hfirst, -⟩ | ⟨ℓ', str', rfl, HUl, -⟩
      · rcases Hstep with Hstep | ⟨ζ, Hstep⟩
        · refine ⟨0, .inl ?_⟩
          rw [pred_at_state_trfirst (P := fun δ => ¬ roleEnabledModel ρ δ), ← Hfirst]
          exact Hstep
        · cases Option.some.inj Hstep; cases HUl
      · rcases Hstep with Hstep | ⟨ζ, Hstep⟩
        · exact ⟨0, .inl (by rw [pred_at_0]; exact Hstep)⟩
        · cases Option.some.inj Hstep
          exact ⟨0, .inr (by rw [pred_at_0]; rw [Option.some.inj HUl.symm])⟩
  | succ n IHn =>
    cases auxtr using Trace.casesOn' with
    | singl s => simp [predAt] at Hstep
    | cons s ℓ btr =>
      rw [pred_at_S, pred_at_S] at Hstep
      rcases Hupto.unfold.cons_inv with ⟨-, -, -, Hind⟩ | ⟨ℓ', str', rfl, HUl, Hrest⟩
      · exact IHn btr mtr (UptoStutter.fold Hind) Hstep
      · by_cases Hℓ' : ℓ' = some ρ
        · subst Hℓ'
          exact ⟨0, .inr (by rw [pred_at_0])⟩
        · obtain ⟨m, Hm⟩ := IHn btr str' Hrest Hstep
          exact ⟨m + 1, by simpa only [pred_at_S] using Hm⟩

@[rocq_alias trillium.fairis.upto_stutter_fairness]
theorem upto_stutter_fairness (auxtr : Auxtrace LM) (mtr : Mtrace M) :
    UptoStutterAuxtr LM auxtr mtr → (∀ ρ, fairAux ρ auxtr) → ∀ ρ, fairModelTrace ρ mtr := by
  intro Hupto Hfa ρ n Hpmod
  cases Heq : after n mtr with
  | none => rw [predAt, Heq] at Hpmod; exact Hpmod.elim
  | some mtr' =>
  rw [predAt_some Heq] at Hpmod
  obtain ⟨n', auxtr', Heq', Hupto'⟩ := upto_stutter_after n Hupto Heq
  have Henaux : roleEnabled ρ auxtr'.first := by
    unfold roleEnabled
    rw [← upto_stutter_trfirst _ _ Hupto']
    exact Hpmod
  have Hfa' := fair_aux_after ρ auxtr n' auxtr' (Hfa ρ) Heq' 0
    (by rw [pred_at_state_trfirst (P := fun δ => roleEnabled ρ δ)]; exact Henaux)
  obtain ⟨m, Hres⟩ := upto_stutter_fairness_0 (LM := LM) ρ auxtr' mtr' Hupto' (by simpa using Hfa')
  refine ⟨m, ?_⟩
  rw [pred_at_sum, Heq]
  rw [pred_at_or] at Hres
  refine pred_at_impl _ _ ?_ _ _ Hres
  rintro s ol (h | rfl)
  · exact .inl h
  · exact .inr ⟨some ρ, rfl, rfl⟩

@[rocq_alias trillium.fairis.upto_stutter_finiteness]
theorem upto_stutter_finiteness (auxtr : Auxtrace LM) (mtr : Mtrace M) :
    UptoStutterAuxtr LM auxtr mtr → terminatingTrace mtr → terminatingTrace auxtr := by
  rintro Hupto ⟨n, Hfin⟩
  exact upto_stutter_after_None n Hupto Hfin

end upto_stutter_preserves_fairness_and_termination

end Trillium.Fairis
