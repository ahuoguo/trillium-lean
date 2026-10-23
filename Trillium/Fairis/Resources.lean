/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.Fairis.Fuel
import Trillium.Fairis.MapIncludedUtils
import Iris.Algebra.Auth
import Iris.Algebra.Excl
import Iris.Algebra.LeibnizSet
import Iris.Instances.IProp
import Iris.ProofMode

/-!
# Ghost state for Fairis
Port of `fairis/resources.v` (ghost state, ownership predicates and the model-state
interpretation). The update lemmas for model, fuel and fork steps are in
`Trillium/Fairis/ResourcesUpdates.lean`.

The ghost state consists of three pieces:
* the current model state, `Auth (Option (Excl (ModelO M)))` (Rocq
  `authUR (optionUR (exclR ModelO))`);
* the fuel mapping of every locale, `Auth (LocMapF Locale (Excl (DiscreteO (GMap Role ℕ))))`
  (Rocq `authUR (gmapUR locale (exclR (gmapUR role nat)))`), using iris-lean's heap CMRA on
  `Std.ExtTreeMap` (`LocMapF Locale V = GMap Locale V`); the inner fuel maps form a discrete
  Leibniz OFE `DiscreteO` (Rocq uses the discrete `gmapUR role natO`);
* the free roles, `Auth (DisjointLeibnizSet (GSet Role))` (Rocq `authUR (gset_disjUR role)`).

Representation decisions:
* `fairnessGpreS LM Σ` and `fairnessGS LM Σ` are the classes `FairnessGpreS LM GF` and
  `FairnessGS LM GF`. As for iris-lean's `IrisG`, the locale type, the fair model and the live
  model are `outParam`s, so that the ownership predicates only need `GF` to find the instance.
  Locales live in `Type` (iris-lean's `constOF` requires it).
* `fairnessΣ`/`subG_fairnessGpreS` are subsumed by iris-lean's `ElemG` typeclass synthesis on
  `BundledGFunctors`.
* `own γ (● (Excl <$> m))` is `iOwn γ (● fuelMapExcl m)`, where `fuelMapExcl m` wraps the values
  of `m` in `Excl ∘ DiscreteO.mk`.
* stdpp map notation: `S <$> fs` is `fs.map fun _ f => f + 1`, `alter f k m` is `m.modify k f`,
  `m !!! k` is `m[k]?.getD ∅`, `filter P m` is `m.filter fun k v => decide (P (k, v))`; map and
  set reasoning is done pointwise with the core `Std.ExtTreeMap` lemmas.
-/

set_option linter.unusedSectionVars false

namespace Trillium.Fairis

open Iris Iris.Std ORA OFE BI
open Trillium Trillium.Fairness Trillium.GMap

/-! ## Map lemmas shared with `fairness/utils_maps.v` -/

attribute [rocq_alias trillium.fairis.dom_domain_restrict] Trillium.Fairness.dom_domain_restrict
attribute [rocq_alias trillium.fairis.dom_domain_restrict_union_l]
  Trillium.Fairness.dom_domain_restrict_union_l
attribute [rocq_alias trillium.fairis.dom_domain_restrict_union_r]
  Trillium.Fairness.dom_domain_restrict_union_r
attribute [rocq_alias trillium.fairis.maps_inverse_match] Trillium.Fairness.mapsInverseMatch
attribute [rocq_alias trillium.fairis.no_locale_empty] Trillium.Fairness.no_locale_empty
attribute [rocq_alias trillium.fairis.maps_inverse_bij] Trillium.Fairness.maps_inverse_bij
attribute [rocq_alias trillium.fairis.dom_empty_iff, rocq_alias trillium.fairis.dom_empty_iff_L]
  Trillium.Fairness.dom_empty_iff
attribute [rocq_alias trillium.fairis.map_imap_dom_inclusion]
  Trillium.Fairness.map_imap_dom_inclusion
attribute [rocq_alias trillium.fairis.map_imap_dom_eq] Trillium.Fairness.map_imap_dom_eq
attribute [rocq_alias trillium.fairis.gset_to_gmap_singletons] _root_.Heap.bigOpS_ofSet

section bigop_utils

private theorem bigOpL_map_fst {A : Type _} [OFE A] {o : A → A → A} {u : A} [Algebra.MonoidOps o u]
    {K V : Type _} (P : K → A) (l : List (K × V)) :
    Algebra.bigOpL o (fun _ x => P x) (l.map Prod.fst) =
      Algebra.bigOpL o (fun _ kv => P kv.1) l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons]
    exact congrArg (o (P a.1)) ih

/-- Rocq `big_opMS`: a big operator over a set is a big operator over the underlying map (with
unit values). -/
@[rocq_alias trillium.fairis.big_opMS]
theorem big_opMS {A : Type _} [OFE A] {o : A → A → A} {u : A} [Algebra.MonoidOps o u]
    {K : Type _} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K] (g : GSet K) (P : K → A) :
    Algebra.bigOpS o P g =
      Algebra.bigOpM (M' := (Std.ExtTreeMap K · compare)) o (fun k (_ : Unit) => P k) g.inner := by
  unfold Algebra.bigOpS Algebra.bigOpM
  rw [← bigOpL_map_fst]
  congr 1
  exact (Std.ExtTreeMap.map_fst_toList_eq_keys).symm

end bigop_utils

/-! ## Ghost state -/

/-- The heap functor of maps with keys in `Locale` (`LocMapF Locale V = GMap Locale V`); iris-lean's
generic heap CMRA is found through it. -/
abbrev LocMapF (Locale : Type) [Ord Locale] : Type → Type := fun V => Std.ExtTreeMap Locale V compare

/-- The (discrete, Leibniz) OFE of model states (Rocq `ModelO`). -/
@[rocq_alias trillium.fairis.ModelO]
abbrev ModelO (M : FairModel) : Type := DiscreteO M.fmstate

#rocq_ignore trillium.fairis.RoleO
  "Roles are only used as keys of maps and elements of sets, which need no OFE in iris-lean; the fuel maps are wrapped in `DiscreteO` as a whole"
#rocq_ignore trillium.fairis.localeO
  "Locales are only used as keys of the heap CMRA, which need no OFE in iris-lean"

/-- The camera of the model state (Rocq `authUR (optionUR (exclR (ModelO M)))`). -/
abbrev ModelR (M : FairModel) : Type := Auth (Option (Excl (ModelO M)))

/-- The camera of the fuel mapping (Rocq `authUR (gmapUR locale (exclR (gmapUR role natO)))`). -/
abbrev FuelMapR (Locale : Type) [Ord Locale] [Std.TransOrd Locale] [Std.LawfulEqOrd Locale]
    (M : FairModel) : Type :=
  Auth (LocMapF Locale (Excl (DiscreteO (GMap M.fmrole Nat))))

/-- The camera of the free roles (Rocq `authUR (gset_disjUR role)`). -/
abbrev FreeRolesR (M : FairModel) : Type := Auth (DisjointLeibnizSet (GSet M.fmrole))

/-- The ghost state needed for Fairis, before allocation (Rocq `fairnessGpreS`). -/
@[rocq_alias trillium.fairis.fairnessGpreS]
class FairnessGpreS {Locale : outParam Type} [Ord Locale] [Std.TransOrd Locale]
    [Std.LawfulEqOrd Locale] {M : outParam FairModel} (LM : outParam (LiveModel Locale M))
    (GF : BundledGFunctors) where
  model : ElemG GF (constOF (ModelR M))
  fuelMapping : ElemG GF (constOF (FuelMapR Locale M))
  freeRoles : ElemG GF (constOF (FreeRolesR M))

attribute [reducible, instance] FairnessGpreS.model FairnessGpreS.fuelMapping
  FairnessGpreS.freeRoles

/-- The ghost state of Fairis with the names of its three components (Rocq `fairnessGS`). -/
@[rocq_alias trillium.fairis.fairnessGS]
class FairnessGS {Locale : outParam Type} [Ord Locale] [Std.TransOrd Locale]
    [Std.LawfulEqOrd Locale] {M : outParam FairModel} (LM : outParam (LiveModel Locale M))
    (GF : BundledGFunctors) where
  [inG : FairnessGpreS LM GF]
  /-- The underlying model. -/
  modelName : GName
  /-- The mapping of threads to roles with fuel. -/
  fuelMappingName : GName
  /-- The set of free/available roles. -/
  freeRolesName : GName

attribute [reducible, instance] FairnessGS.inG

#rocq_ignore trillium.fairis.«fairnessΣ» "Subsumed by BundledGFunctors typeclass synthesis"
#rocq_ignore trillium.fairis.subG_fairnessGpreS
  "Superseded by Lean's direct `ElemG` typeclass synthesis (fields of `FairnessGpreS`)"

section ghost

variable {Locale : Type} [Ord Locale] [Std.TransOrd Locale] [Std.LawfulEqOrd Locale]
variable {M : FairModel}

/-- Rocq `Excl <$> m`. -/
def fuelMapExcl (m : GMap Locale (GMap M.fmrole Nat)) :
    LocMapF Locale (Excl (DiscreteO (GMap M.fmrole Nat))) :=
  m.map fun _ fs => Excl.excl ⟨fs⟩

theorem get?_fuelMapExcl (m : GMap Locale (GMap M.fmrole Nat)) (ζ : Locale) :
    PartialMap.get? (fuelMapExcl m) ζ = m[ζ]?.map fun fs => Excl.excl ⟨fs⟩ :=
  Std.ExtTreeMap.getElem?_map

theorem fuelMapExcl_singleton (ζ : Locale) (fs : GMap M.fmrole Nat) :
    fuelMapExcl (GMap.singleton ζ fs) = PartialMap.singleton ζ (Excl.excl ⟨fs⟩) := by
  apply LawfulPartialMap.equiv_iff_eq.1
  intro k
  rw [get?_fuelMapExcl, getElem?_singleton]
  by_cases h : ζ = k
  · subst h; simp [LawfulPartialMap.get?_singleton_eq]
  · simp [h, LawfulPartialMap.get?_singleton_ne h]

theorem fuelMapExcl_insert (m : GMap Locale (GMap M.fmrole Nat)) (ζ : Locale)
    (fs : GMap M.fmrole Nat) :
    fuelMapExcl (m.insert ζ fs) = PartialMap.insert (fuelMapExcl m) ζ (Excl.excl ⟨fs⟩) := by
  apply LawfulPartialMap.equiv_iff_eq.1
  intro k
  rw [get?_fuelMapExcl, getElem?_insert_ite]
  by_cases h : ζ = k
  · subst h; simp [LawfulPartialMap.get?_insert_eq]
  · simp [h, LawfulPartialMap.get?_insert_ne h, get?_fuelMapExcl]

theorem fuelMapExcl_valid (m : GMap Locale (GMap M.fmrole Nat)) : ✓ fuelMapExcl m := by
  intro k
  rw [get?_fuelMapExcl]
  cases m[k]? <;> trivial

variable {GF : BundledGFunctors} {LM : LiveModel Locale M}

section own

variable [fG : FairnessGS LM GF]

/-- Rocq `auth_fuel_mapping_is`. -/
@[rocq_alias trillium.fairis.auth_fuel_mapping_is]
def authFuelMappingIs (m : GMap Locale (GMap M.fmrole Nat)) : IProp GF :=
  iOwn (F := constOF (FuelMapR Locale M)) fG.fuelMappingName (● fuelMapExcl m)

/-- Rocq `frag_fuel_mapping_is`. -/
@[rocq_alias trillium.fairis.frag_fuel_mapping_is]
def fragFuelMappingIs (m : GMap Locale (GMap M.fmrole Nat)) : IProp GF :=
  iOwn (F := constOF (FuelMapR Locale M)) fG.fuelMappingName (◯ fuelMapExcl m)

/-- Rocq `auth_model_is`. -/
@[rocq_alias trillium.fairis.auth_model_is]
def authModelIs (fm : M.fmstate) : IProp GF :=
  iOwn (F := constOF (ModelR M)) fG.modelName (● some (Excl.excl ⟨fm⟩))

/-- Rocq `frag_model_is`. -/
@[rocq_alias trillium.fairis.frag_model_is]
def fragModelIs (fm : M.fmstate) : IProp GF :=
  iOwn (F := constOF (ModelR M)) fG.modelName (◯ some (Excl.excl ⟨fm⟩))

/-- Rocq `auth_free_roles_are`. -/
@[rocq_alias trillium.fairis.auth_free_roles_are]
def authFreeRolesAre (FR : GSet M.fmrole) : IProp GF :=
  iOwn (F := constOF (FreeRolesR M)) fG.freeRolesName (● DisjointLeibnizSet.valid FR)

/-- Rocq `frag_free_roles_are`. -/
@[rocq_alias trillium.fairis.frag_free_roles_are]
def fragFreeRolesAre (FR : GSet M.fmrole) : IProp GF :=
  iOwn (F := constOF (FreeRolesR M)) fG.freeRolesName (◯ DisjointLeibnizSet.valid FR)

theorem model_valid_2 (a b : ModelR M) :
    iOwn (GF := GF) (F := constOF (ModelR M)) fG.modelName a ∗
      iOwn (F := constOF (ModelR M)) fG.modelName b ⊢ ⌜✓ (a • b)⌝ :=
  iOwn_cmraValid_op.trans (internalCmraValid_discrete (A := ModelR M)).mp

theorem fuelMapping_valid_2 (a b : FuelMapR Locale M) :
    iOwn (GF := GF) (F := constOF (FuelMapR Locale M)) fG.fuelMappingName a ∗
      iOwn (F := constOF (FuelMapR Locale M)) fG.fuelMappingName b ⊢ ⌜✓ (a • b)⌝ :=
  iOwn_cmraValid_op.trans (internalCmraValid_discrete (A := FuelMapR Locale M)).mp

theorem freeRoles_valid_2 (a b : FreeRolesR M) :
    iOwn (GF := GF) (F := constOF (FreeRolesR M)) fG.freeRolesName a ∗
      iOwn (F := constOF (FreeRolesR M)) fG.freeRolesName b ⊢ ⌜✓ (a • b)⌝ :=
  iOwn_cmraValid_op.trans (internalCmraValid_discrete (A := FreeRolesR M)).mp

theorem auth_frag_fuelMapping_agree (m : GMap Locale (GMap M.fmrole Nat)) (ζ : Locale)
    (fs : GMap M.fmrole Nat) :
    authFuelMappingIs (GF := GF) m ∗ fragFuelMappingIs (GMap.singleton ζ fs) ⊢ ⌜m[ζ]? = some fs⌝ := by
  refine (fuelMapping_valid_2 _ _).trans (pure_mono fun H => ?_)
  obtain ⟨Hincl, Hv⟩ := Auth.auth_both_valid_discrete.mp H
  rw [fuelMapExcl_singleton, Heap.exclusive_singleton_inc_iff inferInstance Hv,
    get?_fuelMapExcl] at Hincl
  cases h : m[ζ]? with
  | none => rw [h] at Hincl; cases Hincl
  | some v =>
    rw [h] at Hincl
    simp only [Option.map_some, Option.some.injEq, Excl.excl.injEq] at Hincl
    rw [DiscreteO.eqv_inj Hincl]

theorem auth_frag_model_agree (s1 s2 : M.fmstate) :
    authModelIs (GF := GF) s1 ∗ fragModelIs s2 ⊢ ⌜s1 = s2⌝ := by
  refine (model_valid_2 _ _).trans (pure_mono fun H => ?_)
  obtain ⟨h1, -⟩ := Auth.auth_both_valid_discrete.mp H
  exact DiscreteO.eqv_inj (Excl.excl_included.mp h1).symm

instance auth_frag_model_combine_gives (s1 s2 : M.fmstate) :
    ProofMode.CombineSepGives (PROP := IProp GF) (authModelIs s1) (fragModelIs s2) iprop(⌜s1 = s2⌝) where
  combine_sep_gives := by
    iintro H
    icases auth_frag_model_agree $$ H with %H
    itrivial

end own

/-! ## Fuel maps and the model-state interpretation -/

section model_state_interp

/-- Rocq `fuel_map_le_inner`: every fuel map of `m1` is included in the one of `m2`, with
smaller fuel. -/
@[rocq_alias trillium.fairis.fuel_map_le_inner]
def fuelMapLeInner (m1 m2 : GMap Locale (GMap M.fmrole Nat)) : Prop :=
  mapIncluded (fun _ (fs1 fs2 : GMap M.fmrole Nat) =>
    mapIncluded (fun _ (f1 f2 : Nat) => f1 ≤ f2) fs1 fs2) m1 m2

/-- Rocq `fuel_map_le`. -/
@[rocq_alias trillium.fairis.fuel_map_le]
def fuelMapLe (m1 m2 : GMap Locale (GMap M.fmrole Nat)) : Prop :=
  fuelMapLeInner m1 m2 ∧
  -- OBS: This is a bit hacky, should instead change definition.
  dom m1 = dom m2

/-- Rocq `fuel_map_preserve_dead`: every role of `ρs` has fuel in some fuel map of `m`. -/
@[rocq_alias trillium.fairis.fuel_map_preserve_dead]
def fuelMapPreserveDead (m : GMap Locale (GMap M.fmrole Nat)) (ρs : GSet M.fmrole) : Prop :=
  ∀ ρ, ρ ∈ ρs → ∃ (ζ : Locale) (fs : GMap M.fmrole Nat), m[ζ]? = some fs ∧ ρ ∈ dom fs

variable {Expr State : Type _} [LanguageCore Expr State Locale]

/-- Rocq `fuel_map_preserve_threadpool`: locales which are not threads of `tp` have no fuel
map. -/
@[rocq_alias trillium.fairis.fuel_map_preserve_threadpool]
def fuelMapPreserveThreadpool (tp : List Expr) (fuelMap : GMap Locale (GMap M.fmrole Nat)) :
    Prop :=
  ∀ ζ, ζ ∉ localesOfList tp → fuelMap[ζ]? = none

variable [fG : FairnessGS LM GF]

/-- The model-state interpretation (Rocq `model_state_interp`). -/
@[rocq_alias trillium.fairis.model_state_interp]
def modelStateInterp (tp : List Expr) (δ : LiveState Locale M) : IProp GF :=
  iprop(∃ fuelMap : GMap Locale (GMap M.fmrole Nat),
    ⌜fuelMapLe fuelMap δ.lsMap⌝ ∗
    ⌜fuelMapPreserveDead fuelMap (M.liveRoles δ.lsUnder)⌝ ∗
    ⌜fuelMapPreserveThreadpool tp fuelMap⌝ ∗
    authModelIs δ.lsUnder ∗ authFuelMappingIs fuelMap)

@[rocq_alias trillium.fairis.model_state_interp_tids_smaller]
theorem model_state_interp_tids_smaller [DecidableEq Locale] (δ : LiveState Locale M)
    (tp : List Expr) :
    ⊢ modelStateInterp (GF := GF) tp δ -∗ ⌜tidsSmaller tp δ⌝ := by
  unfold modelStateInterp
  iintro ⟨%m, %Hle, -, %Hbig, -⟩
  ipureintro
  intro ζ Hin
  by_cases hζ : ζ ∈ localesOfList tp
  · obtain ⟨⟨tp', e'⟩, Hp, Heq⟩ := List.mem_map.1 hζ
    subst Heq
    rw [fromLocale, fromLocaleFrom_some Hp]
    rfl
  · exfalso
    rw [← Hle.2, mem_dom_iff] at Hin
    obtain ⟨v, hv⟩ := Hin
    rw [Hbig ζ hζ] at hv
    cases hv

end model_state_interp

#rocq_ignore trillium.fairis.own_proper "OFE is Leibniz; use equality"

section model_state_lemmas

variable [fG : FairnessGS LM GF]

/-- `ζ` owns the roles of `fs` with the given fuel (Rocq `has_fuels`, notation `ζ ↦M fs`). -/
@[rocq_alias trillium.fairis.has_fuels]
def hasFuels (ζ : Locale) (fs : GMap M.fmrole Nat) : IProp GF :=
  fragFuelMappingIs (GMap.singleton ζ fs)

#rocq_ignore trillium.fairis.has_fuels_proper "OFE is Leibniz; use equality"

@[rocq_alias trillium.fairis.has_fuels_timeless]
instance hasFuels_timeless (ζ : Locale) (fs : GMap M.fmrole Nat) :
    Timeless (hasFuels (GF := GF) ζ fs) := by
  unfold hasFuels fragFuelMappingIs
  infer_instance

/-- Rocq `has_fuels_S` (notation `ζ ↦M++ fs`). -/
@[rocq_alias trillium.fairis.has_fuels_S]
def hasFuelsS (ζ : Locale) (fs : GMap M.fmrole Nat) : IProp GF :=
  hasFuels ζ (fs.map fun _ f => f + 1)

/-- Rocq `has_fuels_plus`. -/
@[rocq_alias trillium.fairis.has_fuels_plus]
def hasFuelsPlus (n : Nat) (ζ : Locale) (fs : GMap M.fmrole Nat) : IProp GF :=
  hasFuels ζ (fs.map fun _ m => n + m)

@[rocq_alias trillium.fairis.has_fuel_fuels_plus_1]
theorem has_fuel_fuels_plus_1 (ζ : Locale) (fs : GMap M.fmrole Nat) :
    hasFuelsPlus (GF := GF) 1 ζ fs ⊣⊢ hasFuelsS ζ fs := by
  unfold hasFuelsPlus hasFuelsS
  have : (fun (_ : M.fmrole) (m : Nat) => 1 + m) = fun _ f => f + 1 := by
    funext _ m; omega
  rw [this]
  exact .rfl

@[rocq_alias trillium.fairis.has_fuel_fuels_plus_0]
theorem has_fuel_fuels_plus_0 (ζ : Locale) (fs : GMap M.fmrole Nat) :
    hasFuelsPlus (GF := GF) 0 ζ fs ⊣⊢ hasFuels ζ fs := by
  unfold hasFuelsPlus
  have : (fs.map fun _ m => 0 + m) = fs := by
    apply Std.ExtTreeMap.ext_getElem?
    intro k
    rw [Std.ExtTreeMap.getElem?_map]
    cases fs[k]? <;> simp
  rw [this]
  exact .rfl

@[rocq_alias trillium.fairis.has_fuels_plus_split_S]
theorem has_fuels_plus_split_S (n : Nat) (ζ : Locale) (fs : GMap M.fmrole Nat) :
    hasFuelsPlus (GF := GF) (n + 1) ζ fs ⊣⊢ hasFuelsS ζ (fs.map fun _ m => n + m) := by
  unfold hasFuelsPlus hasFuelsS
  have : (fs.map fun _ m => n + 1 + m) = (fs.map fun _ m => n + m).map fun _ f => f + 1 := by
    apply Std.ExtTreeMap.ext_getElem?
    intro k
    simp only [Std.ExtTreeMap.getElem?_map]
    cases fs[k]? <;> simp; omega
  rw [this]
  exact .rfl

end model_state_lemmas

/-- `ζ ↦M fs`: `ζ` owns the roles of `fs` with the given fuel. -/
scoped notation:20 tid " ↦M " R => hasFuels tid R
/-- `ζ ↦M++ fs`: `ζ` owns the roles of `fs` with one more unit of fuel each. -/
scoped notation:20 tid " ↦M++ " R => hasFuelsS tid R

/-! ## Allocation -/

section adequacy

variable [FairnessGpreS LM GF]

@[rocq_alias trillium.fairis.model_state_init]
theorem model_state_init (s0 : M.fmstate) :
    ⊢@{IProp GF} |==> ∃ γ, iOwn (F := constOF (ModelR M)) γ
      ((● some (Excl.excl ⟨s0⟩)) • ◯ some (Excl.excl ⟨s0⟩)) :=
  iOwn_alloc _ (Auth.auth_both_valid_2 trivial (inc_refl _))

variable (LM) in
/-- The initial fuel mapping (Rocq `init_fuel_map`): `ζ0` owns all live roles of `s0`, with
maximal fuel. -/
@[rocq_alias trillium.fairis.init_fuel_map]
def initFuelMap (s0 : M.fmstate) (ζ0 : Locale) :
    LocMapF Locale (Excl (DiscreteO (GMap M.fmrole Nat))) :=
  PartialMap.singleton ζ0 (Excl.excl ⟨GSet.toGMap (LM.lmFl s0) (M.liveRoles s0)⟩)

@[rocq_alias trillium.fairis.model_fuel_mapping_init]
theorem model_fuel_mapping_init (s0 : M.fmstate) (ζ0 : Locale) :
    ⊢@{IProp GF} |==> ∃ γ, iOwn (F := constOF (FuelMapR Locale M)) γ (● initFuelMap LM s0 ζ0) ∗
      iOwn (F := constOF (FuelMapR Locale M)) γ (◯ initFuelMap LM s0 ζ0) := by
  imod iOwn_alloc (GF := GF) (F := constOF (FuelMapR Locale M))
    ((● initFuelMap LM s0 ζ0 : FuelMapR Locale M) • ◯ initFuelMap LM s0 ζ0) with ⟨%γ, H1, H2⟩
  · exact Auth.auth_both_valid_2 (Heap.singleton_valid_iff.2 trivial) (inc_refl _)
  imodintro
  iexists γ
  iframe

@[rocq_alias trillium.fairis.model_free_roles_init]
theorem model_free_roles_init (_s0 : M.fmstate) (FR : GSet M.fmrole) :
    ⊢@{IProp GF} |==> ∃ γ, iOwn (F := constOF (FreeRolesR M)) γ
      ((● DisjointLeibnizSet.valid FR) • ◯ DisjointLeibnizSet.valid FR) :=
  iOwn_alloc _ (Auth.auth_both_valid_2 trivial (inc_refl _))

end adequacy

/-! ## Updating the ghost state -/

section ghost_updates

variable [fG : FairnessGS LM GF]

@[rocq_alias trillium.fairis.update_model]
theorem update_model (δ δ1 δ2 : M.fmstate) :
    ⊢ authModelIs (GF := GF) δ1 -∗ fragModelIs δ2 ==∗ authModelIs δ ∗ fragModelIs δ := by
  unfold authModelIs fragModelIs
  iintro H1 H2
  iapply (iOwn_update_op _).trans (BIUpdate.mono iOwn_op.1) $$ [$H1 $H2]
  exact Auth.auth_update (LocalUpdate.option (LocalUpdate.exclusive trivial))

@[rocq_alias trillium.fairis.model_update]
theorem model_update (s1 s2 s3 : M.fmstate) :
    ⊢ authModelIs (GF := GF) s1 -∗ fragModelIs s2 ==∗ authModelIs s3 ∗ fragModelIs s3 :=
  update_model s3 s1 s2

@[rocq_alias trillium.fairis.model_agree]
theorem model_agree (s1 s2 : M.fmstate) :
    ⊢ authModelIs (GF := GF) s1 -∗ fragModelIs s2 -∗ ⌜s1 = s2⌝ := by
  iintro Ha Hf
  iapply auth_frag_model_agree $$ [$Ha $Hf]

@[rocq_alias trillium.fairis.model_agree']
theorem model_agree' {Expr State : Type _} [LanguageCore Expr State Locale]
    (δ1 : LiveState Locale M) (s2 : M.fmstate) (n : List Expr) :
    ⊢ modelStateInterp (GF := GF) n δ1 -∗ fragModelIs s2 -∗ ⌜δ1.lsUnder = s2⌝ := by
  unfold modelStateInterp
  iintro ⟨%fm, -, -, -, Hs1, -⟩ Hs2
  iapply model_agree $$ Hs1 Hs2

@[rocq_alias trillium.fairis.has_fuels_agree]
theorem has_fuels_agree (ζ : Locale) (fs : GMap M.fmrole Nat)
    (m : GMap Locale (GMap M.fmrole Nat)) :
    ⊢ authFuelMappingIs (GF := GF) m -∗ hasFuels ζ fs -∗ ⌜m[ζ]? = some fs⌝ := by
  unfold hasFuels
  iintro Ha Hf
  iapply auth_frag_fuelMapping_agree $$ [$Ha $Hf]

instance has_fuels_combine_gives (ζ : Locale) (fs : GMap M.fmrole Nat)
    (m : GMap Locale (GMap M.fmrole Nat)) :
    ProofMode.CombineSepGives (PROP := IProp GF) (authFuelMappingIs m) (hasFuels ζ fs)
      iprop(⌜m[ζ]? = some fs⌝) where
  combine_sep_gives := by
    iintro ⟨Ha, Hf⟩
    icases has_fuels_agree $$ Ha Hf with %H
    itrivial

@[rocq_alias trillium.fairis.has_fuels_update]
theorem has_fuels_update (fm : GMap Locale (GMap M.fmrole Nat)) (ζ : Locale)
    (fs fs' : GMap M.fmrole Nat) :
    ⊢ authFuelMappingIs (GF := GF) fm -∗ hasFuels ζ fs ==∗
      authFuelMappingIs (fm.insert ζ fs') ∗ hasFuels ζ fs' := by
  iintro Hfm Hfs
  icombine Hfm Hfs gives %Hagree
  unfold authFuelMappingIs hasFuels fragFuelMappingIs
  iapply (iOwn_update_op _).trans (BIUpdate.mono iOwn_op.1) $$ [$Hfm $Hfs]
  rw [fuelMapExcl_singleton, fuelMapExcl_singleton, fuelMapExcl_insert]
  refine Auth.auth_update (Heap.singleton_local_update (x := Excl.excl ⟨fs⟩) ?_
    (LocalUpdate.exclusive trivial))
  rw [get?_fuelMapExcl, Hagree]
  rfl

@[rocq_alias trillium.fairis.resources.has_fuels_decr]
theorem has_fuels_decr (ζ : Locale) (fs : GMap M.fmrole Nat)
    (m : GMap Locale (GMap M.fmrole Nat)) :
    ⊢ authFuelMappingIs (GF := GF) m -∗ hasFuelsS ζ fs ==∗
      authFuelMappingIs (m.insert ζ fs) ∗ hasFuels ζ fs := by
  unfold hasFuelsS
  iintro Hfm Hfs
  iapply has_fuels_update $$ Hfm Hfs

@[rocq_alias trillium.fairis.has_fuels_delete]
theorem has_fuels_delete (fs : GMap Locale (GMap M.fmrole Nat)) (ζ : Locale)
    (ρs : GMap M.fmrole Nat) (ρ : M.fmrole) :
    ⊢ authFuelMappingIs (GF := GF) fs -∗ hasFuels ζ ρs ==∗
      authFuelMappingIs (fs.insert ζ (ρs.erase ρ)) ∗ hasFuels ζ (ρs.erase ρ) := by
  iintro Hfm Hfs
  iapply has_fuels_update $$ Hfm Hfs

@[rocq_alias trillium.fairis.has_fuels_alloc]
theorem has_fuels_alloc (fm : GMap Locale (GMap M.fmrole Nat)) (ζ : Locale)
    (fs : GMap M.fmrole Nat) :
    ζ ∉ dom fm →
    ⊢ authFuelMappingIs (GF := GF) fm ==∗ authFuelMappingIs (fm.insert ζ fs) ∗ hasFuels ζ fs := by
  intro Hnin
  unfold authFuelMappingIs hasFuels fragFuelMappingIs
  iintro Hfm
  iapply (iOwn_update _).trans (BIUpdate.mono iOwn_op.1) $$ Hfm
  rw [fuelMapExcl_singleton, fuelMapExcl_insert]
  refine Auth.auth_update_alloc (Heap.alloc_singleton_local_update ?_ trivial)
  rw [get?_fuelMapExcl, not_mem_iff.1 (fun h => Hnin (mem_dom.2 h))]
  rfl

@[rocq_alias trillium.fairis.has_fuels_split]
theorem has_fuels_split (fm : GMap Locale (GMap M.fmrole Nat)) (ζ ζf : Locale)
    (fs1 fs2 : GMap M.fmrole Nat) :
    ζf ∉ dom fm → fs1 ##ₘ fs2 →
    ⊢ authFuelMappingIs (GF := GF) fm -∗ hasFuels ζ (fs1 ∪ fs2) ==∗
      authFuelMappingIs ((fm.insert ζ fs1).insert ζf fs2) ∗ hasFuels ζ fs1 ∗ hasFuels ζf fs2 := by
  intro Hnin _Hdisj
  iintro Hfm Hfs
  icombine Hfm Hfs gives %Hagree
  have Hneq : ζ ≠ ζf := fun h => Hnin (mem_dom.2 (h ▸ mem_of_getElem? Hagree))
  have Hnin' : ζf ∉ dom (fm.insert ζ fs1) := by
    rw [mem_dom, Std.ExtTreeMap.mem_insert]
    rintro (h | h)
    · exact Hneq (Std.LawfulEqOrd.eq_of_compare h)
    · exact Hnin (mem_dom.2 h)
  imod has_fuels_update (fs' := fs1) $$ Hfm Hfs with ⟨Hfm, Hfs1⟩
  imod has_fuels_alloc _ ζf fs2 Hnin' $$ Hfm with ⟨Hfm, Hfs2⟩
  imodintro
  iframe

@[rocq_alias trillium.fairis.free_roles_inclusion]
theorem free_roles_inclusion (FR fr : GSet M.fmrole) :
    ⊢ authFreeRolesAre (GF := GF) FR -∗ fragFreeRolesAre fr -∗ ⌜fr ⊆ FR⌝ := by
  unfold authFreeRolesAre fragFreeRolesAre
  iintro HFR Hfr
  ihave %Hval := freeRoles_valid_2 _ _ $$ [$HFR $Hfr]
  ipureintro
  exact DisjointLeibnizSet.included_iff_subset.1 (Auth.auth_both_valid_discrete.1 Hval).1

@[rocq_alias trillium.fairis.update_free_roles]
theorem update_free_roles (rem FR fr1 : GSet M.fmrole) :
    rem ⊆ fr1 →
    ⊢ authFreeRolesAre (GF := GF) FR -∗ fragFreeRolesAre fr1 ==∗
      authFreeRolesAre (FR \ rem) ∗ fragFreeRolesAre (fr1 \ rem) := by
  intro Hrem
  have Hsplit : (◯ DisjointLeibnizSet.valid fr1 : FreeRolesR M) =
      (◯ DisjointLeibnizSet.valid (fr1 \ rem)) • ◯ DisjointLeibnizSet.valid rem := by
    rw [← Auth.frag_op, DisjointLeibnizSet.disj_op_union]
    · congr 2
      ext x
      simp only [mem_union, mem_diff]
      have := Hrem x
      tauto
    · intro x ⟨h1, h2⟩
      exact (mem_diff.1 h1).2 h2
  unfold authFreeRolesAre fragFreeRolesAre
  iintro HFR Hfr1
  rw [Hsplit]
  icases iOwn_op.1 $$ Hfr1 with ⟨Hfr2, Hrem⟩
  imod (iOwn_update_op (F := constOF (FreeRolesR M))
    (a' := (● DisjointLeibnizSet.valid (FR \ rem) : FreeRolesR M) • ◯ DisjointLeibnizSet.valid ∅)
    (Auth.auth_update DisjointLeibnizSet.localUpdate_dealloc)) $$ [$HFR $Hrem] with H
  icases iOwn_op.1 $$ H with ⟨H, -⟩
  imodintro
  iframe

end ghost_updates

end ghost

end Trillium.Fairis
