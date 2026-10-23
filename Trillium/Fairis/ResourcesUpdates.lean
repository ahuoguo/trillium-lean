/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.Fairis.Resources

/-!
# Updates of the Fairis ghost state
Port of `fairis/resources.v`, second part: the updates of the live state and of the ghost state
for fuel steps (`update_fuel_step`), model steps (`update_model_step`) and fork steps
(`update_fork_step`).

Representation decisions (see also `Trillium/Fairis/Resources.lean`):
* Rocq's `Program Definition`s of live states (`model_update_decr`, `model_update_filter`,
  `model_update_set`) are definitions of `LiveState`s whose invariants are proved inline.
* `model_update_state`, `model_update_model_step`, `model_update_split` and `model_update_fork`
  return the `LiveStateData` (as in Rocq, where e.g. `ls_data δ2 = model_update_model_step …`).
* Map reasoning is done pointwise on `m[k]?` (instead of stdpp's `map_agree_R`-based
  decompositions), so the proofs of the update lemmas differ in their details from Rocq's.
* `trace_last ex` is `ex.last`, `ex :tr[ℓ]: c` is `ex.extend ℓ c`, and `locale_step` is
  `Language.LocaleStep`.
-/

set_option linter.unusedSectionVars false

namespace Trillium.Fairis

open Iris Iris.Std ORA OFE BI
open Trillium Trillium.Fairness Trillium.GMap

/-! ## Pointwise map lemmas -/

section helpers

variable {K V : Type _} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]

open Classical in
theorem getElem?_modify_ite {m : GMap K V} {k k' : K} {f : V → V} :
    (m.modify k f)[k']? = if k = k' then m[k]?.map f else m[k']? := by
  rw [Std.ExtTreeMap.getElem?_modify]
  by_cases h : k = k'
  · subst h; simp
  · have h' : compare k k' ≠ .eq := fun h' => h (Std.LawfulEqOrd.eq_of_compare h')
    simp [h, h']

theorem getElem?_map_eq {W : Type _} {m : GMap K V} {f : V → W} {k : K} :
    (m.map fun _ v => f v)[k]? = m[k]?.map f :=
  Std.ExtTreeMap.getElem?_map

theorem getElem?_filter_eq {m : GMap K V} {P : K → V → Bool} {k : K} :
    (m.filter P)[k]? = m[k]?.filter (P k) :=
  Std.ExtTreeMap.getElem?_filter'

theorem mem_iff_getElem? {m : GMap K V} {k : K} : k ∈ m ↔ (m[k]?).isSome :=
  Std.ExtTreeMap.mem_iff_isSome_getElem?

end helpers

/-! ## Updates of live states -/

section live_state_updates

variable {Locale : Type} [Ord Locale] [Std.TransOrd Locale] [Std.LawfulEqOrd Locale]
variable {M : FairModel}

/-- Disjointness of the fuel maps is preserved by shrinking them. -/
theorem disj_of_keys_sub (δ : LiveState Locale M) (m : GMap Locale (GMap M.fmrole Nat))
    (h : ∀ (ζ : Locale) (fs : GMap M.fmrole Nat), m[ζ]? = some fs →
      ∃ fs0, δ.lsMap[ζ]? = some fs0 ∧ ∀ ρ, ρ ∈ fs → ρ ∈ fs0) :
    ∀ (ζ ζ' : Locale) (fs fs' : GMap M.fmrole Nat), ζ ≠ ζ' → m[ζ]? = some fs →
      m[ζ']? = some fs' → fs ##ₘ fs' := by
  intro ζ ζ' fs fs' Hne H1 H2
  obtain ⟨fs0, H1', S1⟩ := h ζ fs H1
  obtain ⟨fs0', H2', S2⟩ := h ζ' fs' H2
  have D := δ.ls_map_disj ζ ζ' fs0 fs0' Hne H1' H2'
  rw [disjoint_iff_mem] at D ⊢
  exact fun ρ h1 h2 => D ρ (S1 ρ h1) (S2 ρ h2)

theorem modify_keys_sub (δ : LiveState Locale M) (ζ : Locale)
    (g : GMap M.fmrole Nat → GMap M.fmrole Nat) (hg : ∀ fs ρ, ρ ∈ g fs → ρ ∈ fs) :
    ∀ (z : Locale) (fs : GMap M.fmrole Nat), (δ.lsMap.modify ζ g)[z]? = some fs →
      ∃ fs0, δ.lsMap[z]? = some fs0 ∧ ∀ ρ, ρ ∈ fs → ρ ∈ fs0 := by
  intro z fs H
  rw [getElem?_modify_ite] at H
  split at H
  · rename_i h
    subst h
    obtain ⟨fs0, H0, rfl⟩ := Option.map_eq_some_iff.1 H
    exact ⟨fs0, H0, hg fs0⟩
  · exact ⟨fs, H, fun _ h => h⟩

theorem live_modify (δ : LiveState Locale M) (ζ : Locale)
    (g : GMap M.fmrole Nat → GMap M.fmrole Nat)
    (hg : ∀ fs ρ, ρ ∈ fs → ρ ∈ M.liveRoles δ.lsUnder → ρ ∈ g fs) :
    ∀ ρ, ρ ∈ M.liveRoles δ.lsUnder → ∃ (z : Locale) (fs : GMap M.fmrole Nat),
      (δ.lsMap.modify ζ g)[z]? = some fs ∧ ρ ∈ dom fs := by
  intro ρ Hlive
  obtain ⟨ζ', fs, HSome, Hdom⟩ := δ.ls_map_live ρ Hlive
  by_cases h : ζ = ζ'
  · subst h
    refine ⟨ζ, g fs, by rw [getElem?_modify_ite]; simp [HSome], ?_⟩
    exact mem_dom.2 (hg fs ρ (mem_dom.1 Hdom) Hlive)
  · exact ⟨ζ', fs, by rw [getElem?_modify_ite]; simp [h, HSome], Hdom⟩

/-- Rocq `decr_fuel_map`. -/
@[rocq_alias trillium.fairis.decr_fuel_map]
def decrFuelMap (fs : GMap M.fmrole Nat) : GMap M.fmrole Nat :=
  fs.map fun _ f => f - 1

@[rocq_alias trillium.fairis.decr_fuel_map_included]
theorem decr_fuel_map_included (fs : GMap M.fmrole Nat) :
    mapIncluded (fun _ (a b : Nat) => a ≤ b) (decrFuelMap fs) fs := by
  rw [mapIncluded_spec]
  intro k v1 Hm
  rw [decrFuelMap, getElem?_map_eq, Option.map_eq_some_iff] at Hm
  obtain ⟨v2, Hv2, rfl⟩ := Hm
  exact ⟨v2, Hv2, Nat.sub_le _ _⟩

/-- Rocq `filter_fuel_map`: keep the live roles and the roles of `ρs`. -/
@[rocq_alias trillium.fairis.filter_fuel_map]
def filterFuelMap (δ : LiveState Locale M) (ρs : GSet M.fmrole) (fs : GMap M.fmrole Nat) :
    GMap M.fmrole Nat :=
  fs.filter fun ρ _ => decide (ρ ∈ M.liveRoles δ.lsUnder ∨ ρ ∈ ρs)

@[rocq_alias trillium.fairis.filter_fuel_map_included]
theorem filter_fuel_map_included (δ : LiveState Locale M) (ρs : GSet M.fmrole)
    (fs : GMap M.fmrole Nat) :
    mapIncluded (fun _ (a b : Nat) => a ≤ b) (filterFuelMap δ ρs fs) fs := by
  rw [mapIncluded_spec]
  intro k v1 Hm
  rw [filterFuelMap, getElem?_filter_eq, Option.filter_eq_some_iff] at Hm
  exact ⟨v1, Hm.1, Nat.le_refl _⟩

/-- Rocq `model_update_locale_role_map`. -/
@[rocq_alias trillium.fairis.model_update_locale_role_map]
def modelUpdateLocaleRoleMap (δ : LiveState Locale M) (ρs : GSet M.fmrole) :
    GMap M.fmrole Nat → GMap M.fmrole Nat :=
  decrFuelMap ∘ filterFuelMap δ ρs

@[rocq_alias trillium.fairis.model_update_locale_role_map_map_included]
theorem model_update_locale_role_map_map_included (δ : LiveState Locale M)
    (ρs : GSet M.fmrole) (fs : GMap M.fmrole Nat) :
    mapIncluded (fun _ (a b : Nat) => a ≤ b) (modelUpdateLocaleRoleMap δ ρs fs) fs :=
  have : IsTrans Nat (· ≤ ·) := ⟨fun _ _ _ => Nat.le_trans⟩
  mapIncluded_transitivity _ _ _ (decr_fuel_map_included _) (filter_fuel_map_included δ ρs fs)

/-- Rocq `model_update_locale_fuel_map`. -/
@[rocq_alias trillium.fairis.model_update_locale_fuel_map]
def modelUpdateLocaleFuelMap (δ : LiveState Locale M) (ζ : Locale) (ρs : GSet M.fmrole)
    (fm : GMap Locale (GMap M.fmrole Nat)) : GMap Locale (GMap M.fmrole Nat) :=
  fm.insert ζ (modelUpdateLocaleRoleMap δ ρs (fm[ζ]?.getD ∅))

theorem mem_decrFuelMap {fs : GMap M.fmrole Nat} {ρ : M.fmrole} :
    ρ ∈ decrFuelMap fs ↔ ρ ∈ fs :=
  Std.ExtTreeMap.mem_map

theorem mem_filterFuelMap {δ : LiveState Locale M} {ρs : GSet M.fmrole}
    {fs : GMap M.fmrole Nat} {ρ : M.fmrole} :
    ρ ∈ filterFuelMap δ ρs fs ↔ ρ ∈ fs ∧ (ρ ∈ M.liveRoles δ.lsUnder ∨ ρ ∈ ρs) := by
  rw [mem_iff_getElem?, mem_iff_getElem?, filterFuelMap, getElem?_filter_eq]
  cases fs[ρ]? <;> simp [Option.filter]

/-- Decrease the fuel of the roles of `ζ` (Rocq `model_update_decr`). -/
@[rocq_alias trillium.fairis.model_update_decr]
def modelUpdateDecr (ζ : Locale) (δ : LiveState Locale M) : LiveState Locale M where
  lsUnder := δ.lsUnder
  lsMap := δ.lsMap.modify ζ decrFuelMap
  ls_map_disj := disj_of_keys_sub δ _ (modify_keys_sub δ ζ _ fun _ _ h => mem_decrFuelMap.1 h)
  ls_map_live := live_modify δ ζ _ fun _ _ h _ => mem_decrFuelMap.2 h

/-- Remove the dead roles of `ζ` which are not in `ρs` (Rocq `model_update_filter`). -/
@[rocq_alias trillium.fairis.model_update_filter]
def modelUpdateFilter (ζ : Locale) (ρs : GSet M.fmrole) (δ : LiveState Locale M) :
    LiveState Locale M where
  lsUnder := δ.lsUnder
  lsMap := δ.lsMap.modify ζ (filterFuelMap δ ρs)
  ls_map_disj :=
    disj_of_keys_sub δ _ (modify_keys_sub δ ζ _ fun _ _ h => (mem_filterFuelMap.1 h).1)
  ls_map_live := live_modify δ ζ _ fun _ _ h hl => mem_filterFuelMap.2 ⟨h, .inl hl⟩

/-- Rocq `model_update_locale_fuel`. -/
@[rocq_alias trillium.fairis.model_update_locale_fuel]
def modelUpdateLocaleFuel (δ : LiveState Locale M) (ζ : Locale) (ρs : GSet M.fmrole) :
    LiveState Locale M :=
  modelUpdateDecr ζ (modelUpdateFilter ζ ρs δ)

theorem modelUpdateLocaleFuel_lsMap (δ : LiveState Locale M) (ζ : Locale)
    (ρs : GSet M.fmrole) :
    (modelUpdateLocaleFuel δ ζ ρs).lsMap =
      δ.lsMap.modify ζ (modelUpdateLocaleRoleMap δ ρs) := by
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  simp only [modelUpdateLocaleFuel, modelUpdateDecr, modelUpdateFilter, getElem?_modify_ite]
  by_cases h : ζ = k
  · subst h; simp only [ite_true, Option.map_map]; rfl
  · simp [h]

theorem modelUpdateLocaleFuel_lsUnder (δ : LiveState Locale M) (ζ : Locale)
    (ρs : GSet M.fmrole) : (modelUpdateLocaleFuel δ ζ ρs).lsUnder = δ.lsUnder := rfl

/-- Rocq `model_update_set`: set the fuel of `ρ` (owned by `ζ`) to `f`. -/
@[rocq_alias trillium.fairis.model_update_set]
def modelUpdateSet (ζ : Locale) (ρ : M.fmrole) (f : Nat) (δ : LiveState Locale M) :
    LiveState Locale M where
  lsUnder := δ.lsUnder
  lsMap := δ.lsMap.modify ζ fun fs => fs.modify ρ fun _ => f
  ls_map_disj :=
    disj_of_keys_sub δ _ (modify_keys_sub δ ζ _ fun _ _ h => Std.ExtTreeMap.mem_modify.1 h)
  ls_map_live := live_modify δ ζ _ fun _ _ h _ => Std.ExtTreeMap.mem_modify.2 h

/-- Rocq `model_update_state`: replace the underlying model state. -/
@[rocq_alias trillium.fairis.model_update_state]
def modelUpdateState (δ2 : M.fmstate) (δ1 : LiveStateData Locale M) : LiveStateData Locale M where
  lsUnder := δ2
  lsMap := δ1.lsMap

@[rocq_alias trillium.fairis.model_update_state_valid]
theorem model_update_state_valid (δ2 : M.fmstate) (δ1 : LiveState Locale M) :
    M.liveRoles δ2 ⊆ M.liveRoles δ1.lsUnder →
    ∃ δ : LiveState Locale M, δ.toLiveStateData = modelUpdateState δ2 δ1.toLiveStateData := by
  intro Hle
  exact ⟨⟨⟨δ2, δ1.lsMap⟩, δ1.ls_map_disj, fun ρ h => δ1.ls_map_live ρ (Hle ρ h)⟩, rfl⟩

variable (LM : LiveModel Locale M) in
/-- Rocq `model_update_model_step`. (Its Rocq result type is `M`, the live-state data being
coerced; here the live-state data is returned, as used in the Rocq proofs.) -/
@[rocq_alias trillium.fairis.model_update_model_step]
def modelUpdateModelStep (ζ : Locale) (ρs : GSet M.fmrole) (ρ : M.fmrole) (δ2 : M.fmstate)
    (δ : LiveState Locale M) : LiveStateData Locale M :=
  modelUpdateState δ2
    (modelUpdateSet ζ ρ (LM.lmFl δ2) (modelUpdateDecr ζ (modelUpdateFilter ζ ρs δ))).toLiveStateData

@[rocq_alias trillium.fairis.model_update_model_step_valid]
theorem model_update_model_step_valid (LM : LiveModel Locale M) (ζ : Locale)
    (ρs : GSet M.fmrole) (ρ : M.fmrole) (s2 : M.fmstate) (δ1 : LiveState Locale M) :
    M.liveRoles s2 ⊆ M.liveRoles δ1.lsUnder →
    ∃ δ : LiveState Locale M, δ.toLiveStateData = modelUpdateModelStep LM ζ ρs ρ s2 δ1 :=
  fun h => model_update_state_valid s2
    (modelUpdateSet ζ ρ (LM.lmFl s2) (modelUpdateDecr ζ (modelUpdateFilter ζ ρs δ1))) h

/-- Rocq `model_update_split`: the roles of `ρs` owned by `ζ` are given to the new locale
`ζf`. -/
@[rocq_alias trillium.fairis.model_update_split]
def modelUpdateSplit (ζ ζf : Locale) (ρs : GSet M.fmrole) (δ : LiveStateData Locale M) :
    LiveStateData Locale M where
  lsUnder := δ.lsUnder
  lsMap := (δ.lsMap.modify ζ (fun fs => fs.filter fun ρ _ => decide (ρ ∉ ρs))).insert ζf
    ((δ.lsMap[ζ]?.getD ∅).filter fun ρ _ => decide (ρ ∈ ρs))

/-- Rocq `map_live`. -/
@[rocq_alias trillium.fairis.map_live]
def MapLive (ρs : GSet M.fmrole) (m : GMap Locale (GMap M.fmrole Nat)) : Prop :=
  ∀ ρ, ρ ∈ ρs → ∃ (ζ : Locale) (fs : GMap M.fmrole Nat), m[ζ]? = some fs ∧ ρ ∈ dom fs

/-- Rocq `map_disj`. -/
@[rocq_alias trillium.fairis.map_disj]
def MapDisj (m : GMap Locale (GMap M.fmrole Nat)) : Prop :=
  ∀ (ζ ζ' : Locale) (fs fs' : GMap M.fmrole Nat), ζ ≠ ζ' → m[ζ]? = some fs → m[ζ']? = some fs' →
    fs ##ₘ fs'

@[rocq_alias trillium.fairis.model_update_split_valid]
theorem model_update_split_valid (ζ ζf : Locale) (ρs : GSet M.fmrole) (δ1 : LiveState Locale M) :
    ζ ∈ dom δ1.lsMap → ζf ∉ dom δ1.lsMap →
    ∃ δ2 : LiveState Locale M, δ2.toLiveStateData = modelUpdateSplit ζ ζf ρs δ1.toLiveStateData := by
  intro Hin Hnin
  obtain ⟨ρs', HSome⟩ := mem_dom_iff.1 Hin
  have Hnone : δ1.lsMap[ζf]? = none := not_mem_iff.1 fun h => Hnin (mem_dom.2 h)
  have Hneq : ζ ≠ ζf := by
    rintro rfl; rw [HSome] at Hnone; cases Hnone
  set δ2 := modelUpdateSplit ζ ζf ρs δ1.toLiveStateData with hδ2
  -- the fuel maps of `δ2`
  have Hlk : ∀ (z : Locale) (g : GMap M.fmrole Nat), δ2.lsMap[z]? = some g ↔
      (z = ζf ∧ g = ρs'.filter fun ρ _ => decide (ρ ∈ ρs)) ∨
      (z = ζ ∧ g = ρs'.filter fun ρ _ => decide (ρ ∉ ρs)) ∨
      (z ≠ ζ ∧ z ≠ ζf ∧ δ1.lsMap[z]? = some g) := by
    intro z g
    simp only [hδ2, modelUpdateSplit, getElem?_insert_ite, getElem?_modify_ite, HSome,
      Option.getD_some]
    by_cases h1 : ζf = z
    · subst h1
      simp [Ne.symm Hneq, eq_comm]
    · by_cases h2 : ζ = z
      · subst h2
        simp [h1, Ne.symm h1, eq_comm]
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  have Hdisj : ∀ (z z' : Locale) (fs fs' : GMap M.fmrole Nat), z ≠ z' → δ2.lsMap[z]? = some fs →
      δ2.lsMap[z']? = some fs' → fs ##ₘ fs' := by
    intro z z' fs fs' Hne H1 H2
    rw [disjoint_iff_mem]
    intro ρ h1 h2
    have hsub : ∀ (z : Locale) (g : GMap M.fmrole Nat), δ2.lsMap[z]? = some g → ρ ∈ g →
        ((z = ζf ∨ z = ζ) ∧ ρ ∈ ρs' ∧ (z = ζf ↔ ρ ∈ ρs)) ∨
        (z ≠ ζ ∧ z ≠ ζf ∧ δ1.lsMap[z]? = some g) := by
      intro z g H hρ
      rcases (Hlk z g).1 H with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h
      · rw [mem_iff_getElem?, getElem?_filter_eq] at hρ
        refine .inl ⟨.inl rfl, ?_, ?_⟩
        · rw [mem_iff_getElem?]; cases h : ρs'[ρ]? <;> simp_all
        · cases h : ρs'[ρ]? <;> simp_all [Option.filter]
      · rw [mem_iff_getElem?, getElem?_filter_eq] at hρ
        refine .inl ⟨.inr rfl, ?_, ?_⟩
        · rw [mem_iff_getElem?]; cases h : ρs'[ρ]? <;> simp_all
        · cases h : ρs'[ρ]? <;> simp_all [Option.filter]
      · exact .inr h
    rcases hsub z fs H1 h1 with ⟨hz, hρ, hiff⟩ | ⟨hz1, hz2, H1'⟩ <;>
    rcases hsub z' fs' H2 h2 with ⟨hz', hρ', hiff'⟩ | ⟨hz1', hz2', H2'⟩
    · rcases hz with hz | hz <;> rcases hz' with hz' | hz'
      · exact Hne (hz.trans hz'.symm)
      · exact Hneq (hz'.symm.trans (hiff'.2 (hiff.1 hz)))
      · exact Hneq (hz.symm.trans (hiff.2 (hiff'.1 hz')))
      · exact Hne (hz.trans hz'.symm)
    · exact hz1' (ls_map_agree HSome H2' (mem_dom.2 hρ) (mem_dom.2 h2)).1.symm
    · exact hz1 (ls_map_agree HSome H1' (mem_dom.2 hρ') (mem_dom.2 h1)).1.symm
    · exact Hne (ls_map_agree H1' H2' (mem_dom.2 h1) (mem_dom.2 h2)).1
  have Hlive : ∀ ρ, ρ ∈ M.liveRoles δ2.lsUnder → ∃ (z : Locale) (g : GMap M.fmrole Nat),
      δ2.lsMap[z]? = some g ∧ ρ ∈ dom g := by
    intro ρ Hρ
    obtain ⟨ζ', fs, HSome', Hin'⟩ := δ1.ls_map_live ρ Hρ
    by_cases h1 : ζ' = ζ
    · subst h1
      rw [HSome] at HSome'
      cases HSome'
      have hρ : ρs'[ρ]?.isSome := mem_iff_getElem?.1 (mem_dom.1 Hin')
      by_cases h2 : ρ ∈ ρs
      · refine ⟨ζf, _, (Hlk _ _).2 (.inl ⟨rfl, rfl⟩), ?_⟩
        rw [mem_dom, mem_iff_getElem?, getElem?_filter_eq]
        cases h : ρs'[ρ]? <;> simp_all [Option.filter]
      · refine ⟨ζ', _, (Hlk _ _).2 (.inr (.inl ⟨rfl, rfl⟩)), ?_⟩
        rw [mem_dom, mem_iff_getElem?, getElem?_filter_eq]
        cases h : ρs'[ρ]? <;> simp_all [Option.filter]
    · have h3 : ζ' ≠ ζf := by
        rintro rfl; rw [Hnone] at HSome'; cases HSome'
      exact ⟨ζ', fs, (Hlk _ _).2 (.inr (.inr ⟨h1, h3, HSome'⟩)), Hin'⟩
  exact ⟨{ toLiveStateData := δ2, ls_map_disj := Hdisj, ls_map_live := Hlive }, rfl⟩

/-- Rocq `model_update_fork`. -/
@[rocq_alias trillium.fairis.model_update_fork]
def modelUpdateFork (ζ ζf : Locale) (ρs1 ρs2 : GSet M.fmrole) (δ : LiveState Locale M) :
    LiveStateData Locale M :=
  modelUpdateSplit ζ ζf ρs2 (modelUpdateDecr ζ (modelUpdateFilter ζ ρs1 δ)).toLiveStateData

@[rocq_alias trillium.fairis.model_update_fork_valid]
theorem model_update_fork_valid (ζ ζf : Locale) (ρs1 ρs2 : GSet M.fmrole)
    (δ1 : LiveState Locale M) :
    ζ ∈ dom δ1.lsMap → ζf ∉ dom δ1.lsMap →
    ∃ δ2 : LiveState Locale M, δ2.toLiveStateData = modelUpdateFork ζ ζf ρs1 ρs2 δ1 := by
  intro h1 h2
  apply model_update_split_valid
  · rw [mem_dom] at h1 ⊢
    exact Std.ExtTreeMap.mem_modify.2 (Std.ExtTreeMap.mem_modify.2 h1)
  · rw [mem_dom] at h2 ⊢
    exact fun h => h2 (Std.ExtTreeMap.mem_modify.1 (Std.ExtTreeMap.mem_modify.1 h))

theorem LiveStateData.ext' {d1 d2 : LiveStateData Locale M} (h1 : d1.lsUnder = d2.lsUnder)
    (h2 : d1.lsMap = d2.lsMap) : d1 = d2 := by
  cases d1; cases d2; simp_all

/-! ### Sufficient conditions for live-model steps -/

@[rocq_alias trillium.fairis.silent_step_suff_data_weak]
theorem silent_step_suff_data_weak (fl : M.fmstate → Nat) (δ : LiveState Locale M)
    (fs fs' : GMap M.fmrole Nat) (ζ : Locale) :
    δ.lsMap[ζ]? = some fs → fs ≠ ∅ → mapIncluded (fun _ (a b : Nat) => a < b) fs' fs →
    dom fs \ dom fs' ∩ M.liveRoles δ.lsUnder = ∅ →
    ∃ δ' : LiveState Locale M,
      δ'.toLiveStateData = { lsUnder := δ.lsUnder, lsMap := δ.lsMap.insert ζ fs' } ∧
      lsTrans fl δ (.silentStep ζ) δ' := by
  intro Hζ Hne Hle Hlive
  have H1 : dom fs \ (dom fs' ∪ dom (∅ : GMap M.fmrole Nat)) ∩ M.liveRoles δ.lsUnder = ∅ := by
    rw [dom_empty, LawfulSet.union_empty_right]; exact Hlive
  have H2 : dom fs' ∩ dom (∅ : GMap M.fmrole Nat) = ∅ := by
    rw [dom_empty, LawfulSet.inter_empty_right]
  obtain ⟨δ', h1, h2⟩ := silent_step_suff_data fl δ fs fs' ∅ ζ none Hζ Hne
    ((mapIncluded_spec _ _ _).1 Hle) (by intro ρ f h; simp at h) H1 H2
    (by intro _ h; cases h) (fun _ => rfl)
  exact ⟨δ', h1, h2⟩

@[rocq_alias trillium.fairis.silent_step_suff_data_weak_alt]
theorem silent_step_suff_data_weak_alt (fl : M.fmstate → Nat) (δ δ' : LiveState Locale M)
    (fs fs' : GMap M.fmrole Nat) (ζ : Locale) :
    δ.lsUnder = δ'.lsUnder → δ.lsMap[ζ]? = some fs → δ'.lsMap = δ.lsMap.insert ζ fs' →
    fs ≠ ∅ → mapIncluded (fun _ (a b : Nat) => a < b) fs' fs →
    dom fs \ dom fs' ∩ M.liveRoles δ.lsUnder = ∅ →
    lsTrans fl δ (.silentStep ζ) δ' := by
  intro Hδ Hfs Hfs' Hne Hle Hlive
  obtain ⟨δ'', Heq, Htrans⟩ := silent_step_suff_data_weak fl δ fs fs' ζ Hfs Hne Hle Hlive
  have : δ'.toLiveStateData = δ''.toLiveStateData := by
    rw [Heq]; exact LiveStateData.ext' Hδ.symm Hfs'
  show lsTrans fl δ.toLiveStateData _ δ'.toLiveStateData
  rw [this]
  exact Htrans

/-- Rocq `model_can_fuel_step`. -/
@[rocq_alias trillium.fairis.model_can_fuel_step]
def ModelCanFuelStep (δ1 : LiveState Locale M) (ζ : Locale) (δ2 : LiveState Locale M) : Prop :=
  ∃ fs1 fs2 : GMap M.fmrole Nat,
    δ1.lsUnder = δ2.lsUnder ∧
    δ1.lsMap[ζ]? = some fs1 ∧
    δ2.lsMap = δ1.lsMap.insert ζ fs2 ∧
    fs1 ≠ ∅ ∧
    mapIncluded (fun _ (a b : Nat) => a < b) fs2 fs1 ∧
    dom fs1 \ dom fs2 ∩ M.liveRoles δ1.lsUnder = ∅

@[rocq_alias trillium.fairis.model_can_fuel_step_trans]
theorem model_can_fuel_step_trans (fl : M.fmstate → Nat) (ζ : Locale)
    (δ δ' : LiveState Locale M) :
    ModelCanFuelStep δ ζ δ' → lsTrans fl δ (.silentStep ζ) δ' := by
  rintro ⟨fs1, fs2, h1, h2, h3, h4, h5, h6⟩
  exact silent_step_suff_data_weak_alt fl δ δ' fs1 fs2 ζ h1 h2 h3 h4 h5 h6

@[rocq_alias trillium.fairis.model_step_suff_data_weak_alt]
theorem model_step_suff_data_weak_alt (LM : LiveModel Locale M) (δ1 δ2 : LiveState Locale M)
    (ρ : M.fmrole) (fs fs' : GMap M.fmrole Nat) (ζ : Locale) :
    M.fmtrans δ1.lsUnder (some ρ) δ2.lsUnder →
    M.liveRoles δ2.lsUnder ⊆ M.liveRoles δ1.lsUnder →
    δ1.lsMap[ζ]? = some fs →
    δ2.lsMap = δ1.lsMap.insert ζ fs' →
    ρ ∈ dom fs →
    fs'[ρ]? = some (LM.lmFl δ2.lsUnder) →
    mapIncluded (fun _ (a b : Nat) => a < b) (fs'.erase ρ) fs →
    dom fs \ dom fs' ∩ M.liveRoles δ1.lsUnder = ∅ →
    lsTrans LM.lmFl δ1 (.takeStep ρ ζ) δ2 := by
  intro Hstep Hlive Hfs Hfs' Hρ Hρ' Hlt Hlive'
  rw [mapIncluded_spec] at Hlt
  have Hsub : ∀ ρ', ρ' ∈ fs' → ρ' ∈ fs := by
    intro ρ' h
    by_cases e : ρ' = ρ
    · subst e; exact mem_dom.1 Hρ
    · obtain ⟨f', hf'⟩ := mem_iff_exists.1 h
      have : (fs'.erase ρ)[ρ']? = some f' := by rw [getElem?_erase_ite]; simp [Ne.symm e, hf']
      obtain ⟨v, hv, -⟩ := Hlt ρ' f' this
      exact mem_of_getElem? hv
  have Hempty : dom fs' \ dom fs = ∅ := by
    rw [LawfulSet.eq_empty_iff]
    intro x hx
    rw [mem_diff, mem_dom, mem_dom] at hx
    exact hx.2 (Hsub x hx.1)
  obtain ⟨δ'', Heq, Htrans⟩ := model_step_suff_data LM.lmFl δ1 ρ δ2.lsUnder fs fs' ζ Hstep Hfs Hρ
    (by
      intro ρ' f f' h1 hne h2
      have : (fs'.erase ρ)[ρ']? = some f' := by rw [getElem?_erase_ite]; simp [Ne.symm hne, h1]
      obtain ⟨v, hv, hlt⟩ := Hlt ρ' f' this
      rw [h2] at hv; cases hv; exact hlt)
    (by intro f h; rw [Hρ'] at h; cases h; exact Nat.le_refl _)
    (by intro ρ' h; rw [Hempty] at h; exact absurd h LawfulSet.mem_empty)
    (by
      rw [Hempty, LawfulSet.eq_empty_iff]
      intro x hx
      rw [mem_diff] at hx
      exact hx.2 (Hlive x hx.1))
    (by
      intro ρ' h
      rw [mem_diff] at h
      exact absurd (Hlive ρ' h.1) h.2)
    Hlive'
  have : δ2.toLiveStateData = δ''.toLiveStateData := by
    rw [Heq]; exact LiveStateData.ext' rfl Hfs'
  show lsTrans LM.lmFl δ1.toLiveStateData _ δ2.toLiveStateData
  rw [this]
  exact Htrans

/-- Rocq `model_can_model_step`. -/
@[rocq_alias trillium.fairis.model_can_model_step]
def ModelCanModelStep (LM : LiveModel Locale M) (δ1 : LiveState Locale M) (ζ : Locale)
    (ρ : M.fmrole) (δ2 : LiveState Locale M) : Prop :=
  ∃ fs fs' : GMap M.fmrole Nat,
    M.fmtrans δ1.lsUnder (some ρ) δ2.lsUnder ∧
    M.liveRoles δ2.lsUnder ⊆ M.liveRoles δ1.lsUnder ∧
    δ1.lsMap[ζ]? = some fs ∧
    δ2.lsMap = δ1.lsMap.insert ζ fs' ∧
    ρ ∈ dom fs ∧
    fs'[ρ]? = some (LM.lmFl δ2.lsUnder) ∧
    mapIncluded (fun _ (a b : Nat) => a < b) (fs'.erase ρ) fs ∧
    dom fs \ dom fs' ∩ M.liveRoles δ1.lsUnder = ∅

@[rocq_alias trillium.fairis.model_can_model_step_trans]
theorem model_can_model_step_trans (LM : LiveModel Locale M) (ζ : Locale) (ρ : M.fmrole)
    (δ δ' : LiveState Locale M) :
    ModelCanModelStep LM δ ζ ρ δ' → lsTrans LM.lmFl δ (.takeStep ρ ζ) δ' := by
  rintro ⟨fs, fs', h1, h2, h3, h4, h5, h6, h7, h8⟩
  exact model_step_suff_data_weak_alt LM δ δ' ρ fs fs' ζ h1 h2 h3 h4 h5 h6 h7 h8

/-- Rocq `model_can_fork_step`. -/
@[rocq_alias trillium.fairis.model_can_fork_step]
def ModelCanForkStep (δ1 : LiveState Locale M) (ζ ζf : Locale) (δ2 : LiveState Locale M) :
    Prop :=
  ∃ fs fs1 fs2 : GMap M.fmrole Nat,
    δ1.lsUnder = δ2.lsUnder ∧
    δ1.lsMap[ζ]? = some fs ∧ fs ≠ ∅ ∧
    δ2.lsMap = (δ1.lsMap.insert ζf fs2).insert ζ fs1 ∧
    mapIncluded (fun _ (a b : Nat) => a < b) fs1 fs ∧
    mapIncluded (fun _ (a b : Nat) => a < b) fs2 fs ∧
    dom fs \ (dom fs1 ∪ dom fs2) ∩ M.liveRoles δ1.lsUnder = ∅ ∧
    dom fs1 ∩ dom fs2 = ∅ ∧
    ζf ∉ dom δ1.lsMap

@[rocq_alias trillium.fairis.silent_step_suff_data_fork_weak]
theorem silent_step_suff_data_fork_weak (fl : M.fmstate → Nat) (δ : LiveState Locale M)
    (fs fs1 fs2 : GMap M.fmrole Nat) (ζ ζf : Locale) :
    δ.lsMap[ζ]? = some fs → fs ≠ ∅ →
    mapIncluded (fun _ (a b : Nat) => a < b) fs1 fs →
    mapIncluded (fun _ (a b : Nat) => a < b) fs2 fs →
    dom fs \ (dom fs1 ∪ dom fs2) ∩ M.liveRoles δ.lsUnder = ∅ →
    dom fs1 ∩ dom fs2 = ∅ →
    ζf ∉ dom δ.lsMap →
    ∃ δ' : LiveState Locale M,
      δ'.toLiveStateData =
        { lsUnder := δ.lsUnder, lsMap := (δ.lsMap.insert ζf fs2).insert ζ fs1 } ∧
      lsTrans fl δ (.silentStep ζ) δ' := by
  intro Hζ Hne H1 H2 Hlive Hdisj Hnin
  obtain ⟨δ', h1, h2⟩ := silent_step_suff_data fl δ fs fs1 fs2 ζ (some ζf) Hζ Hne
    ((mapIncluded_spec _ _ _).1 H1) ((mapIncluded_spec _ _ _).1 H2) Hlive Hdisj
    (by intro z h; cases h; exact Hnin) (by intro h; cases h)
  exact ⟨δ', h1, h2⟩

@[rocq_alias trillium.fairis.silent_step_suff_data_fork_weak_alt]
theorem silent_step_suff_data_fork_weak_alt (fl : M.fmstate → Nat) (δ δ' : LiveState Locale M)
    (fs fs1 fs2 : GMap M.fmrole Nat) (ζ ζf : Locale) :
    δ.lsUnder = δ'.lsUnder →
    δ.lsMap[ζ]? = some fs →
    δ'.lsMap = (δ.lsMap.insert ζf fs2).insert ζ fs1 →
    fs ≠ ∅ →
    mapIncluded (fun _ (a b : Nat) => a < b) fs1 fs →
    mapIncluded (fun _ (a b : Nat) => a < b) fs2 fs →
    dom fs \ (dom fs1 ∪ dom fs2) ∩ M.liveRoles δ.lsUnder = ∅ →
    dom fs1 ∩ dom fs2 = ∅ →
    ζf ∉ dom δ.lsMap →
    lsTrans fl δ (.silentStep ζ) δ' := by
  intro Hδ Hfs Hfs12 Hne H1 H2 Hlive Hdisj Hnin
  obtain ⟨δ'', Heq, Htrans⟩ :=
    silent_step_suff_data_fork_weak fl δ fs fs1 fs2 ζ ζf Hfs Hne H1 H2 Hlive Hdisj Hnin
  have : δ'.toLiveStateData = δ''.toLiveStateData := by
    rw [Heq]; exact LiveStateData.ext' Hδ.symm Hfs12
  show lsTrans fl δ.toLiveStateData _ δ'.toLiveStateData
  rw [this]
  exact Htrans

@[rocq_alias trillium.fairis.model_can_fork_step_trans]
theorem model_can_fork_step_trans (fl : M.fmstate → Nat) (ζ ζf : Locale)
    (δ δ' : LiveState Locale M) :
    ModelCanForkStep δ ζ ζf δ' → lsTrans fl δ (.silentStep ζ) δ' := by
  rintro ⟨fs, fs1, fs2, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact silent_step_suff_data_fork_weak_alt fl δ δ' fs fs1 fs2 ζ ζf h1 h2 h4 h3 h5 h6 h7 h8 h9

end live_state_updates

/-! ## Fuel maps -/

section fuel_maps

variable {Locale : Type} [Ord Locale] [Std.TransOrd Locale] [Std.LawfulEqOrd Locale]
variable {M : FairModel}

@[rocq_alias trillium.fairis.decr_succ_compose_id]
theorem decr_succ_compose_id : (fun f : Nat => f - 1) ∘ Nat.succ = id := by
  funext x; simp

/-- Rocq `map_inner_disj`. -/
@[rocq_alias trillium.fairis.map_inner_disj]
def MapInnerDisj {K1 K2 V : Type _} [Ord K1] [Std.TransOrd K1] [Std.LawfulEqOrd K1] [Ord K2]
    [Std.TransOrd K2] [Std.LawfulEqOrd K2] (m : GMap K1 (GMap K2 V)) : Prop :=
  ∀ (k1 k2 : K1) (vs1 vs2 : GMap K2 V), k1 ≠ k2 → m[k1]? = some vs1 → m[k2]? = some vs2 →
    vs1 ##ₘ vs2

theorem fuelMapLeInner_spec {fm fm' : GMap Locale (GMap M.fmrole Nat)} :
    fuelMapLeInner fm fm' ↔ ∀ (ζ : Locale) (fs : GMap M.fmrole Nat), fm[ζ]? = some fs →
      ∃ fs', fm'[ζ]? = some fs' ∧ mapIncluded (fun _ (a b : Nat) => a ≤ b) fs fs' :=
  mapIncluded_spec _ _ _

@[rocq_alias trillium.fairis.fuel_map_le_disj]
theorem fuel_map_le_disj (ζ1 ζ2 : Locale) (fm : GMap Locale (GMap M.fmrole Nat))
    (fs1 fs2 : GMap M.fmrole Nat) (ρ : M.fmrole) (fuelMap : GMap Locale (GMap M.fmrole Nat)) :
    fuelMapLeInner fm fuelMap → MapInnerDisj fuelMap →
    fm[ζ1]? = some fs1 → fm[ζ2]? = some fs2 → ρ ∈ dom fs1 → ρ ∈ dom fs2 →
    ζ1 = ζ2 ∧ fs1 = fs2 := by
  intro Hle Hdisj HSome1 HSome2 Hf1 Hf2
  by_cases h : ζ1 = ζ2
  · subst h; rw [HSome1] at HSome2; cases HSome2; exact ⟨rfl, rfl⟩
  · exfalso
    rw [fuelMapLeInner_spec] at Hle
    obtain ⟨fs1', Hfs1', Hle1⟩ := Hle ζ1 fs1 HSome1
    obtain ⟨fs2', Hfs2', Hle2⟩ := Hle ζ2 fs2 HSome2
    have h1 := mapIncluded_subseteq_inv _ _ _ Hle1 ρ (mem_dom.1 Hf1)
    have h2 := mapIncluded_subseteq_inv _ _ _ Hle2 ρ (mem_dom.1 Hf2)
    rcases Hdisj ζ1 ζ2 fs1' fs2' h Hfs1' Hfs2' ρ with e | e
    · exact (not_mem_iff.2 e) h1
    · exact (not_mem_iff.2 e) h2

@[rocq_alias trillium.fairis.fuel_map_le_disj']
theorem fuel_map_le_disj' (ζ1 ζ2 : Locale) (fm : GMap Locale (GMap M.fmrole Nat))
    (fs1 fs2 fs1' fs2' : GMap M.fmrole Nat) (ρ : M.fmrole)
    (fuelMap : GMap Locale (GMap M.fmrole Nat)) :
    fuelMapLeInner fm fuelMap → MapInnerDisj fuelMap →
    fm[ζ1]? = some fs1 → fm[ζ2]? = some fs2 →
    fuelMap[ζ1]? = some fs1' → fuelMap[ζ2]? = some fs2' →
    ρ ∈ dom fs1' → ρ ∈ dom fs2' →
    ζ1 = ζ2 ∧ fs1 = fs2 := by
  intro _ Hdisj HSome1 HSome2 HSome1' HSome2' Hf1 Hf2
  by_cases h : ζ1 = ζ2
  · subst h; rw [HSome1] at HSome2; cases HSome2; exact ⟨rfl, rfl⟩
  · exfalso
    rcases Hdisj ζ1 ζ2 fs1' fs2' h HSome1' HSome2' ρ with e | e
    · exact (not_mem_iff.2 e) (mem_dom.1 Hf1)
    · exact (not_mem_iff.2 e) (mem_dom.1 Hf2)

@[rocq_alias trillium.fairis.fuel_map_le_live_roles]
theorem fuel_map_le_live_roles (fm fm' : GMap Locale (GMap M.fmrole Nat)) (lρs : GSet M.fmrole)
    (ζ : Locale) (ρs ρs' : GMap M.fmrole Nat) (ρ : M.fmrole) :
    MapInnerDisj fm' → fuelMapLeInner fm fm' → fuelMapPreserveDead fm lρs →
    fm[ζ]? = some ρs → fm'[ζ]? = some ρs' → ρ ∈ lρs → ρ ∈ dom ρs' → ρ ∈ dom ρs := by
  intro Hdisj Hfmle Hfmdead Hρ Hρs' Hlive Hf
  obtain ⟨ζ', fs', Hfs', Hv2'⟩ := Hfmdead ρ Hlive
  obtain ⟨fs'', Hfs'', Hle⟩ := fuelMapLeInner_spec.1 Hfmle ζ' fs' Hfs'
  have := mapIncluded_subseteq_inv _ _ _ Hle ρ (mem_dom.1 Hv2')
  obtain ⟨-, e⟩ := fuel_map_le_disj' ζ ζ' fm ρs fs' ρs' fs'' ρ fm' Hfmle Hdisj Hρ Hfs' Hρs' Hfs''
    Hf (mem_dom.2 this)
  subst e
  exact Hv2'

theorem mapInnerDisj_lsMap (δ : LiveState Locale M) : MapInnerDisj δ.lsMap :=
  fun _ _ _ _ h1 h2 h3 => δ.ls_map_disj _ _ _ _ h1 h2 h3

@[rocq_alias trillium.fairis.alter_insert_alt]
theorem alter_insert_alt {K A : Type _} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]
    (m : GMap K A) (i : K) (f : A → A) (x : A) :
    m[i]? = some x → m.modify i f = m.insert i (f x) := by
  intro h
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  rw [getElem?_modify_ite, getElem?_insert_ite]
  by_cases e : i = k
  · subst e; simp [h]
  · simp [e]

end fuel_maps

/-! ## Locales of forked threads -/

section fork_locales

variable {Locale : Type} [Ord Locale] [Std.TransOrd Locale] [Std.LawfulEqOrd Locale]
variable {Expr State : Type _} [LanguageCore Expr State Locale]

/-- `e` was forked from the thread pool `tp1`, giving `tp2` (Rocq `has_forked`). -/
@[rocq_alias trillium.fairis.has_forked]
def HasForked (tp1 tp2 : List Expr) (e : Expr) : Prop :=
  ∃ tp1', tp2 = tp1' ++ [e] ∧ LocalesEquiv tp1 tp1'

@[rocq_alias trillium.fairis.not_elem_of_locale_of_from_list]
theorem not_elem_of_locale_of_from_list (tp : List Expr) (e : Expr) :
    localeOf tp e ∉ localesOfList tp := by
  intro Habs
  obtain ⟨⟨tp1, e1⟩, Hpf, Hlo⟩ := List.mem_map.1 Habs
  obtain ⟨tp2, tp3, He1, He2⟩ := (mem_prefixesFrom_iff _ _ _ _).1 Hpf
  simp only [List.nil_append] at He1
  subst He1 He2
  have Hdone : (tp1 ++ e1 :: tp3, e) ∈ prefixesFrom (tp1 ++ [e1]) (tp3 ++ [e]) :=
    (mem_prefixesFrom_iff _ _ _ _).2 ⟨tp3, [], by simp, by simp⟩
  exact LanguageCore.locale_injective tp1 e1 (tp3 ++ [e]) _ e Hdone Hlo

@[rocq_alias trillium.fairis.elem_of_locale_of_from_list]
theorem elem_of_locale_of_from_list (tp1 tp2 : List Expr) (e : Expr) :
    LocalesEquiv tp1 tp2 → localeOf tp1 e ∈ localesOfList (tp2 ++ [e]) := by
  intro Heq
  rw [LanguageCore.locale_equiv tp1 tp2 e Heq]
  exact List.mem_map.2 ⟨(tp2, e), (mem_prefixesFrom_iff _ _ _ _).2 ⟨tp2, [], by simp, by simp⟩,
    rfl⟩

end fork_locales

/-! ## Disjointness of sets -/

section sets

variable {A : Type _} [Ord A] [Std.TransOrd A] [Std.LawfulEqOrd A]

@[rocq_alias trillium.fairis.disjoint_subseteq]
theorem disjoint_subseteq (xs1 xs2 ys1 ys2 : GSet A) :
    xs1 ⊆ xs2 → ys1 ⊆ ys2 → xs2 ## ys2 → xs1 ## ys1 :=
  fun h1 h2 hd x ⟨a, b⟩ => hd x ⟨h1 x a, h2 x b⟩

@[rocq_alias trillium.fairis.disjoint_subseteq_l]
theorem disjoint_subseteq_l (xs ys zs : GSet A) : xs ⊆ ys → ys ## zs → xs ## zs :=
  fun h hd x ⟨a, b⟩ => hd x ⟨h x a, b⟩

@[rocq_alias trillium.fairis.disjoint_subseteq_r]
theorem disjoint_subseteq_r (xs ys zs : GSet A) : zs ⊆ ys → xs ## ys → xs ## zs :=
  fun h hd x ⟨a, b⟩ => hd x ⟨a, h x b⟩

end sets

/-! ## Pure lemmas about fuel maps -/

section fuel_map_lemmas

variable {K V : Type _} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]

theorem mem_insert_eq {m : GMap K V} {k a : K} {v : V} : a ∈ m.insert k v ↔ k = a ∨ a ∈ m := by
  rw [Std.ExtTreeMap.mem_insert, Std.LawfulEqOrd.compare_eq_iff_eq]

theorem dom_insert_insert {W : Type _} {m1 : GMap K V} {m2 : GMap K W} (k : K) (a : V) (b : W) :
    dom m1 = dom m2 → dom (m1.insert k a) = dom (m2.insert k b) := by
  intro h
  ext x
  have := congrArg (x ∈ ·) h
  simp only [mem_dom, eq_iff_iff] at this
  rw [mem_dom, mem_dom, mem_insert_eq, mem_insert_eq, this]

theorem dom_insert_of_mem {m : GMap K V} {k : K} {v : V} (h : k ∈ m) :
    dom (m.insert k v) = dom m := by
  ext x
  rw [mem_dom, mem_dom, mem_insert_eq]
  constructor
  · rintro (rfl | h') <;> assumption
  · exact .inr

theorem insert_self_of_getElem? {m : GMap K V} {k : K} {v : V} (h : m[k]? = some v) :
    m.insert k v = m := by
  apply Std.ExtTreeMap.ext_getElem?
  intro x
  rw [getElem?_insert_ite]
  by_cases e : k = x
  · subst e; simp [h]
  · simp [e]

theorem getElem?_succ_map {m : GMap K Nat} {k : K} :
    (m.map fun _ f => f + 1)[k]? = m[k]?.map (· + 1) :=
  getElem?_map_eq

end fuel_map_lemmas

section fuel_map_lemmas2

variable {Locale : Type} [Ord Locale] [Std.TransOrd Locale] [Std.LawfulEqOrd Locale]
variable {M : FairModel}

theorem preserveDead_insert {fm : GMap Locale (GMap M.fmrole Nat)} {ζ : Locale}
    {fs0 fs : GMap M.fmrole Nat} {D D' : GSet M.fmrole} (h : fm[ζ]? = some fs0)
    (hsub : ∀ ρ, ρ ∈ D' → ρ ∈ D) (hfs : ∀ ρ, ρ ∈ fs0 → ρ ∈ D' → ρ ∈ fs) :
    fuelMapPreserveDead fm D → fuelMapPreserveDead (fm.insert ζ fs) D' := by
  intro Hdead ρ hρ
  obtain ⟨ζ', ρs, H, Hin⟩ := Hdead ρ (hsub ρ hρ)
  by_cases e : ζ = ζ'
  · subst e
    rw [h] at H; cases H
    exact ⟨ζ, fs, by rw [getElem?_insert_ite]; simp, mem_dom.2 (hfs ρ (mem_dom.1 Hin) hρ)⟩
  · exact ⟨ζ', ρs, by rw [getElem?_insert_ite]; simp [e, H], Hin⟩

variable {Expr State : Type _} [LanguageCore Expr State Locale]

theorem preserveThreadpool_mono {tp1 tp2 : List Expr} {fm fm' : GMap Locale (GMap M.fmrole Nat)}
    (htp : ∀ z, z ∉ localesOfList tp2 → z ∉ localesOfList tp1)
    (hkeys : ∀ z, z ∈ fm' → z ∈ fm ∨ z ∈ localesOfList tp2) :
    fuelMapPreserveThreadpool tp1 fm → fuelMapPreserveThreadpool tp2 fm' := by
  intro Htp z hz
  apply not_mem_iff.1
  intro hin
  rcases hkeys z hin with h | h
  · exact (not_mem_iff.2 (Htp z (htp z hz))) h
  · exact hz h

end fuel_map_lemmas2

section step_lemmas

variable {Locale : Type} [Ord Locale] [Std.TransOrd Locale] [Std.LawfulEqOrd Locale]
  [DecidableEq Locale]
variable {M : FairModel}
variable {Expr Val Ectx State : Type _} [Language Expr Val Ectx State Locale]

theorem locales_not_mem_of_step {tp1 tp2 : List Expr} {σ1 σ2 : State} {oζ : Option Locale}
    (Hstep : Language.LocaleStep (tp1, σ1) oζ (tp2, σ2)) :
    ∀ z, z ∉ localesOfList tp2 → z ∉ localesOfList tp1 :=
  fun _ hz h => hz (localesOfList_step_incl Hstep h)

@[rocq_alias trillium.fairis.fuel_map_preserve_threadpool_fuel_step]
theorem fuel_map_preserve_threadpool_fuel_step (c1 : List Expr × State) (ζ : Locale)
    (c2 : List Expr × State) (fm1 fm2 : GMap Locale (GMap M.fmrole Nat)) :
    dom fm1 = dom fm2 → Language.LocaleStep c1 (some ζ) c2 →
    fuelMapPreserveThreadpool c1.1 fm1 → fuelMapPreserveThreadpool c2.1 fm2 := by
  intro Hdom Hstep
  obtain ⟨tp1, σ1⟩ := c1
  obtain ⟨tp2, σ2⟩ := c2
  refine preserveThreadpool_mono (locales_not_mem_of_step Hstep) fun z hz => .inl ?_
  rw [← mem_dom, Hdom, mem_dom]
  exact hz

end step_lemmas

/-! ## Fuel steps -/

section fuel_steps

variable {Locale : Type} [Ord Locale] [Std.TransOrd Locale] [Std.LawfulEqOrd Locale]
  [DecidableEq Locale]
variable {M : FairModel} {LM : LiveModel Locale M} {GF : BundledGFunctors}
variable {Expr Val Ectx State : Type _} [Language Expr Val Ectx State Locale]

@[rocq_alias trillium.fairis.model_update_locale_spec]
theorem model_update_locale_spec (extr : ExecutionTrace Expr) (auxtr : AuxiliaryTrace LM.toModel)
    (ζ : Locale) (c2 : List Expr × State) (ρs : GSet M.fmrole) :
    ModelCanFuelStep auxtr.last ζ (modelUpdateLocaleFuel auxtr.last ζ ρs) →
    tidsSmaller c2.1 (modelUpdateLocaleFuel auxtr.last ζ ρs) →
    validStateEvolutionFairness LM (extr.extend (some ζ) c2)
      (auxtr.extend (.silentStep ζ) (modelUpdateLocaleFuel auxtr.last ζ ρs)) := by
  intro Hstep Htids
  exact ⟨rfl, model_can_fuel_step_trans _ _ _ _ Hstep, Htids⟩

@[rocq_alias trillium.fairis.fuel_map_le_fuel_step]
theorem fuel_map_le_fuel_step (fm : GMap Locale (GMap M.fmrole Nat)) (ζ : Locale)
    (fs : GMap M.fmrole Nat) (δ : LiveState Locale M) :
    fm[ζ]? = some (fs.map fun _ f => f + 1) → fuelMapLe fm δ.lsMap →
    fuelMapLe (fm.insert ζ fs) (modelUpdateLocaleFuel δ ζ (dom fs)).lsMap := by
  intro Hagree ⟨Hfmle, Hfmdom⟩
  obtain ⟨v2, HSome, Hle⟩ := fuelMapLeInner_spec.1 Hfmle ζ _ Hagree
  rw [modelUpdateLocaleFuel_lsMap, alter_insert_alt _ _ _ _ HSome]
  refine ⟨mapIncluded_insert _ _ _ _ _ _ ?_ Hfmle, dom_insert_insert _ _ _ Hfmdom⟩
  rw [mapIncluded_spec]
  intro ρ f1 Hρ
  obtain ⟨x, hx, hle⟩ := (mapIncluded_spec _ _ _).1 Hle ρ (f1 + 1)
    (by rw [getElem?_succ_map, Hρ]; rfl)
  refine ⟨x - 1, ?_, by omega⟩
  simp only [modelUpdateLocaleRoleMap, Function.comp_apply, decrFuelMap, filterFuelMap,
    getElem?_map_eq, getElem?_filter_eq, hx]
  simp [Option.filter, mem_dom, mem_of_getElem? Hρ]

@[rocq_alias trillium.fairis.fuel_map_preserve_dead_fuel_step]
theorem fuel_map_preserve_dead_fuel_step (fm : GMap Locale (GMap M.fmrole Nat)) (ζ : Locale)
    (fs : GMap M.fmrole Nat) (δ : LiveState Locale M) :
    fm[ζ]? = some (fs.map fun _ f => f + 1) →
    fuelMapPreserveDead fm (M.liveRoles (modelUpdateLocaleFuel δ ζ (dom fs)).lsUnder) →
    fuelMapPreserveDead (fm.insert ζ fs)
      (M.liveRoles (modelUpdateLocaleFuel δ ζ (dom fs)).lsUnder) := by
  intro Hagree
  exact preserveDead_insert Hagree (fun _ h => h) fun _ h _ => Std.ExtTreeMap.mem_map.1 h

theorem can_fuel_step_pure (fm : GMap Locale (GMap M.fmrole Nat)) (δ : LiveState Locale M)
    (ζ : Locale) (fs : GMap M.fmrole Nat) (Hfs : fs ≠ ∅) (Hfmle : fuelMapLe fm δ.lsMap)
    (Hfmdead : fuelMapPreserveDead fm (M.liveRoles δ.lsUnder))
    (Hagree : fm[ζ]? = some (fs.map fun _ f => f + 1)) :
    ModelCanFuelStep δ ζ (modelUpdateLocaleFuel δ ζ (dom fs)) := by
  obtain ⟨v2, HSome, Hle⟩ := fuelMapLeInner_spec.1 Hfmle.1 ζ _ Hagree
  refine ⟨v2, modelUpdateLocaleRoleMap δ (dom fs) v2, rfl, HSome, ?_, ?_, ?_, ?_⟩
  · rw [modelUpdateLocaleFuel_lsMap, alter_insert_alt _ _ _ _ HSome]
  · rintro rfl
    apply Hfs
    rw [eq_empty_iff]
    intro k
    apply not_mem_iff.1
    intro hk
    have := mapIncluded_subseteq_inv _ _ _ Hle k (Std.ExtTreeMap.mem_map.2 hk)
    exact Std.ExtTreeMap.not_mem_empty this
  · rw [mapIncluded_spec]
    intro k v1 Hv
    simp only [modelUpdateLocaleRoleMap, Function.comp_apply, decrFuelMap, filterFuelMap,
      getElem?_map_eq, getElem?_filter_eq] at Hv
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 Hv
    obtain ⟨hx2, hcond⟩ := Option.filter_eq_some_iff.1 hx
    have hk : k ∈ dom fs := by
      rcases of_decide_eq_true hcond with hl | hd
      · have := fuel_map_le_live_roles fm δ.lsMap (M.liveRoles δ.lsUnder) ζ _ v2 k
          (mapInnerDisj_lsMap δ) Hfmle.1 Hfmdead Hagree HSome hl (mem_dom.2 (mem_of_getElem? hx2))
        rw [mem_dom, Std.ExtTreeMap.mem_map] at this
        exact mem_dom.2 this
      · exact hd
    obtain ⟨g, hg⟩ := mem_dom_iff.1 hk
    obtain ⟨y, hy, hle⟩ := (mapIncluded_spec _ _ _).1 Hle k (g + 1)
      (by rw [getElem?_succ_map, hg]; rfl)
    rw [hx2] at hy
    cases hy
    exact ⟨x, hx2, by omega⟩
  · rw [LawfulSet.eq_empty_iff]
    intro k hk
    rw [mem_inter, mem_diff, mem_dom, mem_dom] at hk
    obtain ⟨⟨h1, h2⟩, h3⟩ := hk
    apply h2
    simp only [modelUpdateLocaleRoleMap, Function.comp_apply]
    rw [mem_decrFuelMap, mem_filterFuelMap]
    exact ⟨h1, .inl h3⟩

variable [fG : FairnessGS LM GF]

@[rocq_alias trillium.fairis.model_state_interp_has_fuels_decr]
theorem model_state_interp_has_fuels_decr (tp : List Expr) (δ : LiveState Locale M)
    (tid : Locale) (fs : GMap M.fmrole Nat) :
    ⊢ modelStateInterp (GF := GF) tp δ -∗ hasFuelsS tid fs ==∗
      modelStateInterp tp δ ∗ hasFuels tid fs := by
  unfold modelStateInterp hasFuelsS
  iintro ⟨%fm, %Hfmle, %Hfmdead, %Htp, Hδ, Hfm⟩ Hfs
  icombine Hfm Hfs gives %Hagree
  imod has_fuels_update (fs' := fs) $$ Hfm Hfs with ⟨Hfm, Hfs⟩
  obtain ⟨v2, HSome, Hle⟩ := fuelMapLeInner_spec.1 Hfmle.1 tid _ Hagree
  have P1 : fuelMapLe (fm.insert tid fs) δ.lsMap := by
    rw [← insert_self_of_getElem? HSome]
    refine ⟨mapIncluded_insert _ _ _ _ _ _ ?_ Hfmle.1, dom_insert_insert _ _ _ Hfmle.2⟩
    have : IsTrans Nat (· ≤ ·) := ⟨fun _ _ _ => Nat.le_trans⟩
    refine mapIncluded_transitivity _ _ _ ?_ Hle
    exact mapIncluded_fmap _ _ _ fun x => Nat.le_succ x
  have P2 : fuelMapPreserveDead (fm.insert tid fs) (M.liveRoles δ.lsUnder) :=
    preserveDead_insert Hagree (fun _ h => h) (fun _ h _ => Std.ExtTreeMap.mem_map.1 h) Hfmdead
  have P3 : fuelMapPreserveThreadpool tp (fm.insert tid fs) := by
    refine preserveThreadpool_mono (fun _ h => h) (fun z hz => .inl ?_) Htp
    rcases mem_insert_eq.1 hz with rfl | h
    · exact mem_of_getElem? Hagree
    · exact h
  imodintro
  iframe Hfs
  iexists fm.insert tid fs
  iframe %P1 %P2 %P3 Hδ Hfm

@[rocq_alias trillium.fairis.model_state_interp_has_fuels_dealloc]
theorem model_state_interp_has_fuels_dealloc (tid : Locale) (fs : GMap M.fmrole Nat)
    (ρ : M.fmrole) (tp : List Expr) (δ : M.fmstate) (δ' : LiveState Locale M) :
    ρ ∉ M.liveRoles δ →
    ⊢ modelStateInterp (GF := GF) tp δ' -∗ fragModelIs δ -∗ hasFuels tid fs ==∗
      modelStateInterp tp δ' ∗ fragModelIs δ ∗ hasFuels tid (fs.erase ρ) := by
  intro Hρ
  unfold modelStateInterp
  iintro ⟨%fm, %Hfmle, %Hfmdead, %Htp, Hm, Hfm⟩ Hst Hfs
  icombine Hm Hst gives %Heq
  icombine Hfm Hfs gives %Hagree
  imod has_fuels_delete (ρ := ρ) $$ Hfm Hfs with ⟨Hfm, Hfs⟩
  obtain ⟨v2, HSome, Hle⟩ := fuelMapLeInner_spec.1 Hfmle.1 tid _ Hagree
  have P1 : fuelMapLe (fm.insert tid (fs.erase ρ)) δ'.lsMap := by
    rw [← insert_self_of_getElem? HSome]
    refine ⟨mapIncluded_insert _ _ _ _ _ _ ?_ Hfmle.1, dom_insert_insert _ _ _ Hfmle.2⟩
    refine mapIncluded_subseteq _ _ _ _ (fun k v h => ?_) Hle
    rw [getElem?_erase_ite] at h
    split at h
    · cases h
    · exact h
  have P2 : fuelMapPreserveDead (fm.insert tid (fs.erase ρ)) (M.liveRoles δ'.lsUnder) := by
    refine preserveDead_insert Hagree (fun _ h => h) (fun ρ' h hl => ?_) Hfmdead
    rw [Std.ExtTreeMap.mem_erase]
    refine ⟨fun h' => ?_, h⟩
    rw [Std.LawfulEqOrd.compare_eq_iff_eq] at h'
    subst h'
    exact Hρ (Heq ▸ hl)
  have P3 : fuelMapPreserveThreadpool tp (fm.insert tid (fs.erase ρ)) := by
    refine preserveThreadpool_mono (fun _ h => h) (fun z hz => .inl ?_) Htp
    rcases mem_insert_eq.1 hz with rfl | h
    · exact mem_of_getElem? Hagree
    · exact h
  imodintro
  iframe Hst Hfs
  iexists fm.insert tid (fs.erase ρ)
  iframe %P1 %P2 %P3 Hm Hfm

@[rocq_alias trillium.fairis.model_state_interp_has_fuels_agree]
theorem model_state_interp_has_fuels_agree (es : List Expr) (δ : LiveState Locale M)
    (ζ : Locale) (fs : GMap M.fmrole Nat) :
    ⊢ modelStateInterp (GF := GF) es δ -∗ hasFuels ζ fs -∗
      ⌜∃ fs', δ.lsMap[ζ]? = some fs' ∧ mapIncluded (fun _ (a b : Nat) => a ≤ b) fs fs'⌝ := by
  unfold modelStateInterp
  iintro ⟨%fm, %Hfmle, -, -, -, Hfm⟩ Hf
  icombine Hfm Hf gives %Hagree
  ipureintro
  exact fuelMapLeInner_spec.1 Hfmle.1 ζ fs Hagree

@[rocq_alias trillium.fairis.model_state_interp_can_fuel_step]
theorem model_state_interp_can_fuel_step (es : List Expr) (δ : LiveState Locale M) (ζ : Locale)
    (fs : GMap M.fmrole Nat) :
    fs ≠ ∅ → ⊢ modelStateInterp (GF := GF) es δ -∗ hasFuelsS ζ fs -∗
      ⌜ModelCanFuelStep δ ζ (modelUpdateLocaleFuel δ ζ (dom fs))⌝ := by
  intro Hfs
  unfold modelStateInterp hasFuelsS
  iintro ⟨%fm, %Hfmle, %Hfmdead, -, -, Hfm⟩ Hfs
  icombine Hfm Hfs gives %Hagree
  ipureintro
  exact can_fuel_step_pure fm δ ζ fs Hfs Hfmle Hfmdead Hagree

@[rocq_alias trillium.fairis.model_state_interp_fuel_update]
theorem model_state_interp_fuel_update (c1 c2 : List Expr × State) (δ : LiveState Locale M)
    (ζ : Locale) (fs : GMap M.fmrole Nat) :
    Language.LocaleStep c1 (some ζ) c2 →
    ⊢ modelStateInterp (GF := GF) c1.1 δ -∗ hasFuelsS ζ fs ==∗
      modelStateInterp c2.1 (modelUpdateLocaleFuel δ ζ (dom fs)) ∗ hasFuels ζ fs := by
  intro Hstep
  unfold modelStateInterp hasFuelsS
  rw [modelUpdateLocaleFuel_lsUnder]
  iintro ⟨%fm, %Hfmle, %Hfmdead, %Htp, Hm, Hfm⟩ Hfs
  icombine Hfm Hfs gives %Hagree
  imod has_fuels_update (fs' := fs) $$ Hfm Hfs with ⟨Hfm, Hfs⟩
  have P1 := fuel_map_le_fuel_step fm ζ fs δ Hagree Hfmle
  have P2 : fuelMapPreserveDead (fm.insert ζ fs) (M.liveRoles δ.lsUnder) :=
    fuel_map_preserve_dead_fuel_step fm ζ fs δ Hagree Hfmdead
  have P3 : fuelMapPreserveThreadpool c2.1 (fm.insert ζ fs) := by
    refine fuel_map_preserve_threadpool_fuel_step c1 ζ c2 fm _ ?_ Hstep Htp
    exact (dom_insert_of_mem (mem_of_getElem? Hagree)).symm
  imodintro
  iframe Hfs
  iexists fm.insert ζ fs
  iframe %P1 %P2 %P3 Hm Hfm

@[rocq_alias trillium.fairis.update_fuel_step]
theorem update_fuel_step (extr : ExecutionTrace Expr) (auxtr : AuxiliaryTrace LM.toModel)
    (c2 : List Expr × State) (fs : GMap M.fmrole Nat) (ζ : Locale) :
    fs ≠ ∅ → Language.LocaleStep extr.last (some ζ) c2 →
    ⊢ hasFuelsS (GF := GF) ζ fs -∗ modelStateInterp extr.last.1 auxtr.last ==∗
      ∃ δ2 : LiveState Locale M,
        ⌜validStateEvolutionFairness LM (extr.extend (some ζ) c2)
          (auxtr.extend (.silentStep ζ) δ2)⌝ ∗
        hasFuels ζ fs ∗ modelStateInterp c2.1 δ2 := by
  intro Hdom Hstep
  iintro Hfuel Hm
  ihave %Hcan : ⌜ModelCanFuelStep auxtr.last ζ (modelUpdateLocaleFuel auxtr.last ζ (dom fs))⌝
    $$ [Hm Hfuel]
  · iapply model_state_interp_can_fuel_step _ _ _ _ Hdom $$ Hm Hfuel
  imod model_state_interp_fuel_update _ _ _ _ _ Hstep $$ Hm Hfuel with ⟨Hm, Hfuel⟩
  ihave %Htids : ⌜tidsSmaller c2.1 (modelUpdateLocaleFuel auxtr.last ζ (dom fs))⌝ $$ [Hm]
  · iapply model_state_interp_tids_smaller $$ Hm
  imodintro
  iexists modelUpdateLocaleFuel auxtr.last ζ (dom fs)
  iframe Hfuel Hm
  ipureintro
  exact model_update_locale_spec extr auxtr ζ c2 (dom fs) Hcan Htids

end fuel_steps

/-! ## Model steps -/

section model_steps

variable {Locale : Type} [Ord Locale] [Std.TransOrd Locale] [Std.LawfulEqOrd Locale]
  [DecidableEq Locale]
variable {M : FairModel} {LM : LiveModel Locale M} {GF : BundledGFunctors}
variable {Expr Val Ectx State : Type _} [Language Expr Val Ectx State Locale]

theorem modelUpdateModelStep_lsMap (LM : LiveModel Locale M) (ζ : Locale) (ρs : GSet M.fmrole)
    (ρ : M.fmrole) (s2 : M.fmstate) (δ : LiveState Locale M) :
    (modelUpdateModelStep LM ζ ρs ρ s2 δ).lsMap =
      δ.lsMap.modify ζ fun fs => (modelUpdateLocaleRoleMap δ ρs fs).modify ρ fun _ => LM.lmFl s2 := by
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  simp only [modelUpdateModelStep, modelUpdateState, modelUpdateSet, modelUpdateDecr,
    modelUpdateFilter, getElem?_modify_ite]
  by_cases h : ζ = k
  · subst h; simp only [ite_true, Option.map_map]; rfl
  · simp [h]

open Classical in
theorem getElem?_singleton_union {K V : Type _} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]
    {a k : K} {b : V} {m : GMap K V} :
    (GMap.singleton a b ∪ m)[k]? = if a = k then (m[k]?).or (some b) else m[k]? := by
  rw [Std.ExtTreeMap.getElem?_union, getElem?_singleton]
  by_cases h : a = k <;> simp [h]

theorem mem_singleton_union {K V : Type _} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]
    {a k : K} {b : V} {m : GMap K V} : k ∈ GMap.singleton a b ∪ m ↔ k = a ∨ k ∈ m := by
  rw [mem_iff_getElem?, mem_iff_getElem?, getElem?_singleton_union]
  by_cases h : a = k
  · subst h; cases m[a]? <;> simp
  · simp [h, Ne.symm h]

/-- The facts about the fuel of `ρ` and of the roles of `fs` in the current live state, given
`ζ ↦M ({[ρ := f]} ∪ (S <$> fs))`. -/
theorem model_step_fuel_facts {ρ : M.fmrole} {f : Nat} {fs v2 : GMap M.fmrole Nat} (Hρ : ρ ∉ dom fs)
    (Hle : mapIncluded (fun _ (a b : Nat) => a ≤ b)
      (GMap.singleton ρ f ∪ fs.map fun _ f => f + 1) v2) :
    (∃ x, v2[ρ]? = some x) ∧
      ∀ (ρ' : M.fmrole) (g : Nat), fs[ρ']? = some g → ∃ x, v2[ρ']? = some x ∧ g + 1 ≤ x := by
  have Hρ' : fs[ρ]? = none := not_mem_iff.1 fun h => Hρ (mem_dom.2 h)
  constructor
  · obtain ⟨x, hx, -⟩ := (mapIncluded_spec _ _ _).1 Hle ρ f
      (by rw [getElem?_singleton_union]; simp [Hρ'])
    exact ⟨x, hx⟩
  · intro ρ' g hg
    have hne : ρ ≠ ρ' := by rintro rfl; rw [Hρ'] at hg; cases hg
    exact (mapIncluded_spec _ _ _).1 Hle ρ' (g + 1)
      (by rw [getElem?_singleton_union]; simp [hne, hg])

theorem roleMap_getElem? {δ : LiveState Locale M} {ρs : GSet M.fmrole} {v2 : GMap M.fmrole Nat}
    {ρ : M.fmrole} {x : Nat} (hx : v2[ρ]? = some x)
    (hc : ρ ∈ M.liveRoles δ.lsUnder ∨ ρ ∈ ρs) :
    (modelUpdateLocaleRoleMap δ ρs v2)[ρ]? = some (x - 1) := by
  simp only [modelUpdateLocaleRoleMap, Function.comp_apply, decrFuelMap, filterFuelMap,
    getElem?_map_eq, getElem?_filter_eq, hx]
  simp [Option.filter, hc]

theorem roleMap_getElem?_inv {δ : LiveState Locale M} {ρs : GSet M.fmrole}
    {v2 : GMap M.fmrole Nat} {ρ : M.fmrole} {y : Nat}
    (hy : (modelUpdateLocaleRoleMap δ ρs v2)[ρ]? = some y) :
    ∃ x, v2[ρ]? = some x ∧ y = x - 1 ∧ (ρ ∈ M.liveRoles δ.lsUnder ∨ ρ ∈ ρs) := by
  simp only [modelUpdateLocaleRoleMap, Function.comp_apply, decrFuelMap, filterFuelMap,
    getElem?_map_eq, getElem?_filter_eq] at hy
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hy
  obtain ⟨hx2, hcond⟩ := Option.filter_eq_some_iff.1 hx
  exact ⟨x, hx2, rfl, of_decide_eq_true hcond⟩

variable [fG : FairnessGS LM GF]

@[rocq_alias trillium.fairis.model_state_interp_model_step_update]
theorem model_state_interp_model_step_update (ρ : M.fmrole) (fs : GMap M.fmrole Nat)
    (tp1 tp2 : List Expr) (δ δ2 : LiveState Locale M) (ζ : Locale) (σ1 σ2 : State) (f1 : Nat)
    (s1 s2 : M.fmstate) :
    ρ ∉ dom fs → M.liveRoles s2 ⊆ M.liveRoles s1 →
    Language.LocaleStep (tp1, σ1) (some ζ) (tp2, σ2) → M.fmtrans s1 (some ρ) s2 →
    δ2.toLiveStateData = modelUpdateModelStep LM ζ ({ρ} ∪ dom fs) ρ s2 δ →
    ⊢ modelStateInterp (GF := GF) tp1 δ -∗
      hasFuels ζ (GMap.singleton ρ f1 ∪ fs.map fun _ f => f + 1) -∗
      fragModelIs s1 ==∗
      modelStateInterp tp2 δ2 ∗ hasFuels ζ (GMap.singleton ρ (LM.lmFl s2) ∪ fs) ∗
      fragModelIs s2 := by
  intro Hfs Hlive Hstep _Hmstep Hδ2
  have hU : δ2.lsUnder = s2 := congrArg LiveStateData.lsUnder Hδ2
  have hM := (congrArg LiveStateData.lsMap Hδ2).trans (modelUpdateModelStep_lsMap LM _ _ _ _ _)
  unfold modelStateInterp
  rw [hU]
  iintro ⟨%fm, %Hfmle, %Hfmdead, %Htp, Hm, Hfm⟩ Hf Hs
  icombine Hfm Hf gives %Hagree
  icombine Hm Hs gives %Heq
  imod has_fuels_update (fs' := GMap.singleton ρ (LM.lmFl s2) ∪ fs) $$ Hfm Hf with ⟨Hfm, Hf⟩
  imod update_model s2 $$ Hm Hs with ⟨Hm, Hs⟩
  obtain ⟨v2, HSome, Hle⟩ := fuelMapLeInner_spec.1 Hfmle.1 ζ _ Hagree
  obtain ⟨⟨x0, hx0⟩, Hfacts⟩ := model_step_fuel_facts Hfs Hle
  rw [alter_insert_alt _ _ _ _ HSome] at hM
  have Hρ' : fs[ρ]? = none := not_mem_iff.1 fun h => Hfs (mem_dom.2 h)
  have P1 : fuelMapLe (fm.insert ζ (GMap.singleton ρ (LM.lmFl s2) ∪ fs)) δ2.lsMap := by
    rw [hM]
    refine ⟨mapIncluded_insert _ _ _ _ _ _ ?_ Hfmle.1, dom_insert_insert _ _ _ Hfmle.2⟩
    rw [mapIncluded_spec]
    intro ρ' f Hf'
    rw [getElem?_singleton_union] at Hf'
    by_cases e : ρ = ρ'
    · subst e
      rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), Hρ'] at Hf'
      cases Hf'
      refine ⟨LM.lmFl s2, ?_, Nat.le_refl _⟩
      rw [getElem?_modify_ite, ite_eq_left_of_eq_true _ _ (eq_true rfl),
        roleMap_getElem? hx0 (.inr (mem_union.2 (.inl (LawfulSet.mem_singleton.2 rfl))))]
      rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false e)] at Hf'
      obtain ⟨x, hx, hle⟩ := Hfacts ρ' f Hf'
      refine ⟨x - 1, ?_, by omega⟩
      rw [getElem?_modify_ite, ite_eq_right_of_eq_false _ _ (eq_false e),
        roleMap_getElem? hx (.inr (mem_union.2 (.inr (mem_dom.2 (mem_of_getElem? Hf')))))]
  have P2 : fuelMapPreserveDead (fm.insert ζ (GMap.singleton ρ (LM.lmFl s2) ∪ fs))
      (M.liveRoles s2) := by
    refine preserveDead_insert Hagree (fun ρ' h => Heq ▸ Hlive ρ' h) (fun ρ' h _ => ?_) Hfmdead
    rw [mem_singleton_union] at h ⊢
    rcases h with h | h
    · exact .inl h
    · exact .inr (Std.ExtTreeMap.mem_map.1 h)
  have P3 : fuelMapPreserveThreadpool tp2 (fm.insert ζ (GMap.singleton ρ (LM.lmFl s2) ∪ fs)) := by
    refine preserveThreadpool_mono (locales_not_mem_of_step Hstep) (fun z hz => .inl ?_) Htp
    rcases mem_insert_eq.1 hz with rfl | h
    · exact mem_of_getElem? Hagree
    · exact h
  imodintro
  iframe Hf Hs
  iexists fm.insert ζ (GMap.singleton ρ (LM.lmFl s2) ∪ fs)
  iframe %P1 %P2 %P3 Hm Hfm

theorem can_model_step_pure (fm : GMap Locale (GMap M.fmrole Nat)) (δ δ2 : LiveState Locale M)
    (ζ : Locale) (ρ : M.fmrole) (f : Nat) (fs : GMap M.fmrole Nat) (s1 s2 : M.fmstate)
    (Hstep : M.fmtrans s1 (some ρ) s2) (Hle : M.liveRoles s2 ⊆ M.liveRoles s1) (Hρ : ρ ∉ dom fs)
    (Hδ2 : δ2.toLiveStateData = modelUpdateModelStep LM ζ ({ρ} ∪ dom fs) ρ s2 δ)
    (Hfmle : fuelMapLe fm δ.lsMap) (Hfmdead : fuelMapPreserveDead fm (M.liveRoles δ.lsUnder))
    (Heq : δ.lsUnder = s1)
    (Hagree : fm[ζ]? = some (GMap.singleton ρ f ∪ fs.map fun _ f => f + 1)) :
    ModelCanModelStep LM δ ζ ρ δ2 := by
  have hU : δ2.lsUnder = s2 := congrArg LiveStateData.lsUnder Hδ2
  have hM := (congrArg LiveStateData.lsMap Hδ2).trans (modelUpdateModelStep_lsMap LM _ _ _ _ _)
  obtain ⟨v2, HSome, Hfs'⟩ := fuelMapLeInner_spec.1 Hfmle.1 ζ _ Hagree
  obtain ⟨⟨x0, hx0⟩, Hfacts⟩ := model_step_fuel_facts Hρ Hfs'
  rw [alter_insert_alt _ _ _ _ HSome] at hM
  have Hρin : ρ ∈ ({ρ} ∪ dom fs : GSet M.fmrole) :=
    mem_union.2 (.inl (LawfulSet.mem_singleton.2 rfl))
  refine ⟨v2, (modelUpdateLocaleRoleMap δ ({ρ} ∪ dom fs) v2).modify ρ fun _ => LM.lmFl s2,
    by rw [Heq, hU]; exact Hstep, by rw [Heq, hU]; exact Hle, HSome, hM,
    mem_dom.2 (mem_of_getElem? hx0), ?_, ?_, ?_⟩
  · rw [getElem?_modify_ite, ite_eq_left_of_eq_true _ _ (eq_true rfl), roleMap_getElem? hx0 (.inr Hρin), hU]
    rfl
  · rw [mapIncluded_spec]
    intro ρ' y hy
    rw [getElem?_erase_ite] at hy
    by_cases e : ρ = ρ'
    · rw [ite_eq_left_of_eq_true _ _ (eq_true e)] at hy; cases hy
    rw [ite_eq_right_of_eq_false _ _ (eq_false e), getElem?_modify_ite, ite_eq_right_of_eq_false _ _ (eq_false e)] at hy
    obtain ⟨x, hx, rfl, hc⟩ := roleMap_getElem?_inv hy
    have hk : ρ' ∈ fs := by
      rcases hc with hl | hd
      · have := fuel_map_le_live_roles fm δ.lsMap (M.liveRoles δ.lsUnder) ζ _ v2 ρ'
          (mapInnerDisj_lsMap δ) Hfmle.1 Hfmdead Hagree HSome hl (mem_dom.2 (mem_of_getElem? hx))
        rw [mem_dom, mem_singleton_union] at this
        rcases this with h | h
        · exact absurd h.symm e
        · exact Std.ExtTreeMap.mem_map.1 h
      · rcases mem_union.1 hd with h | h
        · exact absurd (LawfulSet.mem_singleton.1 h).symm e
        · exact mem_dom.1 h
    obtain ⟨g, hg⟩ := mem_iff_exists.1 hk
    obtain ⟨x', hx', hle⟩ := Hfacts ρ' g hg
    rw [hx] at hx'
    cases hx'
    exact ⟨x, hx, by omega⟩
  · rw [LawfulSet.eq_empty_iff]
    intro k hk
    rw [mem_inter, mem_diff, mem_dom, mem_dom] at hk
    obtain ⟨⟨h1, h2⟩, h3⟩ := hk
    apply h2
    rw [Std.ExtTreeMap.mem_modify]
    simp only [modelUpdateLocaleRoleMap, Function.comp_apply]
    rw [mem_decrFuelMap, mem_filterFuelMap]
    exact ⟨h1, .inl h3⟩

@[rocq_alias trillium.fairis.model_state_interp_can_model_step]
theorem model_state_interp_can_model_step (es : List Expr) (δ δ2 : LiveState Locale M)
    (ζ : Locale) (ρ : M.fmrole) (f : Nat) (fs : GMap M.fmrole Nat) (s1 s2 : M.fmstate) :
    M.fmtrans s1 (some ρ) s2 → M.liveRoles s2 ⊆ M.liveRoles s1 → ρ ∉ dom fs →
    δ2.toLiveStateData = modelUpdateModelStep LM ζ ({ρ} ∪ dom fs) ρ s2 δ →
    ⊢ modelStateInterp (GF := GF) es δ -∗
      hasFuels ζ (GMap.singleton ρ f ∪ fs.map fun _ f => f + 1) -∗
      fragModelIs s1 -∗ ⌜ModelCanModelStep LM δ ζ ρ δ2⌝ := by
  intro Hstep Hle Hρ Hδ2
  unfold modelStateInterp
  iintro ⟨%fm, %Hfmle, %Hfmdead, -, Hm, Hfm⟩ Hf Hδ
  icombine Hm Hδ gives %Heq
  icombine Hfm Hf gives %Hagree
  ipureintro
  exact can_model_step_pure fm δ δ2 ζ ρ f fs s1 s2 Hstep Hle Hρ Hδ2 Hfmle Hfmdead Heq Hagree

@[rocq_alias trillium.fairis.model_update_locale_spec_model_step]
theorem model_update_locale_spec_model_step (extr : ExecutionTrace Expr)
    (auxtr : AuxiliaryTrace LM.toModel) (ζ : Locale) (c2 : List Expr × State)
    (ρs : GSet M.fmrole) (ρ : M.fmrole) (δ2 : LiveState Locale M) (s2 : M.fmstate) :
    δ2.toLiveStateData = modelUpdateModelStep LM ζ ({ρ} ∪ ρs) ρ s2 auxtr.last →
    ModelCanModelStep LM auxtr.last ζ ρ δ2 →
    tidsSmaller c2.1 δ2 →
    validStateEvolutionFairness LM (extr.extend (some ζ) c2) (auxtr.extend (.takeStep ρ ζ) δ2) := by
  intro _ Hstep Htids
  exact ⟨rfl, model_can_model_step_trans LM _ _ _ _ Hstep, Htids⟩

@[rocq_alias trillium.fairis.update_model_step]
theorem update_model_step (extr : ExecutionTrace Expr) (auxtr : AuxiliaryTrace LM.toModel)
    (c2 : List Expr × State) (s1 s2 : M.fmstate) (fs : GMap M.fmrole Nat) (ρ : M.fmrole)
    (δ1 : LiveState Locale M) (ζ : Locale) (f : Nat) :
    M.liveRoles s2 ⊆ M.liveRoles s1 → ρ ∉ dom fs → auxtr.last = δ1 →
    Language.LocaleStep extr.last (some ζ) c2 → M.fmtrans s1 (some ρ) s2 →
    ⊢ hasFuels (GF := GF) ζ (GMap.singleton ρ f ∪ fs.map fun _ f => f + 1) -∗
      fragModelIs s1 -∗ modelStateInterp extr.last.1 δ1 ==∗
      ∃ δ2 : LiveState Locale M,
        ⌜validStateEvolutionFairness LM (extr.extend (some ζ) c2)
          (auxtr.extend (.takeStep ρ ζ) δ2)⌝ ∗
        hasFuels ζ (GMap.singleton ρ (LM.lmFl s2) ∪ fs) ∗ fragModelIs s2 ∗
        modelStateInterp c2.1 δ2 := by
  intro Hlive Hdom Hlast Hstep Htrans
  iintro Hfuel Hfrag Hm
  ihave %Heq : ⌜δ1.lsUnder = s1⌝ $$ [Hm Hfrag]
  · iapply model_agree' $$ Hm Hfrag
  obtain ⟨δ2, Hδ2⟩ := model_update_model_step_valid LM ζ ({ρ} ∪ dom fs) ρ s2 δ1
    (Heq ▸ Hlive)
  ihave %Hcan : ⌜ModelCanModelStep LM δ1 ζ ρ δ2⌝ $$ [Hm Hfuel Hfrag]
  · iapply model_state_interp_can_model_step _ _ _ _ _ _ _ _ _ Htrans Hlive Hdom Hδ2 $$ Hm Hfuel
      Hfrag
  imod model_state_interp_model_step_update (tp1 := extr.last.1) (σ1 := extr.last.2)
    (tp2 := c2.1) (σ2 := c2.2) _ _ _ _ _ _ _ _ Hdom Hlive Hstep Htrans Hδ2
    $$ Hm Hfuel Hfrag with ⟨Hm, Hf, Hfrag⟩
  ihave %Htids : ⌜tidsSmaller c2.1 δ2⌝ $$ [Hm]
  · iapply model_state_interp_tids_smaller $$ Hm
  imodintro
  iexists δ2
  iframe Hm Hf Hfrag
  ipureintro
  subst Hlast
  exact model_update_locale_spec_model_step extr auxtr ζ c2 (dom fs) ρ δ2 s2 Hδ2 Hcan Htids

end model_steps

/-! ## Fork steps -/

section fork_steps

variable {Locale : Type} [Ord Locale] [Std.TransOrd Locale] [Std.LawfulEqOrd Locale]
  [DecidableEq Locale]
variable {M : FairModel} {LM : LiveModel Locale M} {GF : BundledGFunctors}
variable {Expr Val Ectx State : Type _} [Language Expr Val Ectx State Locale]

theorem insert_insert_eq {K V : Type _} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]
    (m : GMap K V) (k : K) (a b : V) : (m.insert k a).insert k b = m.insert k b := by
  apply Std.ExtTreeMap.ext_getElem?
  intro x
  simp only [getElem?_insert_ite]
  by_cases e : k = x <;> simp [e]

theorem insert_comm_ne {K V : Type _} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]
    (m : GMap K V) (k1 k2 : K) (a b : V) (h : k1 ≠ k2) :
    (m.insert k1 a).insert k2 b = (m.insert k2 b).insert k1 a := by
  apply Std.ExtTreeMap.ext_getElem?
  intro x
  simp only [getElem?_insert_ite]
  by_cases e1 : k1 = x <;> by_cases e2 : k2 = x
  · exact absurd (e1.trans e2.symm) h
  all_goals simp [e1, e2]

theorem modelUpdateFork_lsMap (ζ ζf : Locale) (ρs1 ρs2 : GSet M.fmrole)
    (δ : LiveState Locale M) (v : GMap M.fmrole Nat) (h : δ.lsMap[ζ]? = some v) :
    (modelUpdateFork ζ ζf ρs1 ρs2 δ).lsMap =
      (δ.lsMap.insert ζ ((modelUpdateLocaleRoleMap δ ρs1 v).filter
        fun ρ _ => decide (ρ ∉ ρs2))).insert ζf
        ((modelUpdateLocaleRoleMap δ ρs1 v).filter fun ρ _ => decide (ρ ∈ ρs2)) := by
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  simp only [modelUpdateFork, modelUpdateSplit, modelUpdateDecr, modelUpdateFilter,
    getElem?_insert_ite, getElem?_modify_ite, h, ite_true, Option.map_some, Option.getD_some]
  by_cases h1 : ζf = k
  · simp only [h1, ite_true]
    rfl
  · by_cases h2 : ζ = k
    · subst h2; simp [h1]; rfl
    · simp [h1, h2]

theorem getElem?_succ_union_of_right {fs1 fs2 : GMap M.fmrole Nat} {ρ : M.fmrole} {g : Nat}
    (h : fs2[ρ]? = some g) : ((fs1 ∪ fs2).map fun _ f => f + 1)[ρ]? = some (g + 1) := by
  rw [getElem?_succ_map, Std.ExtTreeMap.getElem?_union, h]
  rfl

theorem getElem?_succ_union_of_left {fs1 fs2 : GMap M.fmrole Nat} {ρ : M.fmrole} {g : Nat}
    (h : fs1[ρ]? = some g) (h' : fs2[ρ]? = none) :
    ((fs1 ∪ fs2).map fun _ f => f + 1)[ρ]? = some (g + 1) := by
  rw [getElem?_succ_map, Std.ExtTreeMap.getElem?_union, h', h]
  rfl

theorem mem_union_map {fs1 fs2 : GMap M.fmrole Nat} {ρ : M.fmrole} :
    ρ ∈ ((fs1 ∪ fs2).map fun _ f => f + 1) ↔ ρ ∈ fs1 ∨ ρ ∈ fs2 := by
  rw [Std.ExtTreeMap.mem_map, Std.ExtTreeMap.mem_union_iff]

variable [fG : FairnessGS LM GF]

@[rocq_alias trillium.fairis.model_state_interp_fork_update]
theorem model_state_interp_fork_update (fs1 fs2 : GMap M.fmrole Nat) (tp1 tp2 : List Expr)
    (δ1 δ2 : LiveState Locale M) (ζ : Locale) (efork : Expr) (σ1 σ2 : State) :
    δ2.toLiveStateData =
      modelUpdateFork ζ (localeOf tp1 efork) (dom fs1 ∪ dom fs2) (dom fs2) δ1 →
    fs1 ∪ fs2 ≠ ∅ → fs1 ##ₘ fs2 → HasForked tp1 tp2 efork →
    Language.LocaleStep (tp1, σ1) (some ζ) (tp2, σ2) →
    ⊢ modelStateInterp (GF := GF) tp1 δ1 -∗ hasFuelsS ζ (fs1 ∪ fs2) ==∗
      modelStateInterp tp2 δ2 ∗ hasFuels ζ fs1 ∗ hasFuels (localeOf tp1 efork) fs2 := by
  intro Hδ2 _Hfs Hdisj Hforked Hstep
  have HζfNot : localeOf tp1 efork ∉ localesOfList tp1 := not_elem_of_locale_of_from_list tp1 efork
  have HζfIn : localeOf tp1 efork ∈ localesOfList tp2 := by
    obtain ⟨tp1', rfl, Heqv⟩ := Hforked
    exact elem_of_locale_of_from_list _ _ _ Heqv
  generalize localeOf tp1 efork = ζf at Hδ2 HζfNot HζfIn ⊢
  have hU : δ2.lsUnder = δ1.lsUnder := by
    have := congrArg LiveStateData.lsUnder Hδ2; exact this
  unfold modelStateInterp hasFuelsS
  rw [hU]
  iintro ⟨%fm, %Hfmle, %Hfmdead, %Htp, Hm, Hfm⟩ Hf
  icombine Hfm Hf gives %Hagree
  have Hnone : fm[ζf]? = none := Htp ζf HζfNot
  have Hnin : ζf ∉ dom fm := fun h => (not_mem_iff.2 Hnone) (mem_dom.1 h)
  have Hneq : ζ ≠ ζf := fun h => Hnin (mem_dom.2 (h ▸ mem_of_getElem? Hagree))
  have Hnin' : ζf ∉ dom (fm.insert ζ (fs1 ∪ fs2)) := by
    rw [mem_dom, mem_insert_eq]
    rintro (h | h)
    · exact Hneq h
    · exact Hnin (mem_dom.2 h)
  imod has_fuels_update (fs' := fs1 ∪ fs2) $$ Hfm Hf with ⟨Hfm, Hf⟩
  imod has_fuels_split _ _ ζf fs1 fs2 Hnin' Hdisj $$ Hfm Hf with ⟨Hfm, Hf1, Hf2⟩
  obtain ⟨v2, HSome, Hle⟩ := fuelMapLeInner_spec.1 Hfmle.1 ζ _ Hagree
  have hM := (congrArg LiveStateData.lsMap Hδ2).trans (modelUpdateFork_lsMap _ _ _ _ _ _ HSome)
  have Hdisj' := disjoint_iff_mem.1 Hdisj
  -- the fuel of the roles of `fs1 ∪ fs2` in the live state
  have Hfacts : ∀ (ρ' : M.fmrole) (g : Nat), (fs1 ∪ fs2)[ρ']? = some g →
      (modelUpdateLocaleRoleMap δ1 (dom fs1 ∪ dom fs2) v2)[ρ']? ≠ none ∧
      ∀ x, v2[ρ']? = some x → g ≤ x - 1 := by
    intro ρ' g hg
    have hmem : ρ' ∈ fs1 ∪ fs2 := mem_of_getElem? hg
    obtain ⟨x, hx, hle⟩ := (mapIncluded_spec _ _ _).1 Hle ρ' (g + 1)
      (by rw [getElem?_succ_map, hg]; rfl)
    have hR : ρ' ∈ dom fs1 ∪ dom fs2 := by
      rw [mem_union, mem_dom, mem_dom]; exact Std.ExtTreeMap.mem_union_iff.1 hmem
    refine ⟨by rw [roleMap_getElem? hx (.inr hR)]; simp, fun x' hx' => ?_⟩
    rw [hx] at hx'; cases hx'; omega
  have P1 : fuelMapLe (((fm.insert ζ (fs1 ∪ fs2)).insert ζ fs1).insert ζf fs2) δ2.lsMap := by
    rw [insert_insert_eq, hM]
    refine ⟨mapIncluded_insert _ _ _ _ _ _ ?_ (mapIncluded_insert _ _ _ _ _ _ ?_ Hfmle.1),
      dom_insert_insert _ _ _ (dom_insert_insert _ _ _ Hfmle.2)⟩
    · rw [mapIncluded_spec]
      intro ρ' g hg
      have hg' : (fs1 ∪ fs2)[ρ']? = some g := by rw [Std.ExtTreeMap.getElem?_union, hg]; rfl
      obtain ⟨hw, hle⟩ := Hfacts ρ' g hg'
      obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 hw
      obtain ⟨x, hx, rfl, -⟩ := roleMap_getElem?_inv hy
      refine ⟨x - 1, ?_, hle x hx⟩
      rw [getElem?_filter_eq, hy]
      simp [Option.filter, mem_dom, mem_of_getElem? hg]
    · rw [mapIncluded_spec]
      intro ρ' g hg
      have h2 : fs2[ρ']? = none := not_mem_iff.1 (Hdisj' ρ' (mem_of_getElem? hg))
      have hg' : (fs1 ∪ fs2)[ρ']? = some g := by
        rw [Std.ExtTreeMap.getElem?_union, h2, hg]; rfl
      obtain ⟨hw, hle⟩ := Hfacts ρ' g hg'
      obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 hw
      obtain ⟨x, hx, rfl, -⟩ := roleMap_getElem?_inv hy
      refine ⟨x - 1, ?_, hle x hx⟩
      rw [getElem?_filter_eq, hy]
      simp [Option.filter, mem_dom, not_mem_iff.2 h2]
  have P2 : fuelMapPreserveDead (((fm.insert ζ (fs1 ∪ fs2)).insert ζ fs1).insert ζf fs2)
      (M.liveRoles δ1.lsUnder) := by
    rw [insert_insert_eq]
    intro ρ' hρ'
    obtain ⟨ζ', ρs, H, Hin⟩ := Hfmdead ρ' hρ'
    by_cases e : ζ = ζ'
    · subst e
      rw [Hagree] at H
      cases H
      rw [mem_dom, mem_union_map] at Hin
      by_cases h2 : ρ' ∈ fs2
      · exact ⟨ζf, fs2, by rw [getElem?_insert_ite]; simp, mem_dom.2 h2⟩
      · refine ⟨ζ, fs1, by rw [getElem?_insert_ite, getElem?_insert_ite]; simp [Ne.symm Hneq], ?_⟩
        rcases Hin with h | h
        · exact mem_dom.2 h
        · exact absurd h h2
    · have e' : ζf ≠ ζ' := by
        rintro rfl; rw [Hnone] at H; cases H
      exact ⟨ζ', ρs, by rw [getElem?_insert_ite, getElem?_insert_ite]; simp [e, e', H], Hin⟩
  have P3 : fuelMapPreserveThreadpool tp2
      (((fm.insert ζ (fs1 ∪ fs2)).insert ζ fs1).insert ζf fs2) := by
    refine preserveThreadpool_mono (locales_not_mem_of_step Hstep) (fun z hz => ?_) Htp
    rw [insert_insert_eq, mem_insert_eq, mem_insert_eq] at hz
    rcases hz with rfl | rfl | h
    · exact .inr HζfIn
    · exact .inl (mem_of_getElem? Hagree)
    · exact .inl h
  imodintro
  iframe Hf1 Hf2
  iexists ((fm.insert ζ (fs1 ∪ fs2)).insert ζ fs1).insert ζf fs2
  iframe %P1 %P2 %P3 Hm Hfm

theorem can_fork_step_pure (fm : GMap Locale (GMap M.fmrole Nat)) (δ1 δ2 : LiveState Locale M)
    (ζ ζf : Locale) (fs1 fs2 : GMap M.fmrole Nat)
    (Hδ2 : δ2.toLiveStateData = modelUpdateFork ζ ζf (dom fs1 ∪ dom fs2) (dom fs2) δ1)
    (Hne : fs1 ∪ fs2 ≠ ∅) (_Hdisj : fs1 ##ₘ fs2) (Hfmle : fuelMapLe fm δ1.lsMap)
    (Hfmdead : fuelMapPreserveDead fm (M.liveRoles δ1.lsUnder))
    (Hagree : fm[ζ]? = some ((fs1 ∪ fs2).map fun _ f => f + 1)) (Hnin : ζf ∉ dom fm) :
    ModelCanForkStep δ1 ζ ζf δ2 := by
  obtain ⟨v2, HSome, Hle⟩ := fuelMapLeInner_spec.1 Hfmle.1 ζ _ Hagree
  have hM := (congrArg LiveStateData.lsMap Hδ2).trans (modelUpdateFork_lsMap _ _ _ _ _ _ HSome)
  have Hnin1 : ζf ∉ dom δ1.lsMap := by rw [← Hfmle.2]; exact Hnin
  have Hneq : ζ ≠ ζf := fun h => Hnin1 (mem_dom.2 (h ▸ mem_of_getElem? HSome))
  set w := modelUpdateLocaleRoleMap δ1 (dom fs1 ∪ dom fs2) v2 with hw
  have Hw : ∀ (ρ' : M.fmrole) (y : Nat), w[ρ']? = some y → ∃ x, v2[ρ']? = some x ∧ y < x := by
    intro ρ' y hy
    obtain ⟨x, hx, rfl, hc⟩ := roleMap_getElem?_inv hy
    have hk : ρ' ∈ fs1 ∪ fs2 := by
      rcases hc with hl | hd
      · have := fuel_map_le_live_roles fm δ1.lsMap (M.liveRoles δ1.lsUnder) ζ _ v2 ρ'
          (mapInnerDisj_lsMap δ1) Hfmle.1 Hfmdead Hagree HSome hl
          (mem_dom.2 (mem_of_getElem? hx))
        rw [mem_dom, Std.ExtTreeMap.mem_map] at this
        exact this
      · rw [mem_union, mem_dom, mem_dom] at hd
        exact Std.ExtTreeMap.mem_union_iff.2 hd
    obtain ⟨g, hg⟩ := mem_iff_exists.1 hk
    obtain ⟨x', hx', hle⟩ := (mapIncluded_spec _ _ _).1 Hle ρ' (g + 1)
      (by rw [getElem?_succ_map, hg]; rfl)
    rw [hx] at hx'
    cases hx'
    exact ⟨x, hx, by omega⟩
  have Hfilter : ∀ (P : M.fmrole → Bool) (ρ' : M.fmrole) (y : Nat),
      (w.filter fun ρ _ => P ρ)[ρ']? = some y → w[ρ']? = some y := by
    intro P ρ' y h
    rw [getElem?_filter_eq] at h
    exact (Option.filter_eq_some_iff.1 h).1
  refine ⟨v2, w.filter fun ρ _ => decide (ρ ∉ dom fs2), w.filter fun ρ _ => decide (ρ ∈ dom fs2),
    (by have := congrArg LiveStateData.lsUnder Hδ2; exact this.symm), HSome, ?_, ?_, ?_, ?_, ?_,
    ?_, Hnin1⟩
  · rintro rfl
    apply Hne
    rw [eq_empty_iff]
    intro k
    apply not_mem_iff.1
    intro hk
    have := mapIncluded_subseteq_inv _ _ _ Hle k (Std.ExtTreeMap.mem_map.2 hk)
    exact Std.ExtTreeMap.not_mem_empty this
  · rw [hM]
    exact insert_comm_ne _ _ _ _ _ Hneq
  · rw [mapIncluded_spec]
    intro ρ' y hy
    exact Hw ρ' y (Hfilter _ ρ' y hy)
  · rw [mapIncluded_spec]
    intro ρ' y hy
    exact Hw ρ' y (Hfilter _ ρ' y hy)
  · rw [LawfulSet.eq_empty_iff]
    intro k hk
    rw [mem_inter, mem_diff, mem_union, mem_dom, mem_dom, mem_dom] at hk
    obtain ⟨⟨h1, h2⟩, h3⟩ := hk
    obtain ⟨x, hx⟩ := mem_iff_exists.1 h1
    have hwk := roleMap_getElem? (δ := δ1) (ρs := dom fs1 ∪ dom fs2) hx (.inl h3)
    apply h2
    by_cases h4 : k ∈ dom fs2
    · right
      rw [mem_iff_getElem?, getElem?_filter_eq, hwk]
      simp [Option.filter, h4]
    · left
      rw [mem_iff_getElem?, getElem?_filter_eq, hwk]
      simp [Option.filter, h4]
  · rw [LawfulSet.eq_empty_iff]
    intro k hk
    rw [mem_inter, mem_dom, mem_dom, mem_iff_getElem?, mem_iff_getElem?, getElem?_filter_eq,
      getElem?_filter_eq] at hk
    obtain ⟨h1, h2⟩ := hk
    cases h : w[k]? <;> simp_all [Option.filter]

@[rocq_alias trillium.fairis.model_state_interp_can_fork_step]
theorem model_state_interp_can_fork_step (es : List Expr) (δ1 δ2 : LiveState Locale M)
    (ζ : Locale) (fs1 fs2 : GMap M.fmrole Nat) (e : Expr) :
    δ2.toLiveStateData = modelUpdateFork ζ (localeOf es e) (dom fs1 ∪ dom fs2) (dom fs2) δ1 →
    fs1 ∪ fs2 ≠ ∅ → fs1 ##ₘ fs2 →
    ⊢ modelStateInterp (GF := GF) es δ1 -∗ hasFuelsS ζ (fs1 ∪ fs2) -∗
      ⌜ModelCanForkStep δ1 ζ (localeOf es e) δ2⌝ := by
  intro Hδ2 Hne Hdisj
  unfold modelStateInterp hasFuelsS
  iintro ⟨%fm, %Hfmle, %Hfmdead, %Htp, -, Hfm⟩ Hf
  icombine Hfm Hf gives %Hagree
  ipureintro
  have Hnin : localeOf es e ∉ dom fm :=
    fun h => (not_mem_iff.2 (Htp _ (not_elem_of_locale_of_from_list es e))) (mem_dom.1 h)
  exact can_fork_step_pure fm δ1 δ2 ζ _ fs1 fs2 Hδ2 Hne Hdisj Hfmle Hfmdead Hagree Hnin

@[rocq_alias trillium.fairis.model_update_locale_spec_fork]
theorem model_update_locale_spec_fork (extr : ExecutionTrace Expr)
    (auxtr : AuxiliaryTrace LM.toModel) (ζ ζf : Locale) (c2 : List Expr × State)
    (ρs1 ρs2 : GSet M.fmrole) (δ2 : LiveState Locale M) :
    δ2.toLiveStateData = modelUpdateFork ζ ζf ρs1 ρs2 auxtr.last →
    ModelCanForkStep auxtr.last ζ ζf δ2 →
    tidsSmaller c2.1 δ2 →
    validStateEvolutionFairness LM (extr.extend (some ζ) c2) (auxtr.extend (.silentStep ζ) δ2) := by
  intro _ Hstep Htids
  exact ⟨rfl, model_can_fork_step_trans _ _ _ _ _ Hstep, Htids⟩

@[rocq_alias trillium.fairis.update_fork_step]
theorem update_fork_step (fs1 fs2 : GMap M.fmrole Nat) (tp1 tp2 : List Expr)
    (extr : ExecutionTrace Expr) (auxtr : AuxiliaryTrace LM.toModel) (ζ : Locale)
    (efork : Expr) (σ1 σ2 : State) :
    fs1 ∪ fs2 ≠ ∅ → fs1 ##ₘ fs2 → extr.last = (tp1, σ1) →
    Language.LocaleStep (tp1, σ1) (some ζ) (tp2, σ2) → HasForked tp1 tp2 efork →
    ⊢ hasFuelsS (GF := GF) ζ (fs1 ∪ fs2) -∗ modelStateInterp tp1 auxtr.last ==∗
      ∃ δ2 : LiveState Locale M,
        ⌜validStateEvolutionFairness LM (extr.extend (some ζ) (tp2, σ2))
          (auxtr.extend (.silentStep ζ) δ2)⌝ ∗
        hasFuels ζ fs1 ∗ hasFuels (localeOf tp1 efork) fs2 ∗ modelStateInterp tp2 δ2 := by
  intro Hne Hdisj _Hlast Hstep Hforked
  iintro Hfuel Hm
  ihave %Hag : ⌜∃ fs', auxtr.last.lsMap[ζ]? = some fs' ∧
      mapIncluded (fun _ (a b : Nat) => a ≤ b) ((fs1 ∪ fs2).map fun _ f => f + 1) fs'⌝
    $$ [Hm Hfuel]
  · iunfold hasFuelsS at Hfuel
    iapply model_state_interp_has_fuels_agree $$ Hm Hfuel
  ihave %Hnin : ⌜localeOf tp1 efork ∉ dom auxtr.last.lsMap⌝ $$ [Hm]
  · iunfold modelStateInterp at Hm
    icases Hm with ⟨%fm, %Hfmle, -, %Htp, -, -⟩
    ipureintro
    rw [← Hfmle.2]
    exact fun h => (not_mem_iff.2 (Htp _ (not_elem_of_locale_of_from_list tp1 efork)))
      (mem_dom.1 h)
  obtain ⟨fs', HSome, -⟩ := Hag
  obtain ⟨δ2, Hδ⟩ := model_update_fork_valid ζ (localeOf tp1 efork) (dom fs1 ∪ dom fs2) (dom fs2)
    auxtr.last (mem_dom.2 (mem_of_getElem? HSome)) Hnin
  ihave %Hcan : ⌜ModelCanForkStep auxtr.last ζ (localeOf tp1 efork) δ2⌝ $$ [Hm Hfuel]
  · iapply model_state_interp_can_fork_step _ _ _ _ _ _ _ Hδ Hne Hdisj $$ Hm Hfuel
  imod model_state_interp_fork_update _ _ _ _ _ _ _ _ _ _ Hδ Hne Hdisj Hforked Hstep $$ Hm Hfuel
    with ⟨Hm, Hf1, Hf2⟩
  ihave %Htids : ⌜tidsSmaller tp2 δ2⌝ $$ [Hm]
  · iapply model_state_interp_tids_smaller $$ Hm
  imodintro
  iexists δ2
  iframe Hm Hf1 Hf2
  ipureintro
  exact model_update_locale_spec_fork extr auxtr ζ _ (tp2, σ2) _ _ δ2 Hδ Hcan Htids

end fork_steps

end Trillium.Fairis
