/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.Fairis.Fuel
import Trillium.Prelude.Finitary

/-!
# Finite branching of live models
Port of `fairis/fairness_finiteness.v`.

If the relation `ξ` on model traces is finitely branching (`RelFinitary ξ`), then so is the
lifting of `ξ` to live models (`valid_state_evolution_finitary_fairness`): the possible next
live states are enumerated explicitly (`enumerateNext`), bounding the fuel by the maximal fuel of
the previous state and the fuel limit.

Representation decisions:
* stdpp's `Finite` is Mathlib's `Finite` (see `Trillium.Prelude.Finitary`); the enumeration
  `enum` of a finite type is obtained with `Fintype.ofFinite` (so `enumInner` is noncomputable).
  The `ProofIrrel` and `EqDecision` section hypotheses of Rocq are dropped (proof irrelevance is
  definitional in Lean, and decidability is classical).
* Rocq's list monad (`≫=`, `mret`) is `List.flatMap` and singleton lists; the common shape of
  `enumerate_next` and `enumerate_next_simple` is the helper `enumerateNextFrom`.
* Rocq's `max_gmap`/`max_gmap_spec` (duplicates of `fairness/utils_maps.v`) are
  `Trillium.Fairness.maxGMap`/`maxGMap_spec`.
-/

set_option linter.unusedSectionVars false

namespace Trillium.Fairis

open Trillium Trillium.Fairness Trace GMap

attribute [rocq_alias trillium.fairis.max_gmap] Trillium.Fairness.maxGMap
attribute [rocq_alias trillium.fairis.max_gmap_spec] Trillium.Fairness.maxGMap_spec

#rocq_ignore trillium.fairis.eq_dec_next_states
  "decidable equality only needed by stdpp's `Finite`; Lean's `Finite`/`Fintype.ofFinite` do not need it"

/-! ## Underlying model traces -/

/-- Map the states and labels of a finite trace (Rocq `trace_map`). -/
@[rocq_alias trillium.fairis.trace_map]
def traceMap {A A' L L' : Type _} (sf : A → A') (lf : L → L') :
    FiniteTrace A L → FiniteTrace A' L'
  | .singleton x => .singleton (sf x)
  | .extend tr' ℓ x => .extend (traceMap sf lf tr') (lf ℓ) (sf x)

section underlying

variable {Locale : Type _} [Ord Locale] [Std.TransOrd Locale] [Std.LawfulEqOrd Locale]

/-- The model trace underlying an auxiliary trace, keeping only the model steps (Rocq
`get_underlying_fairness_trace`). -/
@[rocq_alias trillium.fairis.get_underlying_fairness_trace]
def getUnderlyingFairnessTrace (M : FairModel) (LM : LiveModel Locale M) :
    AuxiliaryTrace LM.toModel → FiniteTrace M.fmstate M.fmrole
  | .singleton δ => .singleton δ.lsUnder
  | .extend ex' (.takeStep ρ _) δ => .extend (getUnderlyingFairnessTrace M LM ex') ρ δ.lsUnder
  | .extend ex' _ _ => getUnderlyingFairnessTrace M LM ex'

/-- The role of a model step (Rocq `get_role`). -/
@[rocq_alias trillium.fairis.get_role]
def getRole {Role : Type _} (lab : FairLabel Role Locale) : Option Role :=
  match lab with
  | .takeStep ρ _ => some ρ
  | _ => none

/-- The trace of underlying model states, labelled by the roles of model steps (Rocq
`map_underlying_trace`). -/
@[rocq_alias trillium.fairis.map_underlying_trace]
def mapUnderlyingTrace {M : FairModel} {LM : LiveModel Locale M}
    (aux : AuxiliaryTrace LM.toModel) : FiniteTrace M.fmstate (Option M.fmrole) :=
  traceMap (fun s : LiveState Locale M => s.lsUnder) (fun lab => getRole lab) aux

/-- Turn the data of a live state into a live state, if it satisfies the invariants (Rocq
`to_ls`). -/
@[rocq_alias trillium.fairis.condition_1_decision]
noncomputable def condition1Decision {M : FairModel} (x : LiveStateData Locale M) :
    Decidable (∀ (ζ ζ' : Locale) (fs fs' : GMap M.fmrole Nat), ζ ≠ ζ' →
      x.lsMap[ζ]? = some fs → x.lsMap[ζ']? = some fs' → fs ##ₘ fs') :=
  Classical.dec _

open Classical in
/-- Turn the data of a live state into a live state, if it satisfies the invariants (Rocq
`to_ls`). -/
@[rocq_alias trillium.fairis.to_ls]
noncomputable def toLs {M : FairModel} (x : LiveStateData Locale M) :
    Option (LiveState Locale M) :=
  if Hdisj : ∀ (ζ ζ' : Locale) (fs fs' : GMap M.fmrole Nat), ζ ≠ ζ' →
      x.lsMap[ζ]? = some fs → x.lsMap[ζ']? = some fs' → fs ##ₘ fs' then
    if Hlive : ∀ ρ, ρ ∈ M.liveRoles x.lsUnder →
        ∃ (ζ : Locale) (fs : GMap M.fmrole Nat), x.lsMap[ζ]? = some fs ∧ ρ ∈ dom fs then
      some ⟨x, Hdisj, Hlive⟩
    else none
  else none

theorem toLs_toLiveStateData {M : FairModel} (δ : LiveState Locale M) :
    toLs δ.toLiveStateData = some δ := by
  unfold toLs
  split
  · split
    · rfl
    · rename_i h; exact absurd δ.ls_map_live h
  · rename_i h; exact absurd δ.ls_map_disj h

end underlying

/-! ## Enumerating the next live states -/

section enumerate

variable {Locale : Type _} [Ord Locale] [Std.TransOrd Locale] [Std.LawfulEqOrd Locale]
  [DecidableEq Locale]
variable {M : FairModel} {LM : LiveModel Locale M}
variable {Expr Val Ectx State : Type _} [Language Expr Val Ectx State Locale]

variable (LM) in
/-- The candidate next live states, given the last live state `δ1` and candidate next model
states and roles `cands`: the common part of Rocq's `enumerate_next` and
`enumerate_next_simple`. -/
def enumerateNextFrom (δ1 : LiveState Locale M) (cands : List (M.fmstate × Option M.fmrole))
    (c' : List Expr × State) (oζ : Option Locale) :
    List (LiveStateData Locale M × FairLabel M.fmrole Locale) :=
  cands.flatMap fun p =>
    (enumerateDomGsets' (dom (lsFuel (δ1 : LiveStateData Locale M)) ∪ M.liveRoles p.1)).flatMap
      fun d =>
        let fss := enumerateSubdomainGmap d
          (max (maxGMap (lsFuel (δ1 : LiveStateData Locale M))) (LM.lmFl p.1))
        (enumerateDomGsets' (Iris.Std.LawfulSet.ofList (localesOfList c'.1) : GSet Locale)).flatMap
          fun locs =>
            (enumGmapRangeBounded' locs fss).flatMap fun ms =>
              let ℓ' : FairLabel M.fmrole Locale :=
                match p.2 with
                | none => match oζ with
                  | some ζ => .silentStep ζ
                  | none => .configStep
                | some ℓ => match oζ with
                  | none => .configStep
                  | some ζ => .takeStep ℓ ζ
              [({ lsUnder := p.1, lsMap := ms.1 }, ℓ')]

/-- The main membership lemma: a live-model step from `δ1` whose underlying model step is a
candidate is enumerated. -/
theorem mem_enumerateNextFrom (δ1 δ' : LiveState Locale M) (ℓ : FairLabel M.fmrole Locale)
    (cands : List (M.fmstate × Option M.fmrole)) (c' : List Expr × State) (oζ : Option Locale)
    (Hlbl : labelsMatch oζ ℓ) (Htrans : LM.lmLsTrans δ1 ℓ δ') (Htids : tidsSmaller c'.1 δ')
    (Hcand : (δ'.lsUnder, getRole ℓ) ∈ cands) :
    (δ'.toLiveStateData, ℓ) ∈ enumerateNextFrom LM δ1 cands c' oζ := by
  simp only [enumerateNextFrom, List.mem_flatMap, List.mem_singleton]
  refine ⟨_, Hcand, dom (lsFuel (δ' : LiveStateData Locale M)), ?_,
    dom δ'.lsMap, ?_, ⟨δ'.lsMap, fun k => mem_dom.symm⟩, ?_, ?_⟩
  · -- the domain of the new fuel
    apply enumerateDomGsets'_spec
    intro ρ Hρ
    rw [Iris.Std.mem_union]
    cases ℓ with
    | takeStep ρ0 tid =>
      by_cases h : ρ ∈ dom (lsFuel (δ1 : LiveStateData Locale M))
      · exact .inl h
      · right
        have := Htrans.2.2.2.2.2.2 ρ (Iris.Std.mem_diff.2 ⟨Hρ, h⟩)
        exact (Iris.Std.mem_diff.1 this).1
    | silentStep tid => exact .inl (Htrans.2.2.2.1 ρ Hρ)
    | configStep => exact Htrans.2.2.2.2.elim
  · -- the locales are threads of the configuration
    apply enumerateDomGsets'_spec
    intro ζ Hζ
    rw [← Iris.Std.LawfulSet.mem_ofList]
    exact mem_localesOfListFrom_of_fromLocaleFrom (Htids ζ Hζ)
  · -- the fuel maps are enumerated
    apply enumGmapRangeBounded'_spec
    refine ⟨fun k => mem_dom.symm, fun ζ fs Hlk => ?_⟩
    apply enumerateSubdomainGmap_spec
    · intro ρ Hρ
      exact ls_fuel_dom_data ρ δ' ζ fs Hlk (mem_dom.2 Hρ)
    intro ρ f Hlk'
    have Hsome : (lsFuel (δ' : LiveStateData Locale M))[ρ]? = some f :=
      ls_fuel_data ρ δ' ζ fs f Hlk Hlk'
    have Hdom' : ρ ∈ dom (lsFuel (δ' : LiveStateData Locale M)) :=
      mem_dom_iff.2 ⟨f, Hsome⟩
    -- the fuel is bounded by the previous fuel
    have Hold : ∀ f', (lsFuel (δ1 : LiveStateData Locale M))[ρ]? = some f' → f ≤ f' →
        f ≤ max (maxGMap (lsFuel (δ1 : LiveStateData Locale M))) (LM.lmFl δ'.lsUnder) :=
      fun f' Hf' Hle => le_max_of_le_left (Nat.le_trans Hle (maxGMap_spec _ ρ f' Hf'))
    cases ℓ with
    | takeStep ρ' tid =>
      obtain ⟨-, -, -, Hleq', Hlim, Hnew, -⟩ := Htrans
      by_cases Hρ : ρ = ρ'
      · subst Hρ
        rw [Hsome] at Hlim
        exact le_max_of_le_right Hlim
      · by_cases Hin : ρ ∈ dom (lsFuel (δ1 : LiveStateData Locale M))
        · rcases Hleq' ρ Hin (fun h => Hρ (Option.some.inj h)) with Hok | ⟨Hok, -⟩
          · obtain ⟨f', Hf'⟩ := mem_dom_iff.1 Hin
            rw [Hsome, Hf'] at Hok
            exact Hold f' Hf' Hok
          · exact absurd Hdom' Hok
        · have := Hnew ρ (Iris.Std.mem_diff.2 ⟨Hdom', Hin⟩)
          rw [Hsome] at this
          exact le_max_of_le_right this
    | silentStep tid =>
      obtain ⟨-, -, Hleq, Hincl, -⟩ := Htrans
      have Hin := Hincl ρ Hdom'
      rcases Hleq ρ Hin (by simp) with Hok | ⟨Hok, -⟩
      · obtain ⟨f', Hf'⟩ := mem_dom_iff.1 Hin
        rw [Hsome, Hf'] at Hok
        exact Hold f' Hf' Hok
      · exact absurd Hdom' Hok
    | configStep => exact Htrans.2.2.2.2.elim
  · -- the label
    refine Prod.ext rfl ?_
    cases ℓ with
    | takeStep ρ tid =>
      cases oζ with
      | none => exact Hlbl.elim
      | some ζ => obtain rfl : ζ = tid := Hlbl; rfl
    | silentStep tid =>
      cases oζ with
      | none => exact Hlbl.elim
      | some ζ => obtain rfl : ζ = tid := Hlbl; rfl
    | configStep =>
      cases oζ with
      | none => rfl
      | some ζ => exact Hlbl.elim

/-- Membership in the valid next live states, from membership of the data. -/
theorem mem_filterMap_toLs (l : List (LiveStateData Locale M × FairLabel M.fmrole Locale))
    (δ' : LiveState Locale M) (ℓ : FairLabel M.fmrole Locale)
    (H : (δ'.toLiveStateData, ℓ) ∈ l) :
    (δ', ℓ) ∈ l.filterMap (fun p => (toLs p.1).map fun x => (x, p.2)) := by
  rw [List.mem_filterMap]
  exact ⟨_, H, by simp [toLs_toLiveStateData]⟩

section finitary

variable (ξ : ExecutionTrace Expr → FiniteTrace M.fmstate (Option M.fmrole) → Prop)
variable (model_finitary : RelFinitary ξ)

include model_finitary in
@[rocq_alias trillium.fairis.model_finite]
theorem model_finite (ex : ExecutionTrace Expr) (atr : FiniteTrace M.fmstate (Option M.fmrole))
    (c' : List Expr × State) (oζ : Option Locale) :
    Finite {p : M.fmstate × Option M.fmrole // ξ (ex :tr[oζ]: c') (atr :tr[p.2]: p.1)} :=
  smaller_card_nat_finite (model_finitary ex atr c' oζ)

/-- An enumeration of the next model states and roles allowed by `ξ` (Rocq `enum_inner`). -/
@[rocq_alias trillium.fairis.enum_inner]
noncomputable def enumInner (ex : ExecutionTrace Expr)
    (fmodtr : FiniteTrace M.fmstate (Option M.fmrole)) (c' : List Expr × State)
    (oζ : Option Locale) : List (M.fmstate × Option M.fmrole) :=
  haveI := model_finite ξ model_finitary ex fmodtr c' oζ
  haveI := Fintype.ofFinite
    {p : M.fmstate × Option M.fmrole // ξ (ex :tr[oζ]: c') (fmodtr :tr[p.2]: p.1)}
  (Finset.univ : Finset {p : M.fmstate × Option M.fmrole //
    ξ (ex :tr[oζ]: c') (fmodtr :tr[p.2]: p.1)}).toList.map Subtype.val

include model_finitary in
@[rocq_alias trillium.fairis.enum_inner_spec]
theorem enum_inner_spec (δ' : M.fmstate) (ℓ : Option M.fmrole) (extr : ExecutionTrace Expr)
    (atr : FiniteTrace M.fmstate (Option M.fmrole)) (c' : List Expr × State)
    (oζ : Option Locale) :
    ξ (extr :tr[oζ]: c') (atr :tr[ℓ]: δ') → (δ', ℓ) ∈ enumInner ξ model_finitary extr atr c' oζ := by
  intro Hxi
  simp only [enumInner, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
  exact ⟨⟨(δ', ℓ), Hxi⟩, rfl⟩

variable (LM) in
/-- The candidate next live states (Rocq `enumerate_next`). -/
@[rocq_alias trillium.fairis.enumerate_next]
noncomputable def enumerateNext (extr : ExecutionTrace Expr) (fmodtr : AuxiliaryTrace LM.toModel)
    (c' : List Expr × State) (oζ : Option Locale) :
    List (LiveStateData Locale M × FairLabel M.fmrole Locale) :=
  let δ1 : LiveState Locale M := fmodtr.last
  enumerateNextFrom LM δ1
    ((δ1.lsUnder, none) :: enumInner ξ model_finitary extr (mapUnderlyingTrace fmodtr) c' oζ) c' oζ

variable (LM) in
/-- The valid candidate next live states (Rocq `enumerate_next_valid`). -/
@[rocq_alias trillium.fairis.enumerate_next_valid]
noncomputable def enumerateNextValid (extr : ExecutionTrace Expr)
    (fmodtr : AuxiliaryTrace LM.toModel) (c' : List Expr × State) (oζ : Option Locale) :
    List (LiveState Locale M × FairLabel M.fmrole Locale) :=
  (enumerateNext LM ξ model_finitary extr fmodtr c' oζ).filterMap
    fun p => (toLs p.1).map fun x => (x, p.2)

include model_finitary in
@[rocq_alias trillium.fairis.valid_state_evolution_finitary_fairness]
theorem valid_state_evolution_finitary_fairness
    (φ : ExecutionTrace Expr → AuxiliaryTrace LM.toModel → Prop) :
    RelFinitary (validLiftFairness LM
      (fun extr auxtr => ξ extr (mapUnderlyingTrace auxtr) ∧ φ extr auxtr)) := by
  intro ex atr c' oζ
  apply finite_smaller_card_nat
  refine in_list_finite (enumerateNextValid LM ξ model_finitary ex atr c' oζ) ?_
  rintro ⟨δ', ℓ⟩ ⟨⟨Hlbl, Htrans, Htids⟩, Hξ, -⟩
  refine mem_filterMap_toLs _ δ' ℓ (mem_enumerateNextFrom _ δ' ℓ _ c' oζ Hlbl Htrans Htids ?_)
  cases ℓ with
  | silentStep tid =>
    exact List.mem_cons.2 (.inl (by rw [Htrans.2.2.2.2]; rfl))
  | takeStep ρ tid =>
    exact List.mem_cons_of_mem _ (enum_inner_spec ξ model_finitary _ _ ex _ c' oζ Hξ)
  | configStep =>
    exact List.mem_cons_of_mem _ (enum_inner_spec ξ model_finitary _ _ ex _ c' oζ Hξ)

end finitary

section finitary_simple

variable (model_finitary : ∀ s1 : M.fmstate,
  Finite {p : M.fmstate × Option M.fmrole // M.fmtrans s1 p.2 p.1})

/-- An enumeration of the model steps from `s1` (Rocq `enum_inner_simple`). -/
@[rocq_alias trillium.fairis.enum_inner_simple]
noncomputable def enumInnerSimple (s1 : M.fmstate) : List (M.fmstate × Option M.fmrole) :=
  haveI := model_finitary s1
  haveI := Fintype.ofFinite {p : M.fmstate × Option M.fmrole // M.fmtrans s1 p.2 p.1}
  (Finset.univ : Finset {p : M.fmstate × Option M.fmrole // M.fmtrans s1 p.2 p.1}).toList.map
    Subtype.val

include model_finitary in
@[rocq_alias trillium.fairis.enum_inner_spec_simple]
theorem enum_inner_spec_simple (s1 s2 : M.fmstate) (ℓ : Option M.fmrole) :
    M.fmtrans s1 ℓ s2 → (s2, ℓ) ∈ enumInnerSimple model_finitary s1 := by
  intro Ht
  simp only [enumInnerSimple, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
  exact ⟨⟨(s2, ℓ), Ht⟩, rfl⟩

variable (LM) in
/-- The candidate next live states (Rocq `enumerate_next_simple`). -/
@[rocq_alias trillium.fairis.enumerate_next_simple]
noncomputable def enumerateNextSimple (fmodtr : AuxiliaryTrace LM.toModel)
    (c' : List Expr × State) (oζ : Option Locale) :
    List (LiveStateData Locale M × FairLabel M.fmrole Locale) :=
  let δ1 : LiveState Locale M := fmodtr.last
  enumerateNextFrom LM δ1 ((δ1.lsUnder, none) :: enumInnerSimple model_finitary δ1.lsUnder) c' oζ

variable (LM) in
/-- The valid candidate next live states (Rocq `enumerate_next_valid_simple`). -/
@[rocq_alias trillium.fairis.enumerate_next_valid_simple]
noncomputable def enumerateNextValidSimple (fmodtr : AuxiliaryTrace LM.toModel)
    (c' : List Expr × State) (oζ : Option Locale) :
    List (LiveState Locale M × FairLabel M.fmrole Locale) :=
  (enumerateNextSimple LM model_finitary fmodtr c' oζ).filterMap fun p => (toLs p.1).map fun x => (x, p.2)

include model_finitary in
@[rocq_alias trillium.fairis.valid_state_evolution_finitary_fairness_simple]
theorem valid_state_evolution_finitary_fairness_simple
    (φ : ExecutionTrace Expr → AuxiliaryTrace LM.toModel → Prop) :
    RelFinitary (validLiftFairness LM φ) := by
  intro ex atr c' oζ
  apply finite_smaller_card_nat
  refine in_list_finite (enumerateNextValidSimple LM model_finitary atr c' oζ) ?_
  rintro ⟨δ', ℓ⟩ ⟨⟨Hlbl, Htrans, Htids⟩, -⟩
  refine mem_filterMap_toLs _ δ' ℓ (mem_enumerateNextFrom _ δ' ℓ _ c' oζ Hlbl Htrans Htids ?_)
  cases ℓ with
  | silentStep tid =>
    exact List.mem_cons.2 (.inl (by rw [Htrans.2.2.2.2]; rfl))
  | takeStep ρ tid =>
    exact List.mem_cons_of_mem _ (enum_inner_spec_simple model_finitary _ _ _ Htrans.1)
  | configStep =>
    exact List.mem_cons_of_mem _ (enum_inner_spec_simple model_finitary _ _ _ Htrans.1)

end finitary_simple

end enumerate

/-! ## Simulation relations -/

section sim_rel

variable {Locale : Type _} [Ord Locale] [Std.TransOrd Locale] [Std.LawfulEqOrd Locale]
  [DecidableEq Locale]
variable {M : FairModel}
variable {Expr Val Ectx State : Type _} [Language Expr Val Ectx State Locale]

/-- Rocq `live_rel`. -/
@[rocq_alias trillium.fairis.live_rel]
def liveRel (LM : LiveModel Locale M) (ex : ExecutionTrace Expr)
    (aux : AuxiliaryTrace LM.toModel) : Prop :=
  liveTids (M := M) ex.last aux.last

/-- Rocq `sim_rel`. -/
@[rocq_alias trillium.fairis.sim_rel]
def simRel (LM : LiveModel Locale M) (ex : ExecutionTrace Expr)
    (aux : AuxiliaryTrace LM.toModel) : Prop :=
  validStateEvolutionFairness LM ex aux ∧ liveRel LM ex aux

/-- Rocq `sim_rel_with_user`. -/
@[rocq_alias trillium.fairis.sim_rel_with_user]
def simRelWithUser (LM : LiveModel Locale M)
    (ξ : ExecutionTrace Expr → FiniteTrace M.fmstate (Option M.fmrole) → Prop)
    (ex : ExecutionTrace Expr) (aux : AuxiliaryTrace LM.toModel) : Prop :=
  simRel LM ex aux ∧ ξ ex (mapUnderlyingTrace aux)

@[rocq_alias trillium.fairis.valid_lift_fairness_sim_rel_with_user]
theorem valid_lift_fairness_sim_rel_with_user {LM : LiveModel Locale M}
    (ξ : ExecutionTrace Expr → FiniteTrace M.fmstate (Option M.fmrole) → Prop)
    (extr : ExecutionTrace Expr) (atr : AuxiliaryTrace LM.toModel) :
    validLiftFairness LM (fun extr auxtr => ξ extr (mapUnderlyingTrace auxtr) ∧
      liveRel LM extr auxtr) extr atr ↔ simRelWithUser LM ξ extr atr :=
  ⟨fun ⟨Hvalid, Hξ, Hlive⟩ => ⟨⟨Hvalid, Hlive⟩, Hξ⟩,
    fun ⟨⟨Hvalid, Hlive⟩, Hξ⟩ => ⟨Hvalid, Hξ, Hlive⟩⟩

@[rocq_alias trillium.fairis.rel_finitary_sim_rel_with_user_ξ]
theorem rel_finitary_sim_rel_with_user_ξ {LM : LiveModel Locale M}
    (ξ : ExecutionTrace Expr → FiniteTrace M.fmstate (Option M.fmrole) → Prop) :
    RelFinitary ξ → RelFinitary (simRelWithUser LM ξ) := by
  intro Hrel
  refine RelFinitary.of_imp (fun ex aux H => (valid_lift_fairness_sim_rel_with_user ξ ex aux).2 H) ?_
  exact valid_state_evolution_finitary_fairness ξ Hrel _

/-- Rocq's `EqDecision` assumptions on the states and labels are not needed. -/
@[rocq_alias trillium.fairis.rel_finitary_sim_rel_with_user_sim_rel]
theorem rel_finitary_sim_rel_with_user_sim_rel {LM : LiveModel Locale M}
    (ξ : ExecutionTrace Expr → FiniteTrace M.fmstate (Option M.fmrole) → Prop) :
    RelFinitary (simRel (Expr := Expr) LM) → RelFinitary (simRelWithUser LM ξ) :=
  RelFinitary.of_imp fun _ _ H => H.1

end sim_rel

end Trillium.Fairis
