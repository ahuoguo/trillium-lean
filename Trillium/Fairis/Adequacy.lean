/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.Fairis.FuelTermination
import Trillium.Fairis.FairnessFiniteness
import Trillium.Fairis.HeapLangLM
import Trillium.HeapLang.HeapLangDefsPosts
import Trillium.HeapLang.LocalesHelpersHL

/-!
# Adequacy of Fairis for HeapLang
Port of `fairis/adequacy.v`.

A Fairis weakest-precondition proof of a HeapLang program `e1` against a live model `LM` gives a
continued simulation between the executions of `e1` and the traces of `LM`
(`strong_simulation_adequacy`, `simulation_adequacy`). If the underlying fair model is fairly
terminating, every fair execution of `e1` terminates (`simulation_adequacy_terminate`,
`simulation_adequacy_terminate_ftm`).

## Representation

* Rocq's `Σ` with `heapGpreS Σ LM` is `GF` with `[HeapGpreS LM GF]`; the hypothesis
  `∀ `{!heapGS Σ LM}, …` is `∀ [HeapGS LM GF], …`.
* The Rocq points-to `pointsto l (DfracOwn 1) v` is iris-lean's `l ↦ v`.
* stdpp's `gset_to_gmap f X` is `GSet.toGMap f X`, `X ∖ Y` is `X \ Y`.
-/

namespace Trillium.Fairis

open Iris Iris.BI Iris.Std Iris.ProofMode
open Trillium Trillium.Fairness Trillium.HeapLang
open Iris.HeapLang (Loc HeapF)

/-- Rocq `heap_lang_continued_simulation_fair_termination`: `continued_simulation_fair_termination`
for HeapLang, which has no configuration steps. -/
@[rocq_alias trillium.fairis.heap_lang_continued_simulation_fair_termination]
theorem heap_lang_continued_simulation_fair_termination {FM : FairModel}
    [FairTerminatingModel FM] {LM : LiveModel BaseLocale FM}
    (ξ : ExecutionTrace Expr → FiniteTrace FM.fmstate (Option FM.fmrole) → Prop)
    (a1 : FM.fmstate) (r1 : BaseLocale) (extr : Extrace Expr) :
    ContinuedSimulation (simRelWithUser LM ξ) ({tr[extr.first]} : ExecutionTrace Expr)
      ({tr[initialLs LM a1 r1]} : AuxiliaryTrace LM.toModel) →
    ExtraceFairlyTerminating extr := by
  apply continued_simulation_fair_termination
  · intro c c' contra
    cases contra with
    | state _ h => exact h
  · exact fun _ _ H => H.1.2
  · exact fun _ _ H => H.1.1

section adequacy

theorem initialLs_lsMap {M : FairModel} (LM : LiveModel BaseLocale M) (s0 : M.fmstate)
    (ζ0 : BaseLocale) :
    (initialLs LM s0 ζ0).lsMap = GMap.singleton ζ0 (GSet.toGMap (LM.lmFl s0) (M.liveRoles s0)) :=
  rfl

variable (GF : BundledGFunctors) {M : FairModel} (LM : LiveModel BaseLocale M)

@[rocq_alias trillium.fairis.strong_simulation_adequacy]
theorem strong_simulation_adequacy [HeapGpreS LM GF] (s : Stuckness) (e1 : Expr) (σ1 : State)
    (s1 : M.fmstate) (FR : GSet M.fmrole)
    (ξ : ExecutionTrace Expr → FiniteTrace M.fmstate (Option M.fmrole) → Prop) :
    RelFinitary (simRelWithUser LM ξ) →
    M.liveRoles s1 ≠ ∅ →
    (∀ [HeapGS LM GF],
      ⊢ |={⊤}=> (bigSepM (M := HeapF) (fun l v => iprop(l ↦ v)) σ1.heap -∗
        fragModelIs (GF := GF) s1 -∗
        fragFreeRolesAre (GF := GF) (FR \ M.liveRoles s1) -∗
        hasFuels (GF := GF) 0 (GSet.toGMap (LM.lmFl s1) (M.liveRoles s1)) ={⊤}=∗
        WP e1 @ s; (localeOf [] e1); ⊤ {{ fun _ => hasFuels (GF := GF) 0 ∅ }} ∗
        relAlwaysHolds s [fun _ => hasFuels (GF := GF) 0 ∅]
          (fun extr atr => ξ extr (mapUnderlyingTrace atr)) ([e1], σ1) (initialLs LM s1 0))) →
    ContinuedSimulation (simRelWithUser LM ξ) {tr[([e1], σ1)]} {tr[initialLs LM s1 0]} := by
  intro Hfin _Hfevol H
  refine wp_strong_adequacy (GF := GF) (M := LM.toModel) s _ e1 σ1 (initialLs LM s1 0) Hfin ?_
  intro Hinv
  imod genHeap_init (L := Loc) (V := Val) (GF := GF) (H := HeapF) σ1.heap with ⟨%G, Hgen, Hσ, -⟩
  imod model_state_init (LM := LM) (GF := GF) s1 with ⟨%γmod, Hmod⟩
  icases iOwn_op.1 $$ Hmod with ⟨Hmoda, Hmodf⟩
  imod model_fuel_mapping_init (LM := LM) (GF := GF) s1 0 with ⟨%γmap, Hmapa, Hmapf⟩
  imod model_free_roles_init (LM := LM) (GF := GF) s1 (FR \ M.liveRoles s1) with ⟨%γfr, Hfr⟩
  icases iOwn_op.1 $$ Hfr with ⟨HFR, Hfr⟩
  let hG : HeapGS LM GF :=
    { heap_invGS := Hinv, heap_gen_heapGS := ⟨G⟩,
      heap_fairnessGS := { modelName := γmod, fuelMappingName := γmap, freeRolesName := γfr } }
  imod H with Hwp
  imod Hwp $$ Hσ [Hmodf] [Hfr] [Hmapf] with ⟨Hwp, H⟩
  · unfold fragModelIs; exact .rfl
  · unfold fragFreeRolesAre; exact .rfl
  · unfold hasFuels fragFuelMappingIs
    rw [fuelMapExcl_singleton]
    exact .rfl
  imodintro
  iexists stateInterp (GF := GF), (fun _ => hasFuels (GF := GF) 0 ∅), forkPost (GF := GF)
  isplitr
  · iunfold configWp
    iintro !> %ex %atr %c1 %σ2 %_ %_ %Hstep
    exact (show False from Hstep).elim
  isplitl [Hgen Hmoda Hmapa]
  · rw [heapG_stateInterp_eq]
    isplitr
    · ipureintro
      trivial
    isplitl [Hgen]
    · exact .rfl
    unfold modelStateInterp
    iexists (initialLs LM s1 0).lsMap
    isplitr
    · ipureintro
      refine ⟨?_, rfl⟩
      rw [fuelMapLeInner, mapIncluded_spec]
      intro k v h
      refine ⟨v, h, ?_⟩
      rw [mapIncluded_spec]
      intro k' f h'
      exact ⟨f, h', Nat.le_refl f⟩
    isplitr
    · ipureintro
      exact (initialLs LM s1 0).ls_map_live
    isplitr
    · ipureintro
      intro ζ Hζ
      rw [initialLs_lsMap, GMap.getElem?_singleton]
      split
      · rename_i h
        subst h
        exact absurd (by simp [localesOfList, localesOfListFrom_cons]) Hζ
      · rfl
    isplitl [Hmoda]
    · unfold authModelIs; exact .rfl
    · unfold authFuelMappingIs
      rw [initialLs_lsMap, fuelMapExcl_singleton]
      exact .rfl
  isplitl [Hwp]
  · iexact Hwp
  iunfold relAlwaysHolds0
  iintro %ex %atr %c %Hvalex %Hstartex %Hstartatr %Hendex %Hcontr %Hstuck %Hequiv Hsi Hposts
  obtain rfl : c = ex.last := (FiniteTrace.endsIn_iff.1 Hendex).symm
  have Hcontr' : ∀ ex' atr' oζ ℓ, ex.Contract oζ ex' → atr.Contract ℓ atr' →
      ξ ex' (mapUnderlyingTrace atr') :=
    fun ex' atr' oζ ℓ H1 H2 => (Hcontr ex' atr' oζ ℓ H1 H2).2
  iunfold relAlwaysHolds at H
  ihave H := H $$ %ex %atr %(ex.last) %Hvalex %Hstartex %Hstartatr %Hendex %Hcontr' %Hstuck %Hequiv
  ihave Hkeep : iprop(stateInterp (GF := GF) ex atr ∗
      curPosts ex.last.1 e1 (fun _ => hasFuels (GF := GF) 0 ∅) ={⊤,∅}=∗
      ⌜ξ ex (mapUnderlyingTrace atr)⌝) $$ [H]
  · iintro ⟨Hsi, Hposts⟩
    iapply H $$ Hsi
    exact .rfl
  imod fupd_keep_plain_sep $$ Hkeep [Hsi Hposts] with ⟨%Hξ, Hsi, Hposts⟩
  · isplitl [Hsi]
    · iexact Hsi
    · iexact Hposts
  rw [heapG_stateInterp_eq]
  icases Hsi with ⟨%Hvse, -, Hmsi⟩
  iunfold modelStateInterp at Hmsi
  icases Hmsi with ⟨%fm, %Hfmle, %Hfmdead, %Hfmtp, -, Hfm⟩
  have Hlive1 : ∀ (ρ : M.fmrole) (ζ : BaseLocale),
      (lsMapping (atr.last : LiveStateData BaseLocale M))[ρ]? = some ζ →
      (fromLocale ex.last.1 ζ).isSome := by
    intro ρ ζ Hρ
    obtain ⟨fs, Hfs, -⟩ := ls_mapping_data_inv ρ atr.last ζ Hρ
    by_cases hζ : ζ ∈ localesOfList ex.last.1
    · obtain ⟨⟨tp', e'⟩, Hp, Heq⟩ := List.mem_map.1 hζ
      subst Heq
      rw [fromLocale, fromLocaleFrom_some Hp]
      rfl
    · exfalso
      have Hin : ζ ∈ GMap.dom atr.last.lsMap := GMap.mem_dom_iff.2 ⟨fs, Hfs⟩
      rw [← Hfmle.2, GMap.mem_dom_iff] at Hin
      obtain ⟨v, hv⟩ := Hin
      rw [Hfmtp ζ hζ] at hv
      cases hv
  ihave %Hlive2 : iprop(⌜∀ (ζ : BaseLocale) e, fromLocale ex.last.1 ζ = some e → toVal e ≠ none →
      ∀ ρ : M.fmrole, (lsMapping (atr.last : LiveStateData BaseLocale M))[ρ]? = some ζ →
        ρ ∉ M.liveRoles atr.last.lsUnder⌝) $$ [Hfm Hposts]
  · by_cases hP : ∀ (ζ : BaseLocale) e, fromLocale ex.last.1 ζ = some e → toVal e ≠ none →
        ∀ ρ : M.fmrole, (lsMapping (atr.last : LiveStateData BaseLocale M))[ρ]? = some ζ →
          ρ ∉ M.liveRoles atr.last.lsUnder
    · ipureintro
      exact hP
    simp only [Classical.not_forall, not_not] at hP
    obtain ⟨ζ, e, Hsome, Hnoval, ρ, Hρ, Hlive⟩ := hP
    obtain ⟨v, Hv⟩ := Option.ne_none_iff_exists'.1 Hnoval
    have Hsome' := (fromLocale_eq_some_iff _ _ _).1 Hsome
    ihave Hem : hasFuels (GF := GF) ζ ∅ $$ [Hposts]
    · exact posts_of_empty_mapping (M := LM.toModel) (GF := GF) e1 e v ζ ex.last.1 Hsome' Hv
    ihave %Hagree := has_fuels_agree $$ Hfm Hem
    ipureintro
    exfalso
    obtain ⟨fs, HSome, Hfs⟩ := ls_mapping_data_inv ρ atr.last ζ Hρ
    obtain ⟨fs', HSomefs, Hfs'⟩ := (mapIncluded_spec _ _ _).1 Hfmle.1 ζ ∅ Hagree
    rw [HSome] at HSomefs
    cases HSomefs
    obtain ⟨ζ'', fs'', HSome'', Hfs''⟩ := Hfmdead ρ Hlive
    obtain ⟨fs''', HSome''', Hfs'''⟩ := (mapIncluded_spec _ _ _).1 Hfmle.1 ζ'' fs'' HSome''
    have Hζ : ζ'' = ζ := by
      by_contra Hneq
      rcases atr.last.ls_map_disj ζ ζ'' fs fs''' (Ne.symm Hneq) HSome HSome''' ρ with h | h
      · exact GMap.not_mem_iff.2 h (GMap.mem_dom.1 Hfs)
      · exact GMap.not_mem_iff.2 h
          (mapIncluded_subseteq_inv _ _ _ Hfs''' ρ (GMap.mem_dom.1 Hfs''))
    subst Hζ
    rw [Hagree] at HSome''
    cases HSome''
    rw [GMap.mem_dom_iff] at Hfs''
    obtain ⟨f, hf⟩ := Hfs''
    simp at hf
  iapply fupd_mask_intro_discard LawfulSet.empty_subset
  ipureintro
  exact ⟨⟨Hvse, Hlive1, Hlive2⟩, Hξ⟩

@[rocq_alias trillium.fairis.simulation_adequacy]
theorem simulation_adequacy [HeapGpreS LM GF] (s : Stuckness) (e1 : Expr) (σ1 : State)
    (s1 : M.fmstate) (FR : GSet M.fmrole) :
    -- The model has finite branching
    RelFinitary (simRel (Expr := Expr) LM) →
    M.liveRoles s1 ≠ ∅ →
    (∀ [HeapGS LM GF],
      ⊢ |={⊤}=> (fragModelIs (GF := GF) s1 -∗
        fragFreeRolesAre (GF := GF) (FR \ M.liveRoles s1) -∗
        hasFuels (GF := GF) 0 (GSet.toGMap (LM.lmFl s1) (M.liveRoles s1)) ={⊤}=∗
        WP e1 @ s; 0; ⊤ {{ fun _ => hasFuels (GF := GF) 0 ∅ }})) →
    ContinuedSimulation (simRel LM) {tr[([e1], σ1)]} {tr[initialLs LM s1 0]} := by
  intro Hfevol Hne H
  have Heq : simRel (Expr := Expr) LM = simRelWithUser LM (fun _ _ => True) := by
    funext ex atr
    exact propext ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
  rw [Heq]
  refine strong_simulation_adequacy GF LM s e1 σ1 s1 FR _ (Heq ▸ Hfevol) Hne ?_
  intro Hinv
  imod H with H
  imodintro
  iintro - Hm Hfr Hf
  imod H $$ Hm Hfr Hf with Hwp
  imodintro
  isplitl [Hwp]
  · -- `localeOf [] e1` is `0`
    exact .rfl
  · iunfold relAlwaysHolds
    iintro %_ %_ %_ %_ %_ %_ %_ %_ %_ %_ - -
    iapply fupd_mask_intro_discard LawfulSet.empty_subset
    ipureintro
    trivial

@[rocq_alias trillium.fairis.simulation_adequacy_inftraces]
theorem simulation_adequacy_inftraces [HeapGpreS LM GF] (s : Stuckness) (FR : GSet M.fmrole)
    (e1 : Expr) (σ1 : State) (s1 : M.fmstate) (iex : InfExecutionTrace Expr)
    (Hvex : ValidInfExec ({tr[([e1], σ1)]} : ExecutionTrace Expr) iex) :
    -- The model has finite branching
    RelFinitary (simRel (Expr := Expr) LM) →
    M.liveRoles s1 ≠ ∅ →
    (∀ [HeapGS LM GF],
      ⊢ |={⊤}=> (fragModelIs (GF := GF) s1 -∗
        fragFreeRolesAre (GF := GF) (FR \ M.liveRoles s1) -∗
        hasFuels (GF := GF) 0 (GSet.toGMap (LM.lmFl s1) (M.liveRoles s1)) ={⊤}=∗
        WP e1 @ s; 0; ⊤ {{ fun _ => hasFuels (GF := GF) 0 ∅ }})) →
    ∃ iatr, ValidInfSystemTrace (ContinuedSimulation (simRel LM))
      ({tr[([e1], σ1)]} : ExecutionTrace Expr) {tr[initialLs LM s1 0]} iex iatr := by
  intro Hfin Hlr Hwp
  exact ⟨_, produced_inf_aux_trace_valid_inf _ _ _ (ValidSystemTrace.singleton _ _)
    (simulation_adequacy GF LM s e1 σ1 s1 FR Hfin Hlr Hwp) iex Hvex⟩

/-- Execution traces of HeapLang (Rocq `heap_lang_extrace`). -/
@[rocq_alias trillium.fairis.heap_lang_extrace]
abbrev HeapLangExtrace : Type := Extrace Expr

@[rocq_alias trillium.fairis.simulation_adequacy_traces]
theorem simulation_adequacy_traces [HeapGpreS LM GF] (s : Stuckness) (FR : GSet M.fmrole)
    (e1 : Expr) (s1 : M.fmstate) (extr : HeapLangExtrace) (Hvex : ExtraceValid extr)
    (Hexfirst : extr.first.1 = [e1]) :
    -- The model has finite branching
    RelFinitary (simRel (Expr := Expr) LM) →
    M.liveRoles s1 ≠ ∅ →
    (∀ [HeapGS LM GF],
      ⊢ |={⊤}=> (fragModelIs (GF := GF) s1 -∗
        fragFreeRolesAre (GF := GF) (FR \ M.liveRoles s1) -∗
        hasFuels (GF := GF) 0 (GSet.toGMap (LM.lmFl s1) (M.liveRoles s1)) ={⊤}=∗
        WP e1 @ s; 0; ⊤ {{ fun _ => hasFuels (GF := GF) 0 ∅ }})) →
    ∃ auxtr : Auxtrace LM, ExauxTracesMatch Expr LM extr auxtr := by
  intro Hfin Hlr Hwp
  have Hfirst : (([e1], extr.first.2) : List Expr × State) = extr.first :=
    Prod.ext Hexfirst.symm rfl
  obtain ⟨iatr, Hbig⟩ := simulation_adequacy_inftraces GF LM s FR e1 extr.first.2 s1
    (fromTrace extr) (from_trace_preserves_validity extr _ Hvex (ValidExec.singleton _) Hfirst)
    Hfin Hlr Hwp
  exact ⟨toTrace (initialLs LM s1 0) iatr,
    valid_inf_system_trace_implies_traces_match LM (ContinuedSimulation (simRel LM)) _ _ _ _
      extr _ (fun _ _ h => h.rel.2) (fun _ _ h => h.rel.1) (from_trace_spec ({tr[([e1], extr.first.2)]} : ExecutionTrace Expr) extr Hfirst)
      (to_trace_spec _ _) Hbig⟩

@[rocq_alias trillium.fairis.simulation_adequacy_model_trace]
theorem simulation_adequacy_model_trace [HeapGpreS LM GF] (s : Stuckness) (FR : GSet M.fmrole)
    (e1 : Expr) (s1 : M.fmstate) (extr : HeapLangExtrace) (Hvex : ExtraceValid extr)
    (Hexfirst : extr.first.1 = [e1]) :
    -- The model has finite branching
    RelFinitary (simRel (Expr := Expr) LM) →
    M.liveRoles s1 ≠ ∅ →
    (∀ [HeapGS LM GF],
      ⊢ |={⊤}=> (fragModelIs (GF := GF) s1 -∗
        fragFreeRolesAre (GF := GF) (FR \ M.liveRoles s1) -∗
        hasFuels (GF := GF) 0 (GSet.toGMap (LM.lmFl s1) (M.liveRoles s1)) ={⊤}=∗
        WP e1 @ s; 0; ⊤ {{ fun _ => hasFuels (GF := GF) 0 ∅ }})) →
    ∃ (auxtr : Auxtrace LM) (mtr : Mtrace M), ExauxTracesMatch Expr LM extr auxtr ∧
      UptoStutterAuxtr LM auxtr mtr := by
  intro Hfb Hlr Hwp
  obtain ⟨auxtr, Hmatch⟩ :=
    simulation_adequacy_traces GF LM s FR e1 s1 extr Hvex Hexfirst Hfb Hlr Hwp
  obtain ⟨mtr, Hupto⟩ := can_destutter_auxtr auxtr (exaux_preserves_validity extr auxtr Hmatch)
  exact ⟨auxtr, mtr, Hmatch, Hupto⟩

@[rocq_alias trillium.fairis.simulation_adequacy_terminate]
theorem simulation_adequacy_terminate [HeapGpreS LM GF] (s : Stuckness) (e1 : Expr)
    (s1 : M.fmstate) (FR : GSet M.fmrole) (extr : HeapLangExtrace)
    (Hexfirst : extr.first.1 = [e1]) :
    (∀ mtr : Mtrace M, MtraceFairlyTerminating mtr) →
    -- The model has finite branching
    RelFinitary (simRel (Expr := Expr) LM) →
    M.liveRoles s1 ≠ ∅ →
    (∀ [HeapGS LM GF],
      ⊢ |={⊤}=> (fragModelIs (GF := GF) s1 -∗
        fragFreeRolesAre (GF := GF) (FR \ M.liveRoles s1) -∗
        hasFuels (GF := GF) 0 (GSet.toGMap (LM.lmFl s1) (M.liveRoles s1)) ={⊤}=∗
        WP e1 @ s; 0; ⊤ {{ fun _ => hasFuels (GF := GF) 0 ∅ }})) →
    ExtraceFairlyTerminating extr := by
  intro Hterm Hfb Hlr Hwp Hvex Hfair
  obtain ⟨auxtr, mtr, Hmatch, Hupto⟩ :=
    simulation_adequacy_model_trace GF LM s FR e1 s1 extr Hvex Hexfirst Hfb Hlr Hwp
  rcases infinite_or_finite extr with Hinf | Hfin
  swap
  · exact Hfin
  have Hfairaux := fairness_preserved extr auxtr Hinf Hmatch Hfair
  have Hvalaux := exaux_preserves_validity extr auxtr Hmatch
  have Hfairm := upto_stutter_fairness auxtr mtr Hupto Hfairaux
  have Hmtrvalid := upto_preserves_validity auxtr mtr Hupto Hvalaux
  have Htermtr := Hterm mtr Hmtrvalid Hfairm
  exact exaux_preserves_termination extr auxtr Hmatch (upto_stutter_finiteness auxtr mtr Hupto Htermtr)

@[rocq_alias trillium.fairis.simulation_adequacy_terminate_ftm]
theorem simulation_adequacy_terminate_ftm [FairTerminatingModel M] [HeapGpreS LM GF]
    (s : Stuckness) (e1 : Expr) (s1 : M.fmstate) (FR : GSet M.fmrole) (extr : HeapLangExtrace)
    (Hexfirst : extr.first.1 = [e1]) :
    -- The model has finite branching
    RelFinitary (simRel (Expr := Expr) LM) →
    M.liveRoles s1 ≠ ∅ →
    (∀ [HeapGS LM GF],
      ⊢ |={⊤}=> (fragModelIs (GF := GF) s1 -∗
        fragFreeRolesAre (GF := GF) (FR \ M.liveRoles s1) -∗
        hasFuels (GF := GF) 0 (GSet.toGMap (LM.lmFl s1) (M.liveRoles s1)) ={⊤}=∗
        WP e1 @ s; 0; ⊤ {{ fun _ => hasFuels (GF := GF) 0 ∅ }})) →
    ExtraceFairlyTerminating extr :=
  simulation_adequacy_terminate GF LM s e1 s1 FR extr Hexfirst
    (fun mtr => fair_terminating_traces_terminate mtr)

end adequacy

end Trillium.Fairis
