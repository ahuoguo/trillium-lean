# Paper ↔ Lean mapping

This file maps the definitions, rules, theorems and examples of the paper

> Amin Timany, Simon Oddershede Gregersen, Léo Stefanesco, Jonas Kastberg Hinrichsen, Léon Gondelman,
> Abel Nieto, Lars Birkedal. **Trillium: Higher-Order Concurrent and Distributed Separation Logic for
> Intensional Refinement.** POPL 2024. <https://iris-project.org/pdfs/2024-popl-trillium.pdf>

to the Lean port in this repository. The port follows the Rocq development
[logsem/trillium@02ee7fc](https://github.com/logsem/trillium/tree/02ee7fc38046c1c46a0cd2a9765733bea1592e59)
declaration by declaration (see [`CORRESPONDENCE.md`](CORRESPONDENCE.md)), so each row also gives the
Rocq name. Every Lean declaration listed here carries `@[rocq_alias …]`, so `#check @Rocq.trillium.<rocq name>`
(or `Rocq.trillium.fairis.<rocq name>`, …) also finds it.

Notation used in the tables: Lean names are relative to the namespace in the "Lean file" column
(`Trillium`, `Trillium.Fairis`, `Trillium.Fairness`, `Trillium.HeapLang`, or an example namespace such as
`Trillium.Fairis.Yesno`).

---

## §2 Background and key observations

| Paper | Lean | Lean file | Rocq | Notes |
|---|---|---|---|---|
| LTS (model) | `Model` (`mstate`, `mlabel`, `mtrans`) | [`ProgramLogic/Traces.lean`](Trillium/ProgramLogic/Traces.lean) | `Model` | |
| Finite traces, `last`, `first`, `τ →ℓ s` | `FiniteTrace` (`.singleton`, `.extend`, notation `ft :tr[ℓ]: a`), `FiniteTrace.last`, `FiniteTrace.first` | [`Traces/Trace.lean`](Trillium/Traces/Trace.lean) | `finite_trace`, `trace_last`, `trace_first`, `trace_extend` | |
| `prefix(τ, τ′)` | `FiniteTrace.IsPrefix` | [`Traces/Trace.lean`](Trillium/Traces/Trace.lean) | `trace_prefix` | |
| Possibly-infinite traces | `InfList` (= Mathlib `Stream'.Seq`), `InfExecutionTrace`, `InfAuxiliaryTrace` | [`Traces/InfiniteTrace.lean`](Trillium/Traces/InfiniteTrace.lean), [`ProgramLogic/Traces.lean`](Trillium/ProgramLogic/Traces.lean) | `inflist`, `inf_execution_trace`, `inf_auxiliary_trace` | Rocq's coinductive `inflist` is represented by `Stream'.Seq`. |
| **Def. 2.1** ξ-forward simulation `ForSim_ξ(R)` | `ContinuedSimulationPre` | [`ProgramLogic/Traces.lean`](Trillium/ProgramLogic/Traces.lean) | `continued_simulation_pre` | The one-step functor `F_≼ξ` whose post-fixpoints are the ξ-forward simulations. |
| **Def. 2.2** intensional refinement `τ ≼_ξ τ′` | `ContinuedSimulation` (unfolding: `continuedSimulation_unfold`) | [`ProgramLogic/Traces.lean`](Trillium/ProgramLogic/Traces.lean) | `continued_simulation`, `continued_simulation_unfold` | Defined as the greatest fixpoint `GFX` of `F_≼ξ` ([`Prelude/Fixpoint.lean`](Trillium/Prelude/Fixpoint.lean)); `GFX Ψ x = ∃ P, P x ∧ (∀ y, P y → Ψ P y)` is exactly `∃R. ForSim_ξ(R) ∧ R(τ,τ′)`. |
| **Def. 2.3** trace relation extension `R̂` | `ValidInfSystemTrace` | [`ProgramLogic/Traces.lean`](Trillium/ProgramLogic/Traces.lean) | `valid_inf_system_trace` | Stated coinductively (a Lean `coinductive` predicate): every pair of prefixes along the two infinite traces is related. |
| **Lemma 2.4** intensional refinement, lifting | `produced_inf_aux_trace_valid_inf` (with the witness `produceInfAuxTrace`, built by `Stream'.Seq.corec`) | [`ProgramLogic/Traces.lean`](Trillium/ProgramLogic/Traces.lean) | `produced_inf_aux_trace_valid_inf`, `produce_inf_aux_trace` | For valid program executions (`ValidInfExec`). |
| Stutter-lifting (sound for safety) | `AllowsStuttering`, `AllowsPureStep`, `wp_stuttering_atomic` | [`ProgramLogic/WeakestPre.lean`](Trillium/ProgramLogic/WeakestPre.lean) | `AllowsStuttering`, `AllowsPureStep`, `wp_stuttering_atomic` | Not a separate LTS construction: a model that admits a stuttering label is required via these classes. |
| Fin-stutter-lifting (sound for liveness) | the Fuel construction, see §4.3 below | | | |
| **Def. 2.5** finite approximation `FinApprox(F)` | `gsimPre`, `gsim` (guarded fixpoint in Iris) | [`ProgramLogic/Adequacy.lean`](Trillium/ProgramLogic/Adequacy.lean) | `Gsim_pre`, `Gsim` | The development does not define `FinApprox` abstractly. It defines the step-indexed (guarded-recursive) simulation, whose meaning is the finite approximation. |
| **Def. 2.6** relative image-finiteness | `RelFinitary` | [`ProgramLogic/AdequacyLocales.lean`](Trillium/ProgramLogic/AdequacyLocales.lean) | `rel_finitary` | |
| **Thm. 2.7** finite approximation | `simulation_correspondence`, `simulation_correspondence_multiple` | [`ProgramLogic/Adequacy.lean`](Trillium/ProgramLogic/Adequacy.lean) | `simulation_correspondence(_multiple)` | Proved for the concrete `gsim`: `RelFinitary ξ → (⊢ gsim … ) → ContinuedSimulation ξ …`. The key step uses `extract_exists_alt2` ([`Prelude/IrisExtraction.lean`](Trillium/Prelude/IrisExtraction.lean)) and the cardinality lemmas of [`Prelude/Quantifiers.lean`](Trillium/Prelude/Quantifiers.lean) / [`Prelude/Finitary.lean`](Trillium/Prelude/Finitary.lean) (`forall_exists_swap`, `finite_smaller_card_nat`). |

Not mechanised (illustrations only, also absent from the Rocq development): the LTSs `Chain`,
`FinChains`, `Chain-Loops`, `Chain-Fin-Stutter` (Fig. 1 and §2.1) and the program `count_up` (Fig. 2).

## §3 Trillium: a trace program logic framework

| Paper | Lean | Lean file | Rocq | Notes |
|---|---|---|---|---|
| Language: `Expr`, `Val`, `Ectx`, `State`, prim. reduction `e₁,σ₁ ⇝ e₂,σ₂;e_f` | `class Language` (`primStep`, `toVal`/`ToVal.ofVal`, `Iris.ProgramLogic.fill`), built from `EctxLanguage` / `EctxiLanguage` | [`ProgramLogic/Language.lean`](Trillium/ProgramLogic/Language.lean), [`EctxLanguage.lean`](Trillium/ProgramLogic/EctxLanguage.lean), [`EctxiLanguage.lean`](Trillium/ProgramLogic/EctxiLanguage.lean) | `language`, `LanguageMixin`, `prim_step` | |
| Locales `ζ`, fresh locales `fr(ζ, tp)` | `LanguageCore.localeOf : List Expr → Expr → Locale` with `locale_injective`, `locale_equiv` | [`ProgramLogic/Language.lean`](Trillium/ProgramLogic/Language.lean) | `locale_of`, `locale_injective`, `locale_equiv` | The thread pool is a **list**; a thread's locale is computed from the threads before it (`localeOf prefix e`). A forked thread `efᵢ` gets locale `localeOf (tp₁ ++ K[e] :: tp₂ ++ take i efs) efᵢ`, which plays the role of `fr(ζ,tp)ᵢ`. |
| Configuration `c = (tp, σ)`, `tp(ζ)` | `List Expr × State`, `fromLocale tp ζ` | [`ProgramLogic/AdequacyLocales.lean`](Trillium/ProgramLogic/AdequacyLocales.lean) | `cfg`, `from_locale` | |
| Labelled step `c →ζ c′` | `Language.LocaleStep` (labels `Option Locale`; `none` = a `LanguageCore.configStep`) | [`ProgramLogic/Language.lean`](Trillium/ProgramLogic/Language.lean) | `locale_step` | Trillium also has configuration (environment) steps, unused by HeapLang. |
| Program traces `τ`, valid executions | `ExecutionTrace`, `ValidExec`, `ValidSystemTrace` | [`ProgramLogic/Traces.lean`](Trillium/ProgramLogic/Traces.lean) | `execution_trace`, `valid_exec`, `valid_system_trace` | |
| Trace interpretation `S(τ, κ)` | field `IrisG.stateInterp : ExecutionTrace → AuxiliaryTrace M → IProp GF` (with `forkPost` for Ψ) | [`ProgramLogic/WeakestPre.lean`](Trillium/ProgramLogic/WeakestPre.lean) | `irisG`, `state_interp`, `fork_post` | |
| Trillium WP `wp^ζ_E e {Φ}` (guarded fixpoint) | `wp.pre`, `wp.def` (via iris-lean's `fixpoint`), notation `WP e @ s; ζ; E {{ v, Φ }}` / `WP e @[ζ] E {{ … }}` | [`ProgramLogic/WeakestPre.lean`](Trillium/ProgramLogic/WeakestPre.lean), [`BI/WeakestPre.lean`](Trillium/BI/WeakestPre.lean) | `wp_pre`, `wp_def`, `Wp` | In the value case the paper writes `∀τ κ. S(τ,κ) -∗ |⇛ S(τ,κ) ∗ Φ(e)`; the code names this modality `preStep` (`|~{E}~| Φ v`). In the step case the code quantifies over an arbitrary `∃ δ₂ ℓ` and extends both traces, and the step goes through `step_fupdN` with `trace_length` laters. Model transitions are not hard-coded in the WP; they are enforced through `S` and ξ. |
| Remark 3.1 (invariants, update modality, auth resources) | iris-lean (`Iris.Instances.Lib.Invariants`, `FUpd`, `Iris.Algebra.Auth`, …) | — | — | Iris itself, not part of Trillium. |
| **wp-atomic** | `wp_atomic` (and `wp_stuttering_atomic`) | [`ProgramLogic/WeakestPre.lean`](Trillium/ProgramLogic/WeakestPre.lean) | `wp_atomic` | IPM instances `elimAcc_wp_atomic` etc. make `iinv` work. |
| Other standard WP rules (bind, mono, lifting) | `wp_bind`, `wp_strong_mono`, `wp_lift_step_fupdN`, `wp_lift_head_*`, … | [`ProgramLogic/WeakestPre.lean`](Trillium/ProgramLogic/WeakestPre.lean), [`Lifting.lean`](Trillium/ProgramLogic/Lifting.lean), [`EctxLifting.lean`](Trillium/ProgramLogic/EctxLifting.lean) | same names | |
| `AlwaysHolds(ξ, c, m)` | `relAlwaysHolds0` (single thread), `relAlwaysHolds`, `relAlwaysHoldsWithTraceInv` | [`ProgramLogic/Adequacy.lean`](Trillium/ProgramLogic/Adequacy.lean) | `rel_always_holds0`, `rel_always_holds`, `rel_always_holds_with_trace_inv` | The paper defers the precise definition to the Coq development; it is ported exactly. |
| **Thm. 3.2** Adequacy | `wp_strong_adequacy` (also `_multiple`, `_with_trace_inv`); `sim_and_adequacy_xi` / `adequacy_xi` add the usual Iris guarantees (`Adequate`) | [`ProgramLogic/Adequacy.lean`](Trillium/ProgramLogic/Adequacy.lean) | `wp_strong_adequacy`, `sim_and_adequacy_xi` | Conclusion `ContinuedSimulation ξ {tr[([e₁], σ₁)]} {tr[δ₁]}` = `c ≼_ξ m`. Differences: (i) the hypothesis additionally contains `configWp` (WP for configuration steps; trivial for HeapLang); (ii) the paper's side condition `ξ(c, m)` on the initial traces is subsumed by `relAlwaysHolds0`; (iii) `[InvGpreS GF]` replaces a concrete `Σ`. Depends only on `propext`, `Classical.choice`, `Quot.sound`. |
| Two-stage proof: WP ⇒ finite approximation ⇒ refinement | `wp_strong_adequacy_helper` (⊢ `gsim`), then `simulation_correspondence` (Thm. 2.7) | [`ProgramLogic/Adequacy.lean`](Trillium/ProgramLogic/Adequacy.lean) | `wp_strong_adequacy_helper`, `simulation_correspondence` | The fancy-update elimination goes through `fupdToBupd` / `fupd_to_bupd_soundness_no_lc`. |

## §4 The Fairis logic

### Fairness, traces and termination (the 7-step methodology)

| Paper | Lean | Lean file | Rocq | Notes |
|---|---|---|---|---|
| Model `M` with roles, live roles `lroles(m)` | `FairModel` (`fmstate`, `fmrole`, `fmtrans`, `liveRoles`, `fm_live_spec`) | [`Fairness/Fairness.lean`](Trillium/Fairness/Fairness.lean) | `FairModel` | `liveRoles` is given as data with a soundness condition, not defined as `{ρ \| ∃m′. m →ρ m′}`. |
| Possibly-infinite traces (with `after`, lookups) | `Trace` (`⟨s⟩ₜ`, `s -[ℓ]-> tr`), `after`, `predAt`, `tr !! n` | [`Fairness/Inftraces.lean`](Trillium/Fairness/Inftraces.lean), [`TraceLookup.lean`](Trillium/Fairness/TraceLookup.lean) | `trace`, `after`, `pred_at` | |
| `fair(τ)` for program traces | `fairEx ζ extr` (∀ ζ) | [`Fairness/Fairness.lean`](Trillium/Fairness/Fairness.lean) | `fair_ex` | |
| `fair(κ)` for model traces | `fairModelTrace ρ mtr` (∀ ρ) | [`Fairness/Fairness.lean`](Trillium/Fairness/Fairness.lean) | `fair_model_trace` | |
| `fairly_terminating(c)` (§4.2.1) | `ExtraceFairlyTerminating` | [`Fairness/Fairness.lean`](Trillium/Fairness/Fairness.lean) | `extrace_fairly_terminating` | |
| Step (4): local criterion for fair termination of `M` | `class FairTerminatingModel`, `fair_terminating_traces_terminate`, `MtraceFairlyTerminating` | [`Fairis/FairTermination.lean`](Trillium/Fairis/FairTermination.lean) | `FairTerminatingModel`, `fair_terminating_traces_terminate` | The criterion from the paper's appendix: a well-founded order with a decreasing live role. |
| Steps (5)–(7) for termination | `continued_simulation_fair_termination`, `heap_lang_continued_simulation_fair_termination` | [`Fairis/FuelTermination.lean`](Trillium/Fairis/FuelTermination.lean), [`Fairis/Adequacy.lean`](Trillium/Fairis/Adequacy.lean) | same names | |

### §4.3 The Fuel construction `Fuel(M)` and ξ_fuel

| Paper | Lean | Lean file | Rocq | Notes |
|---|---|---|---|---|
| Fuel state `f = (f.m, f.map)` with the two well-formedness conditions | `LiveStateData` (`lsUnder`, `lsMap`), `LiveState` (+ `ls_map_disj`, `ls_map_live`) | [`Fairis/Fuel.lean`](Trillium/Fairis/Fuel.lean) | `LiveStateData`, `LiveState` | |
| `fm_f`, `th_f` | `lsFuel`, `lsMapping` | [`Fairis/Fuel.lean`](Trillium/Fairis/Fuel.lean) | `ls_fuel`, `ls_mapping` | |
| Labels `tau_ζ`, `vis_ζ(ρ)` | `FairLabel.silentStep ζ`, `FairLabel.takeStep ρ ζ` (also `.configStep`) | [`Fairis/Fuel.lean`](Trillium/Fairis/Fuel.lean) | `Silent_step`, `Take_step`, `Config_step` | |
| **Fig. 10** transitions of `Fuel(M)` | `lsTrans` | [`Fairis/Fuel.lean`](Trillium/Fairis/Fuel.lean) | `ls_trans` | Conditions: **st** = `fmtrans` / `lsUnder` unchanged; **th** = `lsMapping a !! ρ = some ζ`; **dec**+**ch** = `fuelDecr` with `MustDecrease` (`.sameTid`, `.changeTid`); **ni** = `fuelMustNotIncr`; **dom** and **ref** = the domain and `oleq … (lmFl b)` clauses. |
| Global fuel cap `F_cap` | `LiveModel.lmFl : M → ℕ` | [`Fairis/Fuel.lean`](Trillium/Fairis/Fuel.lean) | `lm_fl` | Generalised to a state-dependent cap. The examples use 61 (yes-no, even-odd) and 40 (choose-nat). |
| `Fuel(M)` as a Trillium model | `LiveModel`, `LiveModel.toModel` | [`Fairis/Fuel.lean`](Trillium/Fairis/Fuel.lean) | `LiveModel`, `fair_model_model` / `live_model_to_model` | |
| Initial state `m̃` (`F_init`, all roles at `F_cap`) | `initialLs LM s₀ ζ₀` | [`Fairis/Fuel.lean`](Trillium/Fairis/Fuel.lean) | `initial_ls` | |
| ξ_fuel condition (1): labels agree | `labelsMatch`, `validStateEvolutionFairness` | [`Fairis/Fuel.lean`](Trillium/Fairis/Fuel.lean) | `labels_match`, `valid_state_evolution_fairness` | |
| ξ_fuel condition (2): role owners are threads; finished threads own no live roles | `liveTids` (via `liveRel`) | [`Fairis/Fuel.lean`](Trillium/Fairis/Fuel.lean), [`FairnessFiniteness.lean`](Trillium/Fairis/FairnessFiniteness.lean) | `live_tids`, `live_rel` | |
| ξ_fuel = Fuel(ξ) | `simRelWithUser LM ξ` (`simRel LM` for trivial ξ) | [`Fairis/FairnessFiniteness.lean`](Trillium/Fairis/FairnessFiniteness.lean) | `sim_rel_with_user`, `sim_rel` | The user's ξ is applied to the projected model trace `mapUnderlyingTrace`. |
| "ξ_fuel is relatively image-finite whenever ξ is" | `rel_finitary_sim_rel_with_user_ξ`, `valid_state_evolution_finitary_fairness` | [`Fairis/FairnessFiniteness.lean`](Trillium/Fairis/FairnessFiniteness.lean) | same names | |
| Induced trace `κ̄` (drop tau steps) | `UptoStutter`, `UptoStutterAuxtr`, `destutter`, `can_destutter_auxtr` | [`Fairis/Destuttering.lean`](Trillium/Fairis/Destuttering.lean), [`Fuel.lean`](Trillium/Fairis/Fuel.lean) | `upto_stutter`, `upto_stutter_auxtr`, `can_destutter_auxtr` | Rocq's paco definition (mixing induction and coinduction) is a union of post-fixpoints here. |
| "κ finite iff κ̄ finite"; `κ` fair ⇒ `κ̄` fair | `upto_stutter_finiteness`, `upto_stutter_fairness` | [`Fairis/Fuel.lean`](Trillium/Fairis/Fuel.lean) | same names | Finite stuttering because every tau step decreases `fuelMeasure` (Rocq `Ψ`). |
| **Lemma 4.3** τ fair and `ξ̂_fuel(τ, κ)` ⇒ κ fair | `fairness_preserved` (from `ExauxTracesMatch`, obtained by `valid_inf_system_trace_implies_traces_match`) | [`Fairis/Fuel.lean`](Trillium/Fairis/Fuel.lean) | `fairness_preserved` | Proved by the lexicographic induction sketched in the paper. |
| **Lemma 4.2** `AlwaysHolds(Fuel(ξ)) ⇐ AlwaysHolds(ξ)` | inside the proof of `strong_simulation_adequacy` | [`Fairis/Adequacy.lean`](Trillium/Fairis/Adequacy.lean) | (inside `strong_simulation_adequacy`) | Not a separate lemma in Rocq or Lean. |

### Logical resources, trace interpretation, and Thm. 4.1

| Paper | Lean | Lean file | Rocq | Notes |
|---|---|---|---|---|
| `◦γM(m)`, `•γM(m)` | `fragModelIs m`, `authModelIs m` | [`Fairis/Resources.lean`](Trillium/Fairis/Resources.lean) | `frag_model_is`, `auth_model_is` | |
| `ζ ⇒ fs` | `hasFuels ζ fs`, notation `ζ ↦M fs` | [`Fairis/Resources.lean`](Trillium/Fairis/Resources.lean) | `has_fuels` | |
| `ζ ⇒ fs⁺⁺` | `hasFuelsS ζ fs`, notation `ζ ↦M++ fs` | [`Fairis/Resources.lean`](Trillium/Fairis/Resources.lean) | `has_fuels_S` | |
| `FuelMap(FM)` | `authFuelMappingIs FM` | [`Fairis/Resources.lean`](Trillium/Fairis/Resources.lean) | `auth_fuel_mapping_is` | |
| FuelMap-agree / FuelMap-update | `has_fuels_agree` / `has_fuels_update` | [`Fairis/Resources.lean`](Trillium/Fairis/Resources.lean) | same names | |
| Ghost state | `FairnessGpreS`, `FairnessGS`; with the heap: `HeapGpreS`, `HeapGS` | [`Fairis/Resources.lean`](Trillium/Fairis/Resources.lean), [`HeapLangLM.lean`](Trillium/Fairis/HeapLangLM.lean) | `fairnessGpreS`, `fairnessGS`, `heapGpreS`, `heapGS` | |
| Fairis trace interpretation `S(τ, κ)` | `heapG_irisG` (`stateInterp = ⌜validStateEvolutionFairness⌝ ∗ genHeapInterp ∗ modelStateInterp`) | [`Fairis/HeapLangLM.lean`](Trillium/Fairis/HeapLangLM.lean) | `heapG_irisG` | `ownHeap(σ)` = iris-lean `genHeapInterp`. |
| `coherent(FM, m, fm)` ∗ `dom(FM) ⊆ dom(tp)` | `modelStateInterp` = `fuelMapLe` ∗ `fuelMapPreserveDead` ∗ `fuelMapPreserveThreadpool` ∗ `authModelIs` ∗ `authFuelMappingIs` | [`Fairis/Resources.lean`](Trillium/Fairis/Resources.lean) | `model_state_interp`, `fuel_map_le`, `fuel_map_preserve_dead`, `fuel_map_preserve_threadpool` | |
| Ghost updates behind the rules | `update_fuel_step`, `update_model_step`, `update_fork_step` | [`Fairis/ResourcesUpdates.lean`](Trillium/Fairis/ResourcesUpdates.lean) | same names | |
| **Thm. 4.1** Fairis adequacy | `strong_simulation_adequacy` (with a user ξ), `simulation_adequacy` (ξ trivial); trace-level corollaries `simulation_adequacy_inftraces`, `_traces`, `_model_trace`, `_terminate`, `_terminate_ftm` | [`Fairis/Adequacy.lean`](Trillium/Fairis/Adequacy.lean) | same names | Conclusion `ContinuedSimulation (simRelWithUser LM ξ) {tr[([e₁],σ₁)]} {tr[initialLs LM s₁ 0]}` = `c ≼_{ξ_fuel} m̃`. Hypothesis: `[∗ map] l ↦ v ∈ σ₁.heap`, `fragModelIs s₁`, `0 ↦M F_init`, plus `fragFreeRolesAre` (free-role tokens not discussed in the paper), and `WP … {{ 0 ↦M ∅ }} ∗ relAlwaysHolds` for the user's ξ. `simulation_adequacy_terminate_ftm` packages steps (1)–(7) for termination. |

### §4.1 The Fairis program logic (Fig. 5)

| Paper rule | Lean | Lean file | Rocq | Notes |
|---|---|---|---|---|
| Inner WP `wp_E e ⟨Φ⟩` | `sswp s E e Φ` (Φ : `Expr → IProp`) | [`HeapLang/SswpLogic.lean`](Trillium/HeapLang/SswpLogic.lean) | `sswp` | Single-step WP over the heap only. |
| **wp-step-fuel** | `wp_step_fuel` | [`Fairis/Lifting.lean`](Trillium/Fairis/Lifting.lean) | `wp_step_fuel` | |
| **wp-step-model** | `wp_step_model`, `wp_step_model_singlerole` | [`Fairis/Lifting.lean`](Trillium/Fairis/Lifting.lean) | same names | Replenished fuel is `LM.lmFl m′` (= `F_cap`). |
| **wp-role-dealloc** | `wp_role_dealloc` (and `has_fuels_dealloc`) | [`Fairis/Lifting.lean`](Trillium/Fairis/Lifting.lean) | same names | |
| **wp-role-fork** | `wp_role_fork` | [`Fairis/Lifting.lean`](Trillium/Fairis/Lifting.lean) | `wp_role_fork` | |
| **wp-alloc** | `HeapLang.wp_alloc` (also `wp_allocN_seq`) | [`HeapLang/SswpLogic.lean`](Trillium/HeapLang/SswpLogic.lean) | `wp_alloc` | Stated on `sswp` despite the `wp_` name, as in Rocq. |
| **wp-load** | `HeapLang.wp_load` | [`HeapLang/SswpLogic.lean`](Trillium/HeapLang/SswpLogic.lean) | `wp_load` | |
| **wp-store** | `HeapLang.wp_store` | [`HeapLang/SswpLogic.lean`](Trillium/HeapLang/SswpLogic.lean) | `wp_store` | |
| **wp-cas** | `HeapLang.wp_cmpxchg_suc`, `HeapLang.wp_cmpxchg_fail` | [`HeapLang/SswpLogic.lean`](Trillium/HeapLang/SswpLogic.lean) | `wp_cmpxchg_suc`, `wp_cmpxchg_fail` | `cas` is `Snd (CmpXchg …)`; the disjunctive rule of the paper is split in two. |
| **wp-beta** | `sswp_pure_step` with the `PureExec` instance `pure_beta` | [`HeapLang/SswpLogic.lean`](Trillium/HeapLang/SswpLogic.lean), [`HeapLangDefs.lean`](Trillium/HeapLang/HeapLangDefs.lean) | `sswp_pure_step`, `pure_beta` | |
| `wp_E nondet ⟨w. ∃n. w = n⟩` (§4.2.2) | `HeapLang.wp_choose_nat` | [`HeapLang/SswpLogic.lean`](Trillium/HeapLang/SswpLogic.lean) | `wp_choose_nat` | `nondet ()` is HeapLang's `ChooseNat`. |
| Proof-mode tactics used in the examples | `wp_pure`, `wp_pures`, `wp_bind`, `wp_load`, `wp_store`, … | [`Fairis/ProofMode.lean`](Trillium/Fairis/ProofMode.lean) | `proofmode.v` | Each pure/heap step consumes one unit of fuel, as `wp-step-fuel` does. |

The language (an OCaml-like HeapLang with locales) is [`HeapLang/Lang.lean`](Trillium/HeapLang/Lang.lean); programs are
written with the `tl(…)` / `tl_val(…)` notation of [`HeapLang/Notation.lean`](Trillium/HeapLang/Notation.lean).

### §4.2 Examples

#### §4.2.1 Fair termination: Yes-No (Figs. 3, 4)

| Paper | Lean (`Trillium.Fairis.Yesno`) | Lean file | Rocq |
|---|---|---|---|
| Fig. 3 `yes`, `no`, `yn_start` | `yesGo`, `yes`, `noGo`, `no`, `start` | [`Examples/Yesno/Yesno.lean`](Trillium/Fairis/Examples/Yesno/Yesno.lean) | `yes_go`, `yes`, `no_go`, `no`, `start` |
| Fig. 4 `M_yes_no` | `YN` (roles), `YnTrans`, `theFairModel`, `theModel` (its `LiveModel`) | same | `YN`, `yntrans`, `the_fair_model`, `the_model` |
| `γ_yes`, `γ_no` resources | `yesAt`, `noAt`, `authYesAt`, `authNoAt` | same | `yes_at`, `no_at`, `auth_yes_at`, `auth_no_at` |
| `yesno_inv(γ_yes, γ_no, ℓ)` | `yesnoInv`, `yesnoInvInner` | same | `yesno_inv`, `yesno_inv_inner` |
| Specs of the two threads; main spec | `yes_spec`, `no_spec`, `start_spec` | same | `yes_spec`, `no_spec`, `start_spec` |
| Fair termination of the model (local criterion) | instance `the_model_terminates : FairTerminatingModel theFairModel`, `theDecreasingRole` | [`Examples/Yesno/YesnoAdequacy.lean`](Trillium/Fairis/Examples/Yesno/YesnoAdequacy.lean) | `the_decreasing_role` |
| Model is finitely branching (so ξ is relatively image-finite) | `steppable`, `model_finitary` | same | `steppable`, `model_finitary` |
| **Result**: the program fairly terminates | `yesno_terminates` | same | `yesno_terminates` |

Differences: the specs require fuel `f > 50` (cap 61) instead of the paper's illustrative 42, and `start N` needs `N > 1`.
The theorem takes `(GF) [HeapGpreS theModel GF] [YesnoPreG GF]` instead of the concrete `yesnoΣ`.

#### §4.2.2 Sound infinite branching: non-deterministic nat (Figs. 6, 7)

| Paper | Lean (`Trillium.Fairis.ChooseNat`) | Lean file | Rocq |
|---|---|---|---|
| Fig. 6 `decr_loop`, `nondet_start` | `decrLoopProg`, `chooseNatProg` | [`Examples/ChooseNat/ChooseNat.lean`](Trillium/Fairis/Examples/ChooseNat/ChooseNat.lean) | `decr_loop_prog`, `choose_nat_prog` |
| Fig. 7 model (`∞`, `0`, `1`, …) | `CN`, `CnTrans`, `cnFairModel`, `cnModel`; termination instance `cn_model_terminates` (`cnDecreasingRole`) | same | `CN`, `cntrans`, `cn_fair_model`, `cn_model`, `cn_decreasing_role` |
| `ξ^ℓ_nondet` | `ξCn` | same | `ξ_cn` |
| `nondet_inv(γ, ℓ)` | `chooseNatInv`, `chooseNatInvInner` | same | `choose_nat_inv`, `choose_nat_inv_inner` |
| Spec of `nondet_start` | `choose_nat_spec`, `decr_loop_spec` | same | `choose_nat_spec`, `decr_loop_spec` |
| Refinement (relative image-finiteness via ξ) | `choose_nat_sim` | [`Examples/ChooseNat/ChooseNatAdequacy.lean`](Trillium/Fairis/Examples/ChooseNat/ChooseNatAdequacy.lean) | `choose_nat_sim` |
| **Result**: fair termination | `choose_nat_terminates` | same | `choose_nat_terminates` |

#### §4.2.3 Liveness beyond termination: Even-Odd (Figs. 8, 9)

| Paper | Lean (`Trillium.Fairis.EvenOdd`) | Lean file | Rocq |
|---|---|---|---|
| Fig. 8 `incr_loop`, `eo_start` | `incrLoop`, `start` | [`Examples/EvenOdd/EvenOdd.lean`](Trillium/Fairis/Examples/EvenOdd/EvenOdd.lean) | `incr_loop`, `start` |
| Fig. 9 model | `EO` (roles), `EOTrans`, `theFairModel`, `theModel` | same | `EO`, `eotrans`, `the_fair_model`, `the_model` |
| `EO_inv(γ_e, γ_o, ℓ)` | `evenoddInv`, `evenoddInvInner` | same | `evenodd_inv`, `evenodd_inv_inner` |
| Thread specs; main spec | `incr_loop_spec`, `even_go_spec`, `odd_go_spec`, `start_spec` | same | same names |
| `ξ^ℓ_even_odd = ξ_steps ∧ ξ^ℓ_match` | `ξEvenodd` = `ξEvenoddNoValSteps` ∧ `ξEvenoddModelMatch` | [`Examples/EvenOdd/EvenOddAdequacy.lean`](Trillium/Fairis/Examples/EvenOdd/EvenOddAdequacy.lean) | `ξ_evenodd`, `ξ_evenodd_no_val_steps`, `ξ_evenodd_model_match` |
| `evenodd_prop_mdl` (model satisfies the property) | `evenoddMdlProgress`, `evenoddMdlMono`; `evenodd_mdl_progresses`, `evenodd_mdl_is_mono` | same | same names |
| `maximal(τ)` | `ExtraceMaximal` | same | `extrace_maximal` |
| Refinement | `evenodd_sim` | same | `evenodd_sim` |
| **Result**: `evenodd_prop(ℓ, c)` (all numbers visited ∧ monotone) | `evenodd_ex_liveness` (conclusion `evenoddExProgress l extr ∧ evenoddExMono l extr`) | same | `evenodd_ex_liveness` |

Differences: `ξ_steps` is stated in the code as "not all threads are values, and no thread is stuck"
(`ξEvenoddNoValSteps`), which implies the paper's "some locale can step".

## §5 The Aneris logic, §5.1 TLA⁺ refinements (Paxos, two-phase commit), CRDT appendix

**Not in this repository.** The Aneris instantiation of Trillium and its case studies (single-decree Paxos,
two-phase commit, the CRDT of the appendix) are not part of the logsem/trillium development that was ported.
Theorem 5.1 and Corollary 5.2 therefore have no Lean counterpart here.

## Summary

| Paper result | Lean |
|---|---|
| Def. 2.2 / Lemma 2.4 | `ContinuedSimulation` / `produced_inf_aux_trace_valid_inf` |
| Def. 2.6 / Thm. 2.7 | `RelFinitary` / `simulation_correspondence` |
| Thm. 3.2 (Trillium adequacy) | `wp_strong_adequacy`, `sim_and_adequacy_xi` |
| Thm. 4.1 (Fairis adequacy) | `strong_simulation_adequacy`, `simulation_adequacy` |
| Lemma 4.2 | inside `strong_simulation_adequacy` |
| Lemma 4.3 | `fairness_preserved` (+ `upto_stutter_fairness`) |
| §4.2.1 / §4.2.2 / §4.2.3 | `yesno_terminates` / `choose_nat_terminates` / `evenodd_ex_liveness` |
| Thm. 5.1, Cor. 5.2 | not in this development |

All of the Lean results above are proved without `sorry`; their axioms are `propext`, `Classical.choice`
and `Quot.sound` (`#print axioms`).
