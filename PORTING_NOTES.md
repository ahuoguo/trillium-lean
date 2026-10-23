# Trillium → Lean porting notes (conventions for all porting work)

Source (READ ONLY): `/Users/byc/Downloads/trillium/` (Rocq, Iris 4.3, stdpp 1.11, paco).
Target: this Lean 4 project (`/Users/byc/Downloads/lean-stuff/trillium-lean`), Lean v4.35.0,
depending on **iris-lean** (local, `../iris-lean/Iris`, READ ONLY) and **Mathlib** v4.35.0.

**Never run git or any VCS command. Never modify iris-lean, Mathlib, or the Rocq sources.**

## Build

- Build one module: `lake build Trillium.ProgramLogic.Language` (from the project root).
- Quick check of a single file whose imports are already built: `lake env lean Trillium/Foo/Bar.lean`.
- Other agents work concurrently on *other* files. Only edit files you were assigned, plus
  `Trillium.lean` (append your imports; keep it sorted; re-read it right before editing because others
  edit it too). Do not run a bare `lake build` of everything; build only your modules.
- Correspondence report: `python3 scripts/check_correspondence.py --no-build` after
  `lake exe dumpPortingData` (only needs the modules built). You can grep `CORRESPONDENCE.md` for
  your Rocq file to see what's still missing.

## iris-lean reference

- Proof-mode tactics: `../iris-lean/docs/tactics.md`, `../iris-lean/docs/proofmode.md`. Read them before
  writing proof-mode proofs (`iintro`, `icases`, `iapply`, `imod`, `iframe`, `iloeb`, `isplit` …).
- Style: `../iris-lean/Iris/style.md`. Also the iris-port plugin notes:
  `/Users/byc/.claude/plugins/cache/iris-lean/iris-port/0.1.0/notes/{RULES,STYLE_EXTENSIONS,IPROP_QUIRKS,ALGEBRA_QUIRKS}.md`
  (note: the alias syntax there is outdated — use the attribute form below).
- Good templates: `../iris-lean/Iris/Iris/ProgramLogic/*.lean` (Iris' own WP, lifting, adequacy, ectx
  languages), `../iris-lean/Iris/Iris/HeapLang/*.lean`, `../iris-lean/Iris/Iris/BI/Lib/GenHeap.lean`,
  `../iris-lean/Iris/Iris/Instances/Lib/*.lean` (FUpd, invariants, ghost maps).
- Reuse iris-lean whenever Trillium re-uses Iris (OFE/CMRA/auth/excl/agree/gmap-view algebras, `IProp`,
  `BundledGFunctors`, `ElemG`, `iOwn`, fancy updates (`InvGS_gen`, `HasLC`), `step_fupdN`, `fixpoint`,
  big ops, `Stuckness`, `ToVal`, `CoPset`, namespaces …). Do not duplicate them.

## File layout & namespaces

One Lean file per Rocq file, CamelCase path, e.g. `trillium/program_logic/ectx_language.v` →
`Trillium/ProgramLogic/EctxLanguage.lean`; `heap_lang/lang.v` → `Trillium/HeapLang/Lang.lean`;
`fairness/utils_maps.v` → `Trillium/Fairness/UtilsMaps.lean`; `fairis/fuel.v` → `Trillium/Fairis/Fuel.lean`;
`fairis/examples/yesno/yesno.v` → `Trillium/Fairis/Examples/Yesno/Yesno.lean`.
(Exception: `trillium/program_logic/adequacy.v` is split: its pure, WP-free part (thread-pool / locale
lemmas such as `locales_equiv*`, `from_locale*`, `locales_of_list*`, `valid_exec_length`, …) lives in
`Trillium/ProgramLogic/AdequacyLocales.lean`, the rest in `Trillium/ProgramLogic/Adequacy.lean`.)

Root namespace `Trillium`; sub-namespaces `Trillium.HeapLang`, `Trillium.Fairness`, `Trillium.Fairis`
(more specific namespaces inside files are fine). Plain Lean files (do **not** use the `module` keyword).
Header:
```lean
/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import ...

/-!
# <title>
Port of `trillium/program_logic/language.v`.
<short description + any representation decisions>
-/
```

## Correspondence annotations (MANDATORY — this is how completeness is checked)

`scripts/check_correspondence.py` parses every named Rocq declaration (`Definition`, `Lemma`,
`Theorem`, `Instance`/`Global Instance` with a name, `Class`, `Record`, `Inductive`, `CoInductive`,
`Fixpoint`, `CoFixpoint`, `Corollary`, `Fact`, `Axiom`, `Canonical Structure`, …) and requires each to be
either aliased or ignored. Names are prefixed by package:

| Rocq root | alias prefix |
|---|---|
| `trillium/…` | `trillium.` |
| `heap_lang/…` | `trillium.heap_lang.` |
| `fairness/…` | `trillium.fairness.` |
| `fairis/…` | `trillium.fairis.` |

Rocq `Module M` adds `M.` (Sections add nothing). E.g. `heap_lang/lang.v` has `Module heap_lang`, so its
`to_of_val` is `trillium.heap_lang.heap_lang.to_of_val`. If the same prefixed name occurs in several
Rocq files, each occurrence is additionally qualified by the file stem, e.g.
`trillium.language.locale_fill` vs `trillium.heap_lang.lang.locale_fill`… **Check the exact expected
name** in `CORRESPONDENCE.md` (search for your Rocq file) — it lists every expected key.

- Ported declaration: `@[rocq_alias trillium.wp_strong_mono] theorem wp_strong_mono ...`
  (several Rocq names → one Lean decl: `@[rocq_alias a, rocq_alias b]`). Fields of a structure/class:
  `attribute [rocq_alias trillium.foo] Bar.foo`.
- Deliberately not ported: `#rocq_ignore trillium.foo "reason"` (e.g. "Lean core `Classical.em`",
  "Rocq `Proper` instance; derivable from `NonExpansive`", "seal/unseal machinery not used in Lean",
  "Rocq-specific tactic support"). Reasons must be honest and specific.
- Whole file not ported: `#rocq_ignore_file trillium.prelude "classical.v" "reason"` (directory argument
  = `trillium.<subdir>` | `trillium.heap_lang` | `trillium.fairness` | `trillium.fairis` |
  `trillium.fairis.examples` with file `yesno/yesno.v`).
- If a Trillium declaration is literally the same as an existing iris-lean/Mathlib/core declaration, reuse it
  instead of duplicating, and record the link on the existing constant:
  `attribute [rocq_alias trillium.heap_lang.loc] Iris.HeapLang.Loc` (or `#rocq_ignore … "same as iris-lean X"`).
- Correspondence check without clobbering other agents' output: build your modules, then
  `lake exe dumpPortingData $TMP/p.json && python3 scripts/check_correspondence.py --no-build --json $TMP/p.json -o $TMP/c.md`
  (`$TMP` = your own scratch directory; unbuilt modules are skipped automatically).
- Notations, `Ltac`s, `Arguments`, `Hint`s, anonymous instances are not tracked; port them only as needed
  (Ltac → Lean tactic macro if it's used by downstream proofs).

## Representation decisions (shared — do not deviate without good reason)

- **Classical logic**: Lean's `Classical` (`Classical.em`, `Classical.choice`, `Classical.byContradiction`,
  `propext`, `funext`, `Classical.dec`). Trillium's axioms file is replaced by these.
- **stdpp `gmap K V` / `gset K`** → `Trillium.GMap K V` / `Trillium.GSet K` from `Trillium/Std/Maps.lean`
  (= `Std.ExtTreeMap K V compare` / `Std.ExtTreeSet K compare`, as iris-lean's HeapLang does). Keys need
  `[Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]` (replaces `EqDecision K, Countable K`). Use the core
  `Std.ExtTreeMap`/`Std.ExtTreeSet` API (`m[k]?`, `insert`, `erase`, `filter`, `keys`, `ext_getElem?`, …)
  or iris-lean's `Iris.Std.PartialMap`/`LawfulSet` API, whichever gives cleaner proofs.
  `gmultiset` → Mathlib `Multiset`. `coPset` → iris-lean `CoPset`. `list` → `List`, `Z` → `Int`,
  `positive` → `Nat` or iris-lean `Pos` as appropriate, `string` → `String`.
- **stdpp classes**: `EqDecision` → `DecidableEq`, `Decision P` → `Decidable P`, `Inhabited` → `Inhabited`
  / `Nonempty`, `Countable` → Mathlib `Encodable`/`Countable` (only where actually needed), `Finite` →
  Mathlib `Fintype`/`Finite`, `Inj` → `Function.Injective`, `rtc` → `Relation.ReflTransGen`,
  `relations.nsteps` → a local `Nat`-indexed inductive or Mathlib `Relation` API.
- **Coinductive predicates** (`CoInductive … : Prop`, `paco1/paco2` definitions): use Lean's
  `coinductive` command (works in v4.35: `coinductive Foo : α → Prop where | c … : … → Foo x`, gives
  `Foo.coinduct`). Paco proofs (`pcofix`, `pfold`, `punfold`) become ordinary coinduction with a
  suitable invariant (`Foo.coinduct _ (fun x => ∃ …, …)`). Prefer one coinductive predicate per Rocq
  definition and keep the Rocq name in the alias.
- **Coinductive data**: `inflist A` → `Stream'.Seq A` (Mathlib, possibly-infinite lists), see
  `Trillium/Traces/InfiniteTrace.lean`. The fairness `trace S L` (`tr_singl s | tr_cons s ℓ tr`) is defined in
  `Trillium/Fairness/Inftraces.lean` (built from `Stream'.Seq`), with constructor functions, a case-analysis
  lemma, and a corecursor. Downstream files must use that API.
- **Rocq `Record` with mixin** (e.g. `language`, `ectxLanguage`) → Lean `class` indexed by the expression
  type with `outParam`s for the other carriers, following iris-lean's `Iris.ProgramLogic.Language`.
- **Iris**: `iProp Σ` → `IProp GF` with `GF : BundledGFunctors`; `inG Σ A` → `ElemG GF F`;
  `own γ a` → `iOwn γ a`; `invGS_gen HasNoLc Σ` → `InvGS_gen .HasNoLc GF` (check iris-lean's spelling);
  seal/unseal → plain `def` (+ `#rocq_ignore` of the `_aux`/`_unseal` names); `Proper`/`NonExpansive`
  instances → iris-lean's `OFE.NonExpansive` etc. Typeclass `Params`/`Proper` boilerplate whose Lean
  counterpart is automatic can be ignored with a reason.

## Quality bar

- Faithful 1:1 port: same statements (modulo representation), same lemma granularity, proofs following the
  Rocq proof structure where reasonable. Port *every* declaration of your files (alias it) or ignore it with
  a specific reason. Statement changes forced by representation must be mentioned in a comment.
- No `axiom`. Avoid `sorry`. If a proof is genuinely stuck after a serious attempt, leave
  `sorry` with a `-- TODO(port): <what's missing>` comment and report it — the correspondence report
  flags sorry-dependent declarations. Never weaken a statement to make it provable.
- Mathlib naming (`snake_case` theorems, `lowerCamelCase` defs, `UpperCamelCase` types/classes).
  Lean names may differ from Rocq names; the alias records the link.
- Every file must compile without errors when you finish (warnings OK, but avoid noisy ones).

## Learned API facts (appended as agents report)

- `Std.ExtTreeMap` union `m₁ ∪ m₂` is **right-biased** (stdpp's `∪` on gmap is left-biased). Equal for
  disjoint maps; elsewhere swap arguments or use `mergeWith`.
- `Trillium/Fairis/MapIncludedUtils.lean` defines stdpp's `optionRelation`, `mapRelation`, `mapIncluded`
  (namespace `Trillium`, key-indexed relations as in stdpp) and Trillium's `mapAgreeR`. stdpp notation
  translations used there: `f <$> m` = `m.map fun _ => f`; `filter P m` = `m.filter fun k x => decide (P (k,x))`;
  `<[i:=x]>m` = `m.insert i x`; `delete k m` = `m.erase k`; `dom m1 ⊆ dom m2` = `∀ k, k ∈ m1 → k ∈ m2`.

### Language layer API (`Trillium/ProgramLogic/{Language,EctxLanguage,EctxiLanguage}.lean`)

- Do NOT `open Iris.ProgramLogic` wholesale (`Language` clashes); use `open Iris.ProgramLogic (ToVal EvContext EvContextOps)`.
- `class LanguageCore (Expr) (State Locale : outParam)`: `configStep`, `localeOf` (exported), `locale_equiv`,
  `locale_injective`. `configStep` needs `(Expr := E)` explicitly.
- `class Language (Expr) (Val Ectx State Locale : outParam) extends ToVal Expr Val, EvContext Expr Ectx, LanguageCore …`
  with `primStep e σ e' σ' efs` (exported `Trillium.primStep`), fields `val_stuck`, `fill_not_val`, `fill_step`,
  `fill_step_inv`, `ectx_fill_positive`, `locale_step_preserve`, `locale_fill`.
- `class EctxLanguage …` (`headStep`), `class EctxiLanguage (Expr) (Val EctxItem State Locale : outParam)` (`fillItem`);
  declaring only an `EctxiLanguage` instance gives `EctxLanguage` and `Language` automatically
  (contexts = `List EctxItem`, `fill_nil`, `fill_cons`, `fill_append` simp lemmas).
- `toVal` exported; `ofVal` = `ToVal.ofVal`, coercion `↑v`; `ToVal.toVal_coe`, `ToVal.coe_of_toVal_eq_some`.
  `fill` = `EvContext.fill` (exported `Trillium.fill`), `EvContext.fill_empty`, `EvContext.fill_comp`, `EvContextOps.empty/comp`.
- `is_Some (to_val e)` ↦ `(toVal e).isSome`. `Atomicity` = iris-lean `Iris.ProgramLogic.Language.Atomicity`.
  `relations.nsteps` ↦ `Relation.Iterate`, `rtc` ↦ `Relation.ReflTransGen`.
- In `Trillium.Language`: `Reducible e σ`, `Irreducible`, `Stuck`, `NotStuck`, classes `Atomic a e`, `StutteringAtomic a e`,
  `Step ρ ρ'` (ctors `.atomic t1 t2 h`, `.state t h`), `LocaleStep ρ ol ρ'`, `NSteps`, `PureStep` (fields `safe`, `det`),
  `PureStepsTp`, `class PureExec (φ) (n) e1 e2` (`@[ipm_class]`, field `pure_exec`), `IntoVal`, `AsVal`.
- Top level: `prefixesFrom`, `prefixes`, `mem_prefixesFrom_iff`, `LocalesEquiv t t'`, `Cfg E := List E × State`.
- Locations: iris-lean `Iris.HeapLang.Loc` reused (offset `l + i`, `i : Int`); `Trillium.HeapLang.freshLocs`.

### Traces API (`Trillium/Traces/*.lean`, `Trillium/Algebra/Trace.lean`)

- `inflist A` = `Stream'.Seq A` (abbrev `InfList`); `inflist_take n il` = `il.take n`, `inflist_drop n il` = `il.drop n`
  (argument order swapped). `InfList.eq_nil_or_cons`, `InfList.take_add`, `drop_add`, `SameLength`.
- `FiniteTrace A L`: ctors `.singleton a`, `.extend ft ℓ a` (DecidableEq). Scoped notations (in `namespace Trillium` /
  `open Trillium`): `{tr[a]}`, `ft :tr[ℓ]: a`, `ft +trl+ l`. `FiniteTrace.first/last` (simp), `StartsIn`, `EndsIn`
  (`startsIn_iff`, `endsIn_iff` simp), `appendList`, `IsPrefix` (also `≤`), `Contract`, `length`,
  `lookup` (Rocq `ft !! i`). `TraceSteps R ex` (`.singleton`, `.step`, `.step_inv`, …), `TraceSteps2`,
  `TraceForall{,2,3}`.
- `Eventually` inductive (`.now`, `.later`); `Always` coinductive (`.continued`). Prove with
  `Always.coinduct ψ P step f inftr hP`; destruct with `h.dest` or `cases h` (rcases patterns don't work on
  coinductive predicates).
- `TraceAlg A L` (`.trace ft`, `.bot`), discrete CMRA, `TraceAlg.local_update`.

### Prelude API (`Trillium/Prelude/*.lean`)

- Classical: `epsilon`→`Classical.choose`, `ExcludedMiddle`→`Classical.em`, `NNP_P`→`Classical.not_not.mp`,
  `not_forall_exists_not`→`Classical.not_forall.mp`, `make_decision`→`Classical.dec`; stdpp `ProofIrrel` hypotheses dropped.
- `GFX Ψ`, `PredMonotone Ψ`, `GFX.post_fixpoint`, `GFX.fixpoint`, `GFX.coind`.
- `SmallerCard A B`, `forall_exists_swap`, `nat_regular`. stdpp `Finite A` ↦ Mathlib `Finite A` (Prop);
  `finite_smaller_card_nat`, `smaller_card_nat_finite`, `in_list_finite`, `in_gset_finite`, gmap enumerations
  (`enumGmapBounded`, `enumGmapRangeBounded`, `enumerateDomGsets`, …).
- Map/set conventions: `dom m = D` ↦ `∀ k, k ∈ m ↔ k ∈ D`; `elements D` ↦ `D.toList`; `≡ₚ` ↦ `List.Perm`.
- IrisExtraction (for `UPred M`, so `IProp GF`): `extract_forall`, `extract_exists (Hcard : SmallerCard A ℕ)`,
  `extract_and/or/pure/later/except_0/bupd/sep ([IncOrd M])/own/valid/internal_eq (↔ x = y)`.

### HeapLang API (`Trillium/HeapLang/{Lang,Notation,Tactics}.lean`, namespace `Trillium.HeapLang`)

- Reuses iris-lean `Iris.HeapLang.{Loc, Binder, BaseLit, UnOp, BinOp, ProphId}`. New mutual `Expr`/`Val`
  (`.val`, `.var`, `.rec_`, `.app`, …, `.chooseNat`; `Val.lit/rec_/pair/injL/injR`). Simp normal form for values:
  `Expr.val v` (`ofVal_eq_val`, `toVal_eq`).
- `structure State` (`heap : GMap Loc Val`, `usedProphId : GSet ProphId`), `State.updHeap`, `heapArray`,
  `State.initHeap σ l n v = σ.heap ∪ heapArray …` (args swapped: right-biased union).
- `ECtxItem` (+ `.fill`), `Expr.substStr`, `Expr.subst (b : Binder)`. Head step relation is named `BaseStep`
  (ctors `recS`, `betaS`, `allocNS`, `loadS`, `storeS`, `cmpXchgS`, `faaS`, `chooseNatS`, `forkS`, …).
- Locale = `Nat`, `localeOf c e = c.length` (`localeOf_eq`). Instance `instEctxiLanguage : EctxiLanguage Expr Val
  ECtxItem State BaseLocale`; abbrevs `heapEctxLang`, `heapLang`.
- Notation: `tl(…)`, `tl_val(…)` (NOT `hl(…)`, which is iris-lean's), e.g.
  `tl_val(rec yes_go n b := (if cas(b, #true, #false) then n ← !n - #1 else #()); if #0 < !n then yes_go n b else #())`,
  `tl_val(λ N b, let n := alloc(N); v(&yesGo) n b)`; `&t` embeds a Lean term, `v(…)` a value.
- `Tactics.lean`: `findECtx e pred` / `findECtxRev` (port of `reshape_expr`), usable in `ProofModeM`.

### Fairness API (`Trillium/Fairness/*.lean`, namespace `Trillium.Fairness`; `open Trillium.Fairness Trace`)

- `structure Trace (S L) where first : S; steps : Stream'.Seq (L × S)` (`@[ext]`). `Trace.singl s` (`⟨s⟩ₜ`),
  `Trace.cons s ℓ r` (`s -[ℓ]-> r`). `cases tr with | singl s => … | cons s ℓ r => …` works (custom eliminator);
  `rcases/obtain` do NOT. `Trace.singl_or_cons`, `Trace.dest`, `cons_inj`, `singl_ne_cons`, `Trace.corec` (+`corec_eq`),
  `Trace.eq_of_bisim`.
- `after n tr : Option Trace` (`after_0_id`, `after_succ_cons`, `after_sum`), `predAt tr n P`, `infiniteTrace`,
  `terminatingTrace`, `traceLenIs tr len` (`NatOmega`: `.infinity`/`.num n`).
- Coinductive `TraceValid trans tr`, `TracesMatch …`, `ExecTraceMatch ft il tr`: build with `X.coinduct _ pred step _ h`
  or ctors; invert ONLY via `TraceValid.inv`, `trace_valid_cons_inv`, `TracesMatch.inv/.cons_inv/...`, `ExecTraceMatch.inv`
  (`cases h` fails on cons indices). `toTrace s il = ⟨s, il⟩`, `fromTrace tr = tr.steps`.
- Maps (`Trillium.GMap`): `dom m : GSet K` (`mem_dom`), `HasSubset` instance (`subseteq_def`), `Disjoint` (`##ₘ`),
  `singleton`, `getElem?_insert_ite`, `img`; `m ⇂ R` scoped notation. Sets: iris-lean `LawfulSet`/`FiniteSet` API on `GSet`;
  `GSet.toGMap b X` (gset_to_gmap); `Ord (GSet K)` instances exist. iris-lean generic map CMRA instances need the type
  written `(Std.ExtTreeMap K · compare) V` rather than `GMap K V`.
- `nsteps` = `Relation.Iterate`, `clos_trans` = `Relation.TransGen`, `Minimal` = `IsLeast`, `positive` = `ℕ+`.
- Do NOT redefine `GMap.dom`, `HasSubset (GMap …)`, `Ord (GSet …)`, or a global `OFE Nat` (scoped `add_monoid` exists).

### Program-logic traces / events / AdequacyLocales API (namespace `Trillium`)

- `structure Model` (`mstate`, `mlabel`, `mtrans`), `CoeSort Model (Type _)`.
- `ExecutionTrace Expr` = `FiniteTrace (List Expr × State) (Option Locale)`, `AuxiliaryTrace M`,
  `InfExecutionTrace Expr` = `Stream'.Seq (Option Locale × (List Expr × State))`, `InfAuxiliaryTrace M`.
  Case on Seq abbrevs via `rcases InfList.eq_nil_or_cons iex with rfl | ⟨⟨ζ, c⟩, iex, rfl⟩`.
- `ValidExec ex` (= `TraceSteps LocaleStep ex`; `.singleton`, `.extend`, `.extend_inv`), `ValidSystemTrace`.
- `ContinuedSimulation φ ex atr` (= GFX …), `continuedSimulation_unfold`, prove via `GFX.coind`;
  `ContinuedSimulation.rel/.impl/.next_aux_state_exists`, `simulation_does_continue`.
- `ValidInfExec ex iex` (coinductive; `.coinduct`, destruct via `ValidInfExec.cons_inv` or `rw [ValidInfExec.eq_def] at h`),
  `ValidInfSystemTrace`, `produceInfAuxTrace`, `produced_inf_aux_trace_valid_inf`.
- Events: `Event Expr`, `EventObservation`, `TraceHasEvents`, `eventsOfTrace`.
- AdequacyLocales: `LocalesEquivFrom`, `localesOfListFrom`, `localesOfList`, `locales_of_list_equiv`,
  `fromLocaleFrom`, `fromLocale tp ζ : Option Expr` (`[DecidableEq Locale]`), `LocalesEquivPrefix`, `RelFinitary`,
  `AdequateMultiple`, `Adequate`, `WpAdequacyRelation`.

### Locale helpers API

- `Trillium.Fairness`: `localesOfCfg c : GSet Locale`, `mem_localesOfCfg_iff`, `stepFork`, `extrLastFork`,
  `locale_step_from_locale_src`.
- `Trillium.HeapLang`: `fromLocale_eq_some_iff : fromLocale tp tid = some e ↔ tp[tid]? = some e`,
  `localesOfCfg_eq_setSeq`, `mem_localesOfCfg_iff_lt`, `locale_step_fresh_exact`, `locale_step_fork_some`,
  `locales_equiv_of_length_eq`. Trap: `omega` doesn't see through `BaseLocale` (abbrev for `Nat`); `change Nat at x` first.

### Fairness models API (`Trillium/Fairness/{TraceUtils,TraceLookup,Fairness,TraceHelpers,TracesMatch}.lean`)

- `FairModel`: fields `fmstate : Type`, `fmrole : Type`, `fmtrans`, `liveRoles : fmstate → GSet fmrole`, `fm_live_spec`;
  instance fields `fmstate_eqdec`, `fmstate_inhabited`, `fmrole_eqdec`, `fmrole_inhabited`, `fmrole_ord`/`_transOrd`/`_lawfulEqOrd`
  (fill with `ordOfEncodable` etc. for Encodable roles). `CoeSort FairModel Type`, `FairModel.toModel` (mlabel = Option role).
- `Extrace Expr` = `Trace (List Expr × State) (Option Locale)`; `ExtraceValid` coinductive (invert via `.inv`/`.cons_inv`).
  `localeEnabled`, `fairEx ζ extr`, `ExtraceFairlyTerminating`, `fairBy`, `fairByGen`, `weaklyFair`, `Mtrace M`,
  `roleEnabledModel`, `fairModelTrace ρ mtr`, `MtraceValid`.
- Lookups: `traceLookup`, `stateLookup`, `labelLookup`; scoped notations `tr !! i`, `tr S!! i`, `tr L!! i`;
  reduce to `after` via `traceLookup_eq`/`stateLookup_eq`/`labelLookup_eq` (not global simp). `after_succ` loops in simp.
- Rocq record fields are not tracked by the checker: don't alias them.
- On `Mtrace Mdl` / other abbrevs of `Trace`, the custom eliminator doesn't fire: use
  `cases tr using Trace.casesOn' with | singl s => … | cons s ℓ r => …`.
- `FairTerminatingModel` (`Trillium/Fairis/FairTermination.lean`): `ftmLeq`, `ftm_order`, `ftm_wf`, `ftmDecreasingRole`,
  `ftm_decr`, `ftm_decreasing_role_preserved`, `ftm_notinc`; `fair_terminating_traces_terminate`, `MtraceFairlyTerminating`.

### WP API (`Trillium/BI/WeakestPre.lean`, `Trillium/ProgramLogic/{WeakestPre,Lifting,EctxLifting,Atomic}.lean`)

- `class IrisG (Expr : outParam) {Val Ectx State Locale : outParam} [Language …] (M : outParam Model) (GF)` with
  `[invGS : InvGS_gen .hasNoLC GF]`, `stateInterp : ExecutionTrace Expr → AuxiliaryTrace M → IProp GF`,
  `forkPost : Locale → Val → IProp GF` (exported). `stateInterp (GF := GF) …` when GF isn't fixed by context.
- WP: `WP e @ s; ζ; E {{ v, Φ }}`, `WP e @[ζ] E {{ … }}`, `WP e @[ζ] E ? {{ … }}`, `WP e @[ζ] {{ … }}`; Texan
  `{{ P }} e @[ζ] E {{ RET v; Q }}`. Instance `wp.def`, `Wp.wp s E ζ e Φ`.
- `|~{ E1 , E2 }~| P`, `|~{ E }~| P`, `|~~| P` (`preStep`); `imod`/`imodintro` work.
- `wp_unfold` (use `.to_eq`, prefer `ieval (rewrite [wp_unfold.to_eq])`), `wp_strong_mono`, `fupd_wp`, `wp_bind (K : Ectx)`,
  `wp_value'`, `wp_stuttering_atomic`, `wp_lift_*`, `wp_pure_step_later`, `AllowsStuttering M GF` / `AllowsPureStep M GF`
  (use wrappers `stutteringLabel GF`, `pureLabel GF`, `allowsStuttering`, `allowsPureStep`).

### Fairis fuel API (`Trillium/Fairis/{Destuttering,Fuel,FuelTermination,FairnessFiniteness}.lean`)

- `UptoStutter Us Ul` (union of post-fixpoints; `h.unfold`, `UptoStutter.fold`, `UptoStutter.coind`).
- `LiveStateData Locale M` (`lsUnder`, `lsMap : GMap Locale (GMap M.fmrole Nat)`), `LiveState Locale M` (+ `ls_map_disj`,
  `ls_map_live`); `lsFuel δ`, `lsMapping δ` take `LiveStateData` (write `(δ : LiveStateData _ _)`);
  `lsFuel_getElem?_eq_some_iff`, `lsMapping_getElem?_eq_some_iff`, `ls_same_doms`.
- `FairLabel Role Locale` (`.takeStep ρ ζ`, `.silentStep ζ`, `.configStep`), `lsTrans`, `MustDecrease`.
- `structure LiveModel Locale M` (field `lmFl`), parametrised by Locale (not Λ); `LM.lmLs`, `LM.lmLbl`, `LM.lmLsTrans`,
  `LM.toModel` (CoeOut to Model). `initialLs LM s0 ζ0`, `labelsMatch`, `Auxtrace LM`, `AuxtraceValid LM`,
  `ExauxTracesMatch Expr LM`, `validLiftFairness LM φ`, `fairness_preserved`, `upto_stutter_fairness`,
  `continued_simulation_fair_termination`, `valid_state_evolution_finitary_fairness`, `simRel`, `simRelWithUser`.
- Traps: `autoImplicit` is on — annotate binder types in `∃ ζ fs, …`; avoid `rfl` patterns on `ζ1 = ζ`, use `subst`.

### HeapLang program-logic API (`Trillium/HeapLang/{HeapLangDefs,HeapLangDefsPosts,SswpLogic}.lean`)

- `class Heap1GpreS GF` (`heap1GpreS_gen_heap : genHeapPreS Loc Val GF HeapF`), `class Heap1GS GF`
  (`heap1_gen_heapGS : genHeapGS Loc Val GF HeapF`), `heap1GF`. `HeapF` = iris-lean `Iris.HeapLang.HeapF` (= `GMap Loc ·`).
- Points-to: iris-lean `l ↦ v`, `l ↦{dq} v` with `dq : DFrac` — Trillium's `l ↦{q} v` is `l ↦{.own q} v`.
  `genHeapInterp (H := HeapF) σ.heap`, `metaToken (V := Val) l E`; `genHeap_valid'`, `genHeap_update'`, `genHeap_alloc_initHeap`.
- `PureExec` instances `pure_beta` (via `[AsRecV v f x erec]`), `pure_eqop`, `pure_unop_getD`, `pure_binop_getD`
  (`pure_unop`/`pure_binop` are theorems: out-param result). `*_atomic` instances; macros `solve_atomic`, `solve_pure_exec`.
- `sswp s E e Φ` (Φ : Expr → IProp), unfold via `sswp_eq_of_toVal_none`; `sswp_wand`, `sswp_fupd`, `sswp_pure_step`,
  `wp_allocN_seq`, `wp_alloc`, `wp_choose_nat`, `wp_load`, `wp_store`, `wp_cmpxchg_fail/suc`, `wp_faa` (all stated on `sswp`).
- Posts: `postsOf_getElem?`, `posts_of_empty_mapping(_multiple)`.

### Adequacy API (`Trillium/ProgramLogic/Adequacy.lean`, namespace `Trillium`)

- `wptpFrom t0 s t Φs`, `wptp s t Φs`, `postsOf t Φs`, `newElems`, `newPosts`, `configWp` (Persistent), `curPosts tp e0 Φ0`,
  `relAlwaysHolds s Φs ξ c1 c2`, `relAlwaysHoldsWithTraceInv s traceInv Φs ξ c1 c2`, `relAlwaysHolds0 ξ s stateI Φ0 e1 σ1 δ1`,
  `gsim`, `fupdToBupd`.
- WP hypotheses have the form `∀ [InvGS_gen .hasNoLC GF], ⊢ |={⊤}=> ∃ stateI … forkPost, letI _ : IrisG Expr M GF :=
  { stateInterp := stateI, forkPost := forkPost }; iprop(configWp ∗ stateI {tr[([e1], σ1)]} {tr[δ1]} ∗ WP … ∗ relAlwaysHolds…)`.
- `wp_strong_adequacy[_multiple][_with_trace_inv] [InvGpreS GF] s ξ e1 σ1 δ1 (Hsc : RelFinitary ξ) H :
  ContinuedSimulation ξ {tr[([e1], σ1)]} {tr[δ1]}`; `simulation_correspondence`; `adequacy_xi … : Adequate s e1 σ1 (fun v _ => φ v)`;
  `sim_and_adequacy_xi` (∧ of both); `_multiple` variants.
- Tips: after `imod Hwp with ⟨%stateI, …⟩` do `let _ : IrisG Expr M GF := { … }`; to prove the hypothesis `iexists stateI, traceInv, Φ, fp`
  then `iframe`; `curPosts` vs `postsOf c.1 ([Φ] ++ newPosts …)`: `ieval (simp only [newPosts, newElems, List.singleton_append, List.length_singleton])`.

### Fairis resources API (`Trillium/Fairis/{Resources,ResourcesUpdates}.lean`)

- Cameras: `LocMapF Locale` (use this abbrev for map CMRAs), `ModelR M`, `FuelMapR Locale M`, `FreeRolesR M`. Locale : Type.
- `class FairnessGpreS (LM : outParam (LiveModel Locale M)) GF` (ElemG fields `model`, `fuelMapping`, `freeRoles`),
  `class FairnessGS LM GF` (`inG`, `modelName`, `fuelMappingName`, `freeRolesName`); predicates need only `(GF := GF)`.
  Allocate with `model_state_init`, `model_fuel_mapping_init`, `model_free_roles_init`, `initFuelMap LM s0 ζ0`.
- `authModelIs s`, `fragModelIs s`, `authFuelMappingIs`, `hasFuels ζ fs` (`ζ ↦M fs`), `hasFuelsS` (`ζ ↦M++ fs`), `hasFuelsPlus`,
  `authFreeRolesAre`, `fragFreeRolesAre`. `modelStateInterp tp δ`, `model_state_interp_tids_smaller`.
- `update_fuel_step`, `update_model_step`, `update_fork_step`, `has_fuels_*`, `model_agree`, `update_model`, `free_roles_inclusion`,
  `ModelCanFuelStep`, `ModelCanModelStep LM`, `ModelCanForkStep`. stdpp `S <$> fs` ↦ `fs.map fun _ f => f + 1`; `alter` ↦ `.modify`.

### Fairis lifting API (`Trillium/Fairis/Lifting.lean`; ctx `{M} {LM : LiveModel BaseLocale M} {GF} [HeapGS LM GF]`)

- `has_fuels_decr_preStep`, `has_fuels_dealloc`, `wp_role_dealloc`, `wp_step_model`, `wp_step_model_singlerole`,
  `wp_step_fuel (fs ≠ ∅)`, `wp_role_fork`. Timeless instances `hasFuelsS_timeless`, `fragModelIs_timeless`, `fragFreeRolesAre_timeless`.
- Write `hasFuelsS (GF := GF)` when GF isn't fixed; parenthesise `(tid ↦M fs)`; `rw [heapG_stateInterp_eq]`;
  WP postcondition binder must be named (`{{ _v, … }}`); `simp only [toVal_eq, to_of_val, Option.elim]`.

### Fairis adequacy API (`Trillium/Fairis/Adequacy.lean`; `variable (GF) {M : FairModel} (LM : LiveModel BaseLocale M)` — GF, LM explicit)

WPHYP := `(∀ [HeapGS LM GF], ⊢ |={⊤}=> (fragModelIs (GF := GF) s1 -∗ fragFreeRolesAre (GF := GF) (FR \ M.liveRoles s1) -∗
  hasFuels (GF := GF) 0 (GSet.toGMap (LM.lmFl s1) (M.liveRoles s1)) ={⊤}=∗ WP e1 @ s; 0; ⊤ {{ fun _ => hasFuels (GF := GF) 0 ∅ }}))`
- `simulation_adequacy [HeapGpreS LM GF] s e1 σ1 s1 FR : RelFinitary (simRel LM) → M.liveRoles s1 ≠ ∅ → WPHYP → ContinuedSimulation …`
- `simulation_adequacy_inftraces`, `simulation_adequacy_traces`, `simulation_adequacy_model_trace`,
  `simulation_adequacy_terminate` (`(∀ mtr, MtraceFairlyTerminating mtr) → … → ExtraceFairlyTerminating extr`),
  `simulation_adequacy_terminate_ftm [FairTerminatingModel M] [HeapGpreS LM GF] s e1 s1 FR extr (Hexfirst : extr.first.1 = [e1]) :
   RelFinitary (simRel LM) → M.liveRoles s1 ≠ ∅ → WPHYP → ExtraceFairlyTerminating extr`, `strong_simulation_adequacy`,
  `heap_lang_continued_simulation_fair_termination`, `HeapLangExtrace`.
- Tips: `iexact` may fail across defeq instance forms (`iOwn` vs `fragModelIs`, `@ 0` vs `@ (localeOf [] e1)`): `unfold fragModelIs; exact .rfl`.
  Manual HeapGS: `{ heap_invGS := Hinv, heap_gen_heapGS := ⟨G⟩, heap_fairnessGS := { modelName := γ1, … } }`.

### Fairis proof mode (`Trillium/Fairis/{HeapLangLM,ProofMode}.lean`) — READY

- `class HeapGpreS LM GF` (extends InvGpreS; `Heap1GpreS`, `FairnessGpreS`), `class HeapGS LM GF` (`heap_invGS`, `heap_gen_heapGS`,
  `heap_fairnessGS`); use `variable {M : FairModel} {LM : LiveModel BaseLocale M} {GF} [HeapGS LM GF]`.
  `heapG_irisG : IrisG Expr LM.toModel GF`, `heapG_stateInterp_eq`, `heapG_forkPost_eq` (forkPost tid _ = hasFuels tid ∅).
- Tactics (each pure/heap step consumes 1 fuel from the thread's `tid ↦M fs`): `wp_pure` (pattern in `tl(…)` syntax), `wp_pures`,
  `wp_rec`, `wp_lam`, `wp_if(_true/_false)`, `wp_op`, `wp_let`, `wp_seq`, `wp_proj`, `wp_case`, `wp_match`, `wp_pair`, `wp_closure`,
  `wp_bind (cas(_, _, _))` / `wp_bind (&(Expr.cmpXchg _ _ _))`, `wp_load`, `wp_store`, `wp_value_head`, `wp_finish`, `wp_expr_simp`,
  `solve_fuel_positive`, `simpl_has_fuels`. Model steps/fork/cmpxchg: `iapply wp_step_model_singlerole`, `wp_role_fork`,
  `wp_cmpxchg_suc`, … (sswp lemmas). `wp_pures` doesn't unfold defs: `unfold` first or `wp_rec`/`wp_lam`.
- Do NOT import iris-lean's `Iris.HeapLang.ProofMode` in the same file (tactic name clash).
- Worked example: see the `tests` section at the end of `Trillium/Fairis/ProofMode.lean`.

### Example-porting tips (from choose_nat)

- A global `Std.LawfulEqOrd Unit` instance `unitLawfulEqOrd` exists in `Trillium/Fairis/Examples/ChooseNat/ChooseNat.lean`;
  do NOT define another one elsewhere (import that file or define a differently-scoped one if needed).
- Example adequacy statements take `(GF) [HeapGpreS LM GF] [MyExampleG GF]` instead of a concrete `Σ`.
- `ieval (rw [h]) at H` fails: prove `have : P ⊢ Q := by rw …` then `ihave H := this $$ H`. Unfolding the LiveModel with `isimp`
  breaks the IrisG instance: use rfl-equations like `have H40 : LM.lmFl _ = 40 := rfl; isimp only [H40] at Hf`.
- `wp_pures` lacks `decide_true/false`: `isimp only [decide_false]`. Invariants defined as `def`: write an accessor via `inv_acc_timeless`.
  `iinv` on non-atomic WP: `iapply wp_preStep` + unfold `preStep`, `preStep_elim`. `localeOf [] e` → `isimp only [localeOf_eq, List.length_nil]`.
