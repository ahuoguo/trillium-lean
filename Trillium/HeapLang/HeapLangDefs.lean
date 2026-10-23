/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Iris.BI.Lib.GenHeap
import Trillium.HeapLang.Lang
import Trillium.ProgramLogic.WeakestPre

/-!
# HeapLang ghost state, atomicity and pure-step instances

Port of `heap_lang/heap_lang_defs.v` (except the `GeneralProperties` section about `posts_of`
and `cur_posts`, which lives in `Trillium/HeapLang/HeapLangDefsPosts.lean` since it depends on
the adequacy development).

## Representation

* The heap ghost state is iris-lean's `gen_heap` (`Iris.genHeapPreS`, `Iris.genHeapGS`) with
  keys `Loc`, values Trillium's `Val`, and the map type `Iris.HeapLang.HeapF`
  (`= fun V => Std.ExtTreeMap Loc V compare`, the same as `GMap Loc V`).
* Rocq's `heap1GS` has two instance fields, `heap1GpreS Σ` and `gen_heapGS loc val Σ`. In
  iris-lean `genHeapGS` extends `genHeapPreS`, so `Heap1GS GF` only stores the `genHeapGS`
  and `Heap1GS.heap1_inG` is a derived instance (this avoids an instance diamond).
* `heap1Σ` is the concrete `BundledGFunctors` `heap1GF`; `subG_heap1PreG` is subsumed by the
  instance `instHeap1GpreS_heap1GF` (in Lean, `ElemG` instances are found directly).
* The points-to connective is iris-lean's `pointsTo` with its notations `l ↦{dq} v` and
  `l ↦ v`. Trillium's notation `l ↦{q} v` (with `q` a fraction) is `l ↦{DFrac.own q} v`.
* The ghost-map operations of `gen_heap` are stated with iris-lean's generic `PartialMap`
  operations (left-biased union, `insert` via `alter`). `partialMap_insert_eq` and
  `partialMap_union_eq` translate them to core's `Std.ExtTreeMap` operations used by
  `Trillium.HeapLang.State`.
* `seq 0 n` is `List.range n`.
* `PureExec` has `φ` and `e2` as out-params, so Rocq's instances `pure_unop`/`pure_binop`
  (whose result `v'` only occurs in out-params) are theorems here; the instances used by
  automation are `pure_unop_getD`/`pure_binop_getD`. Rocq's instance priorities (`pure_eqop`
  before `pure_binop`) are kept with `priority := high`/`low`.
* The Rocq tactics `solve_atomic`/`solve_pure_exec` are ported as tactic macros, based on the
  lemmas `atomic_of_baseStep`/`pureExec_of_baseStep`. The `inv_head_step` tactic and the hints
  are replaced by `cases` on `BaseStep` in the proofs.
-/

set_option linter.dupNamespace false

namespace Trillium.HeapLang

open Iris Iris.BI Iris.Std Iris.ProofMode Iris.Algebra
open Iris.HeapLang (Loc Binder BaseLit UnOp BinOp HeapF)
open Trillium.Language

/-! ## Ghost state -/

/-- The ghost state needed to allocate a heap (Rocq `heap1GpreS`). -/
@[rocq_alias trillium.heap_lang.heap1GpreS]
class Heap1GpreS (GF : BundledGFunctors) where
  heap1GpreS_gen_heap : genHeapPreS Loc Val GF HeapF

attribute [reducible, instance] Heap1GpreS.heap1GpreS_gen_heap

/-- The ghost state of an allocated heap (Rocq `heap1GS`). -/
@[rocq_alias trillium.heap_lang.heap1GS]
class Heap1GS (GF : BundledGFunctors) where
  heap1_gen_heapGS : genHeapGS Loc Val GF HeapF

attribute [reducible, instance] Heap1GS.heap1_gen_heapGS

/-- Rocq field `heap1_inG` of `heap1GS`: derived from the `genHeapGS` instance. -/
@[reducible]
instance Heap1GS.heap1_inG [Heap1GS GF] : Heap1GpreS GF :=
  ⟨(Heap1GS.heap1_gen_heapGS (GF := GF)).togenHeapPreS⟩

/-- The functors needed for the heap (Rocq `heap1Σ`). -/
@[rocq_alias trillium.heap_lang.«heap1Σ»]
def heap1GF : BundledGFunctors
  | 0 => ⟨constOF (HeapView Loc (Agree (DiscreteO Val)) HeapF)⟩
  | 1 => ⟨constOF (HeapView Loc (Agree (DiscreteO GName)) HeapF)⟩
  | 2 => ⟨constOF MetaUR⟩
  | _ => ⟨constOF Unit⟩

instance instHeap1GpreS_heap1GF : Heap1GpreS heap1GF where
  heap1GpreS_gen_heap := by
    constructor
    · constructor
      exists 0
    · constructor
      exists 1
    · exists 2

#rocq_ignore trillium.heap_lang.subG_heap1PreG
  "`subG` is subsumed by direct `ElemG` synthesis on `BundledGFunctors`; see `instHeap1GpreS_heap1GF`."

/-! ## Translating `PartialMap` operations to `Std.ExtTreeMap` -/

theorem partialMap_get?_eq {V : Type _} (m : HeapF V) (k : Loc) : get? m k = m[k]? := rfl

/-- iris-lean's generic `insert` on `HeapF` is core's `Std.ExtTreeMap.insert`. -/
theorem partialMap_insert_eq {V : Type _} (m : HeapF V) (k : Loc) (v : V) :
    Iris.Std.insert (M := HeapF) m k v = Std.ExtTreeMap.insert m k v := by
  apply Std.ExtTreeMap.ext_getElem?
  intro k'
  change (Iris.Std.get? (Iris.Std.insert m k v) k') = _
  by_cases h : k = k'
  · subst h; rw [LawfulPartialMap.get?_insert_eq rfl]; simp
  · rw [LawfulPartialMap.get?_insert_ne h, Std.ExtTreeMap.getElem?_insert]
    have : ¬ compare k k' = .eq := fun h' => h (Std.LawfulEqOrd.eq_of_compare h')
    simp [this]; rfl

/-- iris-lean's generic (left-biased) union on `HeapF` is core's (right-biased) union with the
arguments swapped. -/
theorem partialMap_union_eq {V : Type _} (m₁ m₂ : HeapF V) :
    (Union.union (self := PartialMap.instUnion) m₁ m₂ : HeapF V) = m₂ ∪ m₁ := by
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  change (Iris.Std.get? (Union.union (self := PartialMap.instUnion) m₁ m₂) k) = _
  rw [LawfulPartialMap.get?_union, Std.ExtTreeMap.getElem?_union]
  change (m₁[k]?).orElse (fun _ => m₂[k]?) = _
  cases m₁[k]? <;> cases m₂[k]? <;> rfl

/-! ## Values and atomicity -/

@[rocq_alias trillium.heap_lang.into_val_val]
instance into_val_val (v : Val) : IntoVal (Expr.val v) v := ⟨rfl⟩

@[rocq_alias trillium.heap_lang.as_val_val]
instance as_val_val (v : Val) : AsVal (Expr.val v) := ⟨⟨v, rfl⟩⟩

/-- Port of the Rocq tactic `solve_atomic`: an expression whose head steps all end in values and
whose sub-redexes are all values is (strongly, hence also weakly) atomic. -/
theorem atomic_of_baseStep (a : Atomicity) (e : Expr)
    (hstep : ∀ σ e' σ' efs, BaseStep e σ e' σ' efs → (e'.toVal).isSome)
    (hsub : ∀ (Ki : ECtxItem) e', e = Ki.fill e' → (e'.toVal).isSome) :
    Atomic (State := State) a e :=
  strongly_atomic_atomic <|
    EctxLanguage.ectx_language_atomic .StronglyAtomic
      (fun σ e' σ' efs h => hstep σ e' σ' efs h)
      (EctxiLanguage.ectxi_language_sub_redexes_are_values fun Ki e' h => hsub Ki e' h)

/-- Port of the Rocq tactic `solve_atomic`. -/
macro "solve_atomic" : tactic => `(tactic| (
  apply atomic_of_baseStep
  · intro σ e' σ' efs h
    cases h <;> simp_all [Expr.toVal, Expr.subst, Expr.substStr]
  · intro Ki e' h
    cases Ki <;> simp only [ECtxItem.fill, Expr.val.injEq, reduceCtorEq] at h <;>
      (try obtain ⟨rfl, _⟩ := h) <;> (try obtain ⟨_, rfl, _⟩ := h) <;> (try subst h) <;>
      simp [Expr.toVal]))

@[rocq_alias trillium.heap_lang.rec_atomic]
instance rec_atomic (s : Atomicity) (f x : Binder) (e : Expr) :
    Atomic (State := State) s (Expr.rec_ f x e) := by solve_atomic

@[rocq_alias trillium.heap_lang.pair_atomic]
instance pair_atomic (s : Atomicity) (v1 v2 : Val) :
    Atomic (State := State) s (Expr.pair (.val v1) (.val v2)) := by solve_atomic

@[rocq_alias trillium.heap_lang.injl_atomic]
instance injl_atomic (s : Atomicity) (v : Val) :
    Atomic (State := State) s (Expr.injL (.val v)) := by solve_atomic

@[rocq_alias trillium.heap_lang.injr_atomic]
instance injr_atomic (s : Atomicity) (v : Val) :
    Atomic (State := State) s (Expr.injR (.val v)) := by solve_atomic

/-- The instance below is a more general version of `Skip`. -/
@[rocq_alias trillium.heap_lang.beta_atomic]
instance beta_atomic (s : Atomicity) (f x : Binder) (v1 v2 : Val) :
    Atomic (State := State) s (Expr.app (.val (.rec_ f x (.val v1))) (.val v2)) := by
  cases f <;> cases x <;> solve_atomic

@[rocq_alias trillium.heap_lang.unop_atomic]
instance unop_atomic (s : Atomicity) (op : UnOp) (v : Val) :
    Atomic (State := State) s (Expr.unop op (.val v)) := by solve_atomic

@[rocq_alias trillium.heap_lang.binop_atomic]
instance binop_atomic (s : Atomicity) (op : BinOp) (v1 v2 : Val) :
    Atomic (State := State) s (Expr.binop op (.val v1) (.val v2)) := by solve_atomic

@[rocq_alias trillium.heap_lang.if_true_atomic]
instance if_true_atomic (s : Atomicity) (v1 : Val) (e2 : Expr) :
    Atomic (State := State) s (Expr.if (.val (.lit (.bool true))) (.val v1) e2) := by solve_atomic

@[rocq_alias trillium.heap_lang.if_false_atomic]
instance if_false_atomic (s : Atomicity) (e1 : Expr) (v2 : Val) :
    Atomic (State := State) s (Expr.if (.val (.lit (.bool false))) e1 (.val v2)) := by solve_atomic

@[rocq_alias trillium.heap_lang.fst_atomic]
instance fst_atomic (s : Atomicity) (v : Val) :
    Atomic (State := State) s (Expr.fst (.val v)) := by solve_atomic

@[rocq_alias trillium.heap_lang.snd_atomic]
instance snd_atomic (s : Atomicity) (v : Val) :
    Atomic (State := State) s (Expr.snd (.val v)) := by solve_atomic

@[rocq_alias trillium.heap_lang.fork_atomic]
instance fork_atomic (s : Atomicity) (e : Expr) :
    Atomic (State := State) s (Expr.fork e) := by solve_atomic

@[rocq_alias trillium.heap_lang.alloc_atomic]
instance alloc_atomic (s : Atomicity) (v w : Val) :
    Atomic (State := State) s (Expr.allocN (.val v) (.val w)) := by solve_atomic

@[rocq_alias trillium.heap_lang.load_atomic]
instance load_atomic (s : Atomicity) (v : Val) :
    Atomic (State := State) s (Expr.load (.val v)) := by solve_atomic

@[rocq_alias trillium.heap_lang.store_atomic]
instance store_atomic (s : Atomicity) (v1 v2 : Val) :
    Atomic (State := State) s (Expr.store (.val v1) (.val v2)) := by solve_atomic

@[rocq_alias trillium.heap_lang.cmpxchg_atomic]
instance cmpxchg_atomic (s : Atomicity) (v0 v1 v2 : Val) :
    Atomic (State := State) s (Expr.cmpXchg (.val v0) (.val v1) (.val v2)) := by solve_atomic

@[rocq_alias trillium.heap_lang.faa_atomic]
instance faa_atomic (s : Atomicity) (v1 v2 : Val) :
    Atomic (State := State) s (Expr.faa (.val v1) (.val v2)) := by solve_atomic

/-! ## Pure steps -/

/-- `AsRecV v f x erec` turns the value `v` into `.rec_ f x erec`. The only instance,
`AsRecV_recv`, applies when `v` is syntactically a `.rec_` (instances do not unfold
definitions), mirroring the Rocq `Hint Extern` set-up: the pure-step automation does not reduce
lambdas hidden behind definitions. -/
@[rocq_alias trillium.heap_lang.AsRecV]
class AsRecV (v : Val) (f x : outParam Binder) (erec : outParam Expr) : Prop where
  as_recv : v = .rec_ f x erec

@[rocq_alias trillium.heap_lang.AsRecV_recv]
instance AsRecV_recv (f x : Binder) (e : Expr) : AsRecV (.rec_ f x e) f x e := ⟨rfl⟩

/-- Port of the Rocq tactic `solve_pure_exec`: a deterministic, state-independent head step
gives a one-step `PureExec`. -/
theorem pureExec_of_baseStep {φ : Prop} {e1 e2 : Expr}
    (safe : φ → ∀ σ : State, ∃ e' σ' efs, BaseStep e1 σ e' σ' efs)
    (det : φ → ∀ (σ : State) e2' σ2 efs, BaseStep e1 σ e2' σ2 efs →
      σ2 = σ ∧ e2' = e2 ∧ efs = []) :
    PureExec (Expr := Expr) φ 1 e1 e2 :=
  ⟨fun hφ => Relation.Iterate.once <|
    EctxLanguage.pure_head_step_pure_step ⟨fun σ => safe hφ σ, fun h => det hφ _ _ _ _ h⟩⟩

/-- Port of the Rocq tactic `solve_pure_exec`. -/
macro "solve_pure_exec" : tactic => `(tactic| (
  apply pureExec_of_baseStep
  · intro hφ σ
    exact ⟨_, _, _, by constructor <;> first | assumption | rfl⟩
  · intro hφ σ e2' σ2 efs h
    cases h <;> simp_all))

@[rocq_alias trillium.heap_lang.pure_recc]
instance pure_recc (f x : Binder) (erec : Expr) :
    PureExec True 1 (Expr.rec_ f x erec) (.val (.rec_ f x erec)) := by solve_pure_exec

@[rocq_alias trillium.heap_lang.pure_pairc]
instance pure_pairc (v1 v2 : Val) :
    PureExec True 1 (Expr.pair (.val v1) (.val v2)) (.val (.pair v1 v2)) := by solve_pure_exec

@[rocq_alias trillium.heap_lang.pure_injlc]
instance pure_injlc (v : Val) : PureExec True 1 (Expr.injL (.val v)) (.val (.injL v)) := by
  solve_pure_exec

@[rocq_alias trillium.heap_lang.pure_injrc]
instance pure_injrc (v : Val) : PureExec True 1 (Expr.injR (.val v)) (.val (.injR v)) := by
  solve_pure_exec

@[rocq_alias trillium.heap_lang.pure_beta]
instance pure_beta (f x : Binder) (erec : Expr) (v1 v2 : Val) [h : AsRecV v1 f x erec] :
    PureExec True 1 (Expr.app (.val v1) (.val v2)) ((erec.subst f v1).subst x v2) := by
  obtain ⟨rfl⟩ := h
  apply pureExec_of_baseStep
  · intro _ σ
    exact ⟨_, _, _, .betaS f x erec v2 _ σ rfl⟩
  · intro _ σ e2' σ2 efs h
    cases h; simp_all

/-- Rocq's instance `pure_unop`. Since `φ` and `e2` are out-params of `PureExec`, `v'` (which
occurs only there) cannot be found by instance resolution; this is therefore a theorem, and the
instance used by automation is `pure_unop_getD`. -/
@[rocq_alias trillium.heap_lang.pure_unop]
theorem pure_unop (op : UnOp) (v v' : Val) :
    PureExec (unOpEval op v = some v') 1 (Expr.unop op (.val v)) (.val v') := by
  apply pureExec_of_baseStep
  · intro hφ σ
    exact ⟨_, _, _, .unOpS op v v' σ hφ⟩
  · intro hφ σ e2' σ2 efs h
    cases h; simp_all

/-- Rocq's instance `pure_binop`. As for `pure_unop`, this is a theorem; the instance used by
automation is `pure_binop_getD`. -/
@[rocq_alias trillium.heap_lang.pure_binop]
theorem pure_binop (op : BinOp) (v1 v2 v' : Val) :
    PureExec (binOpEval op v1 v2 = some v') 1 (Expr.binop op (.val v1) (.val v2)) (.val v') := by
  apply pureExec_of_baseStep
  · intro hφ σ
    exact ⟨_, _, _, .binOpS op v1 v2 v' σ hφ⟩
  · intro hφ σ e2' σ2 efs h
    cases h; simp_all

/-- Instance form of `pure_unop`, with the result value computed by `unOpEval`. -/
instance pure_unop_getD (op : UnOp) (v : Val) :
    PureExec ((unOpEval op v).isSome = true) 1 (Expr.unop op (.val v))
      (.val ((unOpEval op v).getD default)) :=
  ⟨fun h => (pure_unop op v _).pure_exec (by cases hv : unOpEval op v <;> simp_all)⟩

/-- Instance form of `pure_binop`, with the result value computed by `binOpEval`. -/
instance (priority := low) pure_binop_getD (op : BinOp) (v1 v2 : Val) :
    PureExec ((binOpEval op v1 v2).isSome = true) 1 (Expr.binop op (.val v1) (.val v2))
      (.val ((binOpEval op v1 v2).getD default)) :=
  ⟨fun h => (pure_binop op v1 v2 _).pure_exec (by cases hv : binOpEval op v1 v2 <;> simp_all)⟩

/-- Higher-priority instance for `EqOp`. -/
@[rocq_alias trillium.heap_lang.pure_eqop]
instance (priority := high) pure_eqop (v1 v2 : Val) :
    PureExec (v1.compareSafe v2 = true) 1 (Expr.binop .eq (.val v1) (.val v2))
      (.val (.lit (.bool (decide (v1 = v2))))) := by
  have hev : v1.compareSafe v2 = true →
      binOpEval .eq v1 v2 = some (.lit (.bool (decide (v1 = v2)))) := by
    intro h; simp [binOpEval, h]
  apply pureExec_of_baseStep
  · intro hφ σ
    exact ⟨_, _, _, .binOpS .eq v1 v2 _ σ (hev hφ)⟩
  · intro hφ σ e2' σ2 efs h
    cases h with
    | binOpS _ _ _ v' _ h => rw [hev hφ] at h; cases h; simp

@[rocq_alias trillium.heap_lang.pure_if_true]
instance pure_if_true (e1 e2 : Expr) :
    PureExec True 1 (Expr.if (.val (.lit (.bool true))) e1 e2) e1 := by solve_pure_exec

@[rocq_alias trillium.heap_lang.pure_if_false]
instance pure_if_false (e1 e2 : Expr) :
    PureExec True 1 (Expr.if (.val (.lit (.bool false))) e1 e2) e2 := by solve_pure_exec

@[rocq_alias trillium.heap_lang.pure_fst]
instance pure_fst (v1 v2 : Val) : PureExec True 1 (Expr.fst (.val (.pair v1 v2))) (.val v1) := by
  solve_pure_exec

@[rocq_alias trillium.heap_lang.pure_snd]
instance pure_snd (v1 v2 : Val) : PureExec True 1 (Expr.snd (.val (.pair v1 v2))) (.val v2) := by
  solve_pure_exec

@[rocq_alias trillium.heap_lang.pure_case_inl]
instance pure_case_inl (v : Val) (e1 e2 : Expr) :
    PureExec True 1 (Expr.case (.val (.injL v)) e1 e2) (.app e1 (.val v)) := by solve_pure_exec

@[rocq_alias trillium.heap_lang.pure_case_inr]
instance pure_case_inr (v : Val) (e1 e2 : Expr) :
    PureExec True 1 (Expr.case (.val (.injR v)) e1 e2) (.app e2 (.val v)) := by solve_pure_exec

/-! ## Heap arrays -/

section Heap

variable {GF : BundledGFunctors} [Heap1GS GF]

theorem heapArray_get?_self_succ (l : Loc) (vs : List Val) :
    (heapArray (l + (1 : Int)) vs)[l]? = none := by
  rcases h : (heapArray (l + (1 : Int)) vs)[l]? with _ | w
  · rfl
  · obtain ⟨j, hj, hl, -⟩ := (heapArray_lookup _ vs w l).mp h
    rw [Iris.HeapLang.loc_add_assoc] at hl
    have := congrArg Loc.n hl
    simp at this
    omega

theorem heapArray_cons_eq (l : Loc) (v : Val) (vs : List Val) :
    heapArray l (v :: vs) = Iris.Std.insert (M := HeapF) (heapArray (l + (1 : Int)) vs) l v := by
  rw [partialMap_insert_eq]; rfl

/-- The usable rules for `allocN` stated in terms of the `array` proposition are derived in the
file `array`. -/
@[rocq_alias trillium.heap_lang.heap_array_to_seq_meta]
theorem heapArray_toSeq_metaToken (l : Loc) (vs : List Val) (n : Nat) (hlen : vs.length = n) :
    bigSepM (M := HeapF) (fun l' _ => metaToken (V := Val) l' ⊤) (heapArray l vs) ⊢@{IProp GF}
      [∗list] i ∈ List.range n, metaToken (V := Val) (l + ((i : Nat) : Int)) ⊤ := by
  subst hlen
  induction vs generalizing l with
  | nil => exact BigSepM.bigSepM_empty.1.trans BigSepL.bigSepL_nil.2
  | cons v vs ih =>
    rw [heapArray_cons_eq, List.length_cons, List.range_succ_eq_map]
    refine (BigSepM.bigSepM_insert (Φ := fun l' _ => iprop(metaToken (V := Val) l' ⊤))
      (heapArray_get?_self_succ l vs)).1.trans ?_
    refine .trans ?_ BigSepL.bigSepL_cons.2
    rw [BigSepL.bigSepL_map]
    refine BI.sep_mono (by simp [Iris.HeapLang.loc_add_zero]) ((ih (l + (1 : Int))).trans ?_)
    refine BigSepL.bigSepL_mono_of_forall ?_
    have h (j : Nat) : l + (1 : Int) + (j : Int) = l + ((j.succ : Nat) : Int) := by
      rw [Iris.HeapLang.loc_add_assoc]; congr 1; omega
    intro _ j; rw [h]

@[rocq_alias trillium.heap_lang.heap_array_to_seq_mapsto]
theorem heapArray_toSeq_pointsTo (l : Loc) (v : Val) (n : Nat) :
    bigSepM (M := HeapF) (fun l' v => iprop(l' ↦ v)) (heapArray l (List.replicate n v))
      ⊢@{IProp GF} [∗list] i ∈ List.range n, (l + ((i : Nat) : Int)) ↦ v := by
  induction n generalizing l with
  | zero => exact BigSepM.bigSepM_empty.1.trans BigSepL.bigSepL_nil.2
  | succ n ih =>
    rw [List.replicate_succ, heapArray_cons_eq, List.range_succ_eq_map]
    refine (BigSepM.bigSepM_insert (Φ := fun l' v => iprop(l' ↦ v))
      (heapArray_get?_self_succ l _)).1.trans ?_
    refine .trans ?_ BigSepL.bigSepL_cons.2
    rw [BigSepL.bigSepL_map]
    refine BI.sep_mono (by simp [Iris.HeapLang.loc_add_zero]) ((ih (l + (1 : Int))).trans ?_)
    refine BigSepL.bigSepL_mono_of_forall ?_
    have h (j : Nat) : l + (1 : Int) + (j : Int) = l + ((j.succ : Nat) : Int) := by
      rw [Iris.HeapLang.loc_add_assoc]; congr 1; omega
    intro _ j; rw [h]

end Heap

end Trillium.HeapLang
