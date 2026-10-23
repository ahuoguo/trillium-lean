/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.HeapLang.Locations
import Trillium.ProgramLogic.EctxiLanguage
import Iris.HeapLang.Semantics

/-!
# HeapLang (Trillium variant)

Port of `heap_lang/lang.v`.

Trillium's HeapLang is a variant of Iris' HeapLang: there are no prophecy operations
(`NewProph`/`Resolve`), no `Free`/`Xchg`, but a non-deterministic `ChooseNat`; the state still
records a set of used prophecy identifiers; locales are natural numbers (the position of a
thread in the thread pool, `localeOf c e = c.length`) and there are no configuration steps.
The language is set up by a single `Trillium.EctxiLanguage` instance
(`Trillium.HeapLang.instEctxiLanguage`), from which `EctxLanguage` and `Language` follow.

## Representation

* Literals, unary and binary operators, binders, prophecy identifiers and locations are the
  same as in Iris' HeapLang, so iris-lean's `Iris.HeapLang.{BaseLit, UnOp, BinOp, Binder,
  ProphId, Loc}` are reused (together with `BinOp.evalInt`, `BinOp.evalBool` and
  `BaseLit.isUnboxed`). The expression and value types `Trillium.HeapLang.Expr`/`Val` are new.
* Rocq's `Val v`/`of_val v` is the constructor `Expr.val v`, which is the simp normal form
  (`ofVal v` and the coercion `↑v` unfold to it by `ofVal_eq_val`).
* `gmap loc val` is `GMap Loc Val`, `gset proph_id` is `GSet ProphId`. Rocq's
  `heap_array`/`state_init_heap` use stdpp's left-biased union; here `heapArray` inserts and
  `State.initHeap` uses core's right-biased union with the arguments swapped.
* Unboxedness and `vals_compare_safe` are `Bool`-valued (as in iris-lean).
* The head step relation `head_step` is the inductive `Trillium.HeapLang.BaseStep` (named as in
  iris-lean, to avoid a clash with the class `Trillium.HeadStep` whose field `headStep` it
  instantiates). Evaluation context items are `ECtxItem` with `ECtxItem.fill`.
-/

set_option linter.dupNamespace false

namespace Trillium.HeapLang

open Iris.HeapLang (Loc Binder BaseLit UnOp BinOp ProphId loc_add_n)
open Iris.ProgramLogic (ToVal EvContext EvContextOps)
open Iris.ProgramLogic.ToVal (ofVal)

/-! ## Syntax -/

attribute [rocq_alias trillium.heap_lang.heap_lang.proph_id] Iris.HeapLang.ProphId
attribute [rocq_alias trillium.heap_lang.heap_lang.base_lit] Iris.HeapLang.BaseLit
attribute [rocq_alias trillium.heap_lang.heap_lang.un_op] Iris.HeapLang.UnOp
attribute [rocq_alias trillium.heap_lang.heap_lang.bin_op] Iris.HeapLang.BinOp
attribute [rocq_alias trillium.heap_lang.heap_lang.base_lit_eq_dec]
  Iris.HeapLang.instDecidableEqBaseLit
attribute [rocq_alias trillium.heap_lang.heap_lang.un_op_eq_dec] Iris.HeapLang.instDecidableEqUnOp
attribute [rocq_alias trillium.heap_lang.heap_lang.bin_op_eq_dec]
  Iris.HeapLang.instDecidableEqBinOp
attribute [rocq_alias trillium.heap_lang.heap_lang.base_lit_countable]
  Iris.HeapLang.instCountableBaseLit
attribute [rocq_alias trillium.heap_lang.heap_lang.un_op_finite] Iris.HeapLang.instCountableUnOp
attribute [rocq_alias trillium.heap_lang.heap_lang.bin_op_countable]
  Iris.HeapLang.instCountableBinOp

mutual
  /-- Expressions of Trillium's HeapLang. -/
  @[rocq_alias trillium.heap_lang.heap_lang.expr]
  inductive Expr : Type where
    /- Values -/
    | val (v : Val)
    /- Base lambda calculus -/
    | var (x : String)
    | rec_ (f x : Binder) (e : Expr)
    | app (e₁ e₂ : Expr)
    /- Base types and their operations -/
    | unop (op : UnOp) (e : Expr)
    | binop (op : BinOp) (e₁ e₂ : Expr)
    | if (e₀ e₁ e₂ : Expr)
    /- Products -/
    | pair (e₁ e₂ : Expr)
    | fst (e : Expr)
    | snd (e : Expr)
    /- Sums -/
    | injL (e : Expr)
    | injR (e : Expr)
    | case (e₀ e₁ e₂ : Expr)
    /- Concurrency -/
    | fork (e : Expr)
    /- Heap -/
    | allocN (e₁ e₂ : Expr) /- array length (positive number), initial value -/
    | load (e : Expr)
    | store (e₁ e₂ : Expr)
    | cmpXchg (e₀ e₁ e₂ : Expr) /- compare-exchange -/
    | faa (e₁ e₂ : Expr) /- fetch-and-add -/
    /- Non-determinism -/
    | chooseNat
  deriving Repr, DecidableEq

  /-- Values of Trillium's HeapLang. -/
  @[rocq_alias trillium.heap_lang.heap_lang.val]
  inductive Val : Type where
    | lit (l : BaseLit)
    | rec_ (f x : Binder) (e : Expr)
    | pair (v₁ v₂ : Val)
    | injL (v : Val)
    | injR (v : Val)
  deriving Repr, DecidableEq
end

attribute [rocq_alias trillium.heap_lang.heap_lang.expr_eq_dec] instDecidableEqExpr
attribute [rocq_alias trillium.heap_lang.heap_lang.val_eq_dec] instDecidableEqVal

@[rocq_alias trillium.heap_lang.heap_lang.val_inhabited]
instance instInhabitedVal : Inhabited Val := ⟨.lit .unit⟩

@[rocq_alias trillium.heap_lang.heap_lang.expr_inhabited]
instance instInhabitedExpr : Inhabited Expr := ⟨.val default⟩

/-- An observation associates a prophecy variable (identifier) to a pair of values. Trillium's
HeapLang has no prophecy operations, so observations are unused. -/
@[rocq_alias trillium.heap_lang.heap_lang.observation]
abbrev Observation := ProphId × (Val × Val)

@[rocq_alias trillium.heap_lang.heap_lang.to_val]
def Expr.toVal : Expr → Option Val
  | .val v => some v
  | _ => none

@[rocq_alias trillium.heap_lang.heap_lang.to_of_val, simp]
theorem to_of_val (v : Val) : Expr.toVal (.val v) = some v := rfl

@[rocq_alias trillium.heap_lang.heap_lang.of_to_val]
theorem of_to_val {e : Expr} {v : Val} : e.toVal = some v → Expr.val v = e := by
  cases e <;> simp [Expr.toVal, eq_comm]

@[rocq_alias trillium.heap_lang.heap_lang.of_val_inj]
theorem val_injective : Function.Injective Expr.val := fun _ _ h => Expr.val.inj h

instance instToVal : ToVal Expr Val where
  toVal := Expr.toVal
  ofVal := .val
  coe_of_toVal_eq_some := of_to_val
  toVal_coe := to_of_val

@[simp]
theorem ofVal_eq_val (v : Val) : (ofVal v : Expr) = .val v := rfl

@[simp]
theorem toVal_eq (e : Expr) : toVal e = e.toVal := rfl

/-! ### Countability -/

/-- One node of the `Expr`/`Val` encoding: a constructor tag followed by the codes of that
constructor's arguments (Rocq encodes into `gen_tree`). -/
def encNode (tag : Nat) (args : List Pos) : Pos :=
  Pos.Countable.encode (Pos.Countable.encode tag :: args)

@[simp]
theorem encNode_eq_iff {t₁ t₂ : Nat} {a₁ a₂ : List Pos} :
    encNode t₁ a₁ = encNode t₂ a₂ ↔ t₁ = t₂ ∧ a₁ = a₂ := by
  simp [encNode]

mutual

/-- Injective encoding of expressions into `Pos`. -/
def Expr.enc : Expr → Pos
  | .val v            => encNode 0 [v.enc]
  | .var x            => encNode 1 [Pos.Countable.encode x]
  | .rec_ f x e       => encNode 2 [Pos.Countable.encode f, Pos.Countable.encode x, e.enc]
  | .app e₁ e₂        => encNode 3 [e₁.enc, e₂.enc]
  | .unop op e        => encNode 4 [Pos.Countable.encode op, e.enc]
  | .binop op e₁ e₂   => encNode 5 [Pos.Countable.encode op, e₁.enc, e₂.enc]
  | .if e₀ e₁ e₂      => encNode 6 [e₀.enc, e₁.enc, e₂.enc]
  | .pair e₁ e₂       => encNode 7 [e₁.enc, e₂.enc]
  | .fst e            => encNode 8 [e.enc]
  | .snd e            => encNode 9 [e.enc]
  | .injL e           => encNode 10 [e.enc]
  | .injR e           => encNode 11 [e.enc]
  | .case e₀ e₁ e₂    => encNode 12 [e₀.enc, e₁.enc, e₂.enc]
  | .fork e           => encNode 13 [e.enc]
  | .allocN e₁ e₂     => encNode 14 [e₁.enc, e₂.enc]
  | .load e           => encNode 15 [e.enc]
  | .store e₁ e₂      => encNode 16 [e₁.enc, e₂.enc]
  | .cmpXchg e₀ e₁ e₂ => encNode 17 [e₀.enc, e₁.enc, e₂.enc]
  | .faa e₁ e₂        => encNode 18 [e₁.enc, e₂.enc]
  | .chooseNat        => encNode 19 []

/-- Injective encoding of values into `Pos`. -/
def Val.enc : Val → Pos
  | .lit l      => encNode 0 [Pos.Countable.encode l]
  | .rec_ f x e => encNode 1 [Pos.Countable.encode f, Pos.Countable.encode x, e.enc]
  | .pair v₁ v₂ => encNode 2 [v₁.enc, v₂.enc]
  | .injL v     => encNode 3 [v.enc]
  | .injR v     => encNode 4 [v.enc]

end

theorem Expr.enc_inj : Expr.enc.Injective := by
  intro e₁
  induction e₁ using Expr.enc.induct
      (motive_2 := fun v => ∀ v', Val.enc v = Val.enc v' → v = v') <;>
    (try intro _ _) <;> rename_i e₂ _ <;> cases e₂ <;> simp_all [Expr.enc, Val.enc] <;> grind

theorem Val.enc_inj : Val.enc.Injective := by
  intro v₁
  induction v₁ using Val.enc.induct
      (motive_1 := fun e => ∀ e', Expr.enc e = Expr.enc e' → e = e') <;>
    (try intro _ _) <;> rename_i v₂ _ <;> cases v₂ <;> simp_all [Expr.enc, Val.enc] <;> grind

@[rocq_alias trillium.heap_lang.heap_lang.expr_countable]
noncomputable instance instCountableExpr : Pos.Countable Expr := .ofInjective Expr.enc Expr.enc_inj

/-- Rocq derives this from `of_val`/`to_val`; we use the direct encoding. -/
@[rocq_alias trillium.heap_lang.heap_lang.val_countable]
noncomputable instance instCountableVal : Pos.Countable Val := .ofInjective Val.enc Val.enc_inj

/-! ### Unboxed values -/

attribute [rocq_alias trillium.heap_lang.heap_lang.lit_is_unboxed] Iris.HeapLang.BaseLit.isUnboxed

/-- Values that are represented by a single machine word (see the Rocq source for the encoding).
`Bool`-valued, as in iris-lean. -/
@[rocq_alias trillium.heap_lang.heap_lang.val_is_unboxed]
def Val.isUnboxed : Val → Bool
  | .lit l => l.isUnboxed
  | .injL (.lit l) => l.isUnboxed
  | .injR (.lit l) => l.isUnboxed
  | _ => false

#rocq_ignore trillium.heap_lang.heap_lang.lit_is_unboxed_dec
  "`BaseLit.isUnboxed` is `Bool`-valued; decidability is definitional."
#rocq_ignore trillium.heap_lang.heap_lang.val_is_unboxed_dec
  "`Val.isUnboxed` is `Bool`-valued; decidability is definitional."

/-- Comparing two values is safe if at least one of them is unboxed. -/
@[rocq_alias trillium.heap_lang.heap_lang.vals_compare_safe]
def Val.compareSafe (vl v1 : Val) : Bool :=
  vl.isUnboxed || v1.isUnboxed

/-! ## State -/

/-- The state: a heap of values and a set of used prophecy identifiers. -/
@[rocq_alias trillium.heap_lang.heap_lang.state]
structure State where
  heap : GMap Loc Val
  usedProphId : GSet ProphId

@[rocq_alias trillium.heap_lang.heap_lang.state_inhabited]
instance instInhabitedState : Inhabited State := ⟨⟨∅, ∅⟩⟩

#rocq_ignore trillium.heap_lang.heap_lang.stateO
  "Canonical Leibniz OFE on `state`; Lean uses the generic `stateO State` (`DiscreteO State`)."
#rocq_ignore trillium.heap_lang.heap_lang.locO
  "Canonical Leibniz OFE on `loc`; Lean uses `DiscreteO Loc`."
#rocq_ignore trillium.heap_lang.heap_lang.valO
  "Canonical Leibniz OFE on `val`; Lean uses the generic `valO Val` (`DiscreteO Val`)."
#rocq_ignore trillium.heap_lang.heap_lang.exprO
  "Canonical Leibniz OFE on `expr`; Lean uses the generic `exprO Expr` (`DiscreteO Expr`)."

/-! ## Evaluation contexts -/

@[rocq_alias trillium.heap_lang.heap_lang.ectx_item]
inductive ECtxItem where
  | appL (v2 : Val)
  | appR (e1 : Expr)
  | unOp (op : UnOp)
  | binOpL (op : BinOp) (v2 : Val)
  | binOpR (op : BinOp) (e1 : Expr)
  | if (e1 e2 : Expr)
  | pairL (v2 : Val)
  | pairR (e1 : Expr)
  | fst
  | snd
  | injL
  | injR
  | case (e1 e2 : Expr)
  | allocNL (v2 : Val)
  | allocNR (e1 : Expr)
  | load
  | storeL (v2 : Val)
  | storeR (e1 : Expr)
  | cmpXchgL (v1 v2 : Val)
  | cmpXchgM (e0 : Expr) (v2 : Val)
  | cmpXchgR (e0 e1 : Expr)
  | faaL (v2 : Val)
  | faaR (e1 : Expr)
  deriving Repr, DecidableEq

@[rocq_alias trillium.heap_lang.heap_lang.fill_item]
def ECtxItem.fill (Ki : ECtxItem) (e : Expr) : Expr :=
  match Ki with
  | .appL v2        => .app e (.val v2)
  | .appR e1        => .app e1 e
  | .unOp op        => .unop op e
  | .binOpL op v2   => .binop op e (.val v2)
  | .binOpR op e1   => .binop op e1 e
  | .if e1 e2       => .if e e1 e2
  | .pairL v2       => .pair e (.val v2)
  | .pairR e1       => .pair e1 e
  | .fst            => .fst e
  | .snd            => .snd e
  | .injL           => .injL e
  | .injR           => .injR e
  | .case e1 e2     => .case e e1 e2
  | .allocNL v2     => .allocN e (.val v2)
  | .allocNR e1     => .allocN e1 e
  | .load           => .load e
  | .storeL v2      => .store e (.val v2)
  | .storeR e1      => .store e1 e
  | .cmpXchgL v1 v2 => .cmpXchg e (.val v1) (.val v2)
  | .cmpXchgM e0 v2 => .cmpXchg e0 e (.val v2)
  | .cmpXchgR e0 e1 => .cmpXchg e0 e1 e
  | .faaL v2        => .faa e (.val v2)
  | .faaR e1        => .faa e1 e

/-! ## Substitution -/

@[rocq_alias trillium.heap_lang.heap_lang.subst]
def Expr.substStr (x : String) (v : Val) : Expr → Expr
  | .val v' => .val v'
  | .var y => if x = y then .val v else .var y
  | .rec_ f y e => .rec_ f y <| if Binder.named x ≠ f ∧ Binder.named x ≠ y then e.substStr x v else e
  | .app e₁ e₂ => .app (e₁.substStr x v) (e₂.substStr x v)
  | .unop op e => .unop op (e.substStr x v)
  | .binop op e₁ e₂ => .binop op (e₁.substStr x v) (e₂.substStr x v)
  | .if e₀ e₁ e₂ => .if (e₀.substStr x v) (e₁.substStr x v) (e₂.substStr x v)
  | .pair e₁ e₂ => .pair (e₁.substStr x v) (e₂.substStr x v)
  | .fst e => .fst (e.substStr x v)
  | .snd e => .snd (e.substStr x v)
  | .injL e => .injL (e.substStr x v)
  | .injR e => .injR (e.substStr x v)
  | .case e₀ e₁ e₂ => .case (e₀.substStr x v) (e₁.substStr x v) (e₂.substStr x v)
  | .fork e => .fork (e.substStr x v)
  | .allocN e₁ e₂ => .allocN (e₁.substStr x v) (e₂.substStr x v)
  | .load e => .load (e.substStr x v)
  | .store e₁ e₂ => .store (e₁.substStr x v) (e₂.substStr x v)
  | .cmpXchg e₀ e₁ e₂ => .cmpXchg (e₀.substStr x v) (e₁.substStr x v) (e₂.substStr x v)
  | .faa e₁ e₂ => .faa (e₁.substStr x v) (e₂.substStr x v)
  | .chooseNat => .chooseNat

/-- Substitution for a binder (Rocq `subst'`): does nothing for the anonymous binder. -/
@[rocq_alias trillium.heap_lang.heap_lang.subst']
def Expr.subst (mx : Binder) (v : Val) : Expr → Expr :=
  match mx with
  | .named x => Expr.substStr x v
  | .anon => id

/-! ## The stepping relation -/

@[rocq_alias trillium.heap_lang.heap_lang.un_op_eval]
def unOpEval : UnOp → Val → Option Val
  | .neg,   .lit (.bool b) => some (.lit (.bool (!b)))
  | .neg,   .lit (.int n)  => some (.lit (.int (~~~n)))
  | .minus, .lit (.int n)  => some (.lit (.int (-n)))
  | _,      _              => none

attribute [rocq_alias trillium.heap_lang.heap_lang.bin_op_eval_int] Iris.HeapLang.BinOp.evalInt
attribute [rocq_alias trillium.heap_lang.heap_lang.bin_op_eval_bool] Iris.HeapLang.BinOp.evalBool

/-- Evaluation of binary operators. Unlike Iris' HeapLang, Trillium's version performs pointer
offsetting for a location and an integer under *every* operator other than `EqOp`. -/
@[rocq_alias trillium.heap_lang.heap_lang.bin_op_eval]
def binOpEval (op : BinOp) (v1 v2 : Val) : Option Val :=
  if op = .eq then
    -- Crucially, this compares the same way as `CmpXchg`!
    if v1.compareSafe v2 then some (.lit (.bool (decide (v1 = v2)))) else none
  else
    match v1, v2 with
    | .lit (.int n1), .lit (.int n2) => Val.lit <$> op.evalInt n1 n2
    | .lit (.bool b1), .lit (.bool b2) => Val.lit <$> op.evalBool b1 b2
    | .lit (.loc l), .lit (.int off) => some (.lit (.loc (l + off)))
    | _, _ => none

@[rocq_alias trillium.heap_lang.heap_lang.state_upd_heap]
def State.updHeap (f : GMap Loc Val → GMap Loc Val) (σ : State) : State :=
  { σ with heap := f σ.heap }

@[rocq_alias trillium.heap_lang.heap_lang.state_upd_used_proph_id]
def State.updUsedProphId (f : GSet ProphId → GSet ProphId) (σ : State) : State :=
  { σ with usedProphId := f σ.usedProphId }

@[simp] theorem State.updHeap_heap (f : GMap Loc Val → GMap Loc Val) (σ : State) :
    (σ.updHeap f).heap = f σ.heap := rfl

@[simp] theorem State.updHeap_usedProphId (f : GMap Loc Val → GMap Loc Val) (σ : State) :
    (σ.updHeap f).usedProphId = σ.usedProphId := rfl

@[simp] theorem State.updUsedProphId_heap (f : GSet ProphId → GSet ProphId) (σ : State) :
    (σ.updUsedProphId f).heap = σ.heap := rfl

@[simp] theorem State.updUsedProphId_usedProphId (f : GSet ProphId → GSet ProphId) (σ : State) :
    (σ.updUsedProphId f).usedProphId = f σ.usedProphId := rfl

/-- The heap fragment storing `vs` at consecutive locations starting at `l`. Rocq uses
`{[l := v]} ∪ heap_array (l +ₗ 1) vs'` with stdpp's left-biased union, i.e. an insertion. -/
@[rocq_alias trillium.heap_lang.heap_lang.heap_array]
def heapArray (l : Loc) : List Val → GMap Loc Val
  | [] => ∅
  | v :: vs => (heapArray (l + (1 : Int)) vs).insert l v

@[rocq_alias trillium.heap_lang.heap_lang.heap_array_singleton]
theorem heapArray_singleton (l : Loc) (v : Val) :
    heapArray l [v] = (∅ : GMap Loc Val).insert l v := rfl

@[rocq_alias trillium.heap_lang.heap_lang.heap_array_lookup]
theorem heapArray_lookup (l : Loc) (vs : List Val) (w : Val) (k : Loc) :
    (heapArray l vs)[k]? = some w ↔ ∃ j : Int, 0 ≤ j ∧ k = l + j ∧ vs[j.toNat]? = some w := by
  induction vs generalizing l with
  | nil => simp [heapArray]
  | cons v vs ih =>
    rw [heapArray, Std.ExtTreeMap.getElem?_insert]
    constructor
    · intro h
      split at h
      · rename_i hlk
        have hk : k = l := (Std.LawfulEqOrd.eq_of_compare hlk).symm
        refine ⟨0, le_rfl, by simp [hk], ?_⟩
        simpa using h
      · obtain ⟨j, hj, rfl, hjw⟩ := (ih _).mp h
        refine ⟨1 + j, by omega, by rw [Iris.HeapLang.loc_add_assoc], ?_⟩
        have : (1 + j).toNat = j.toNat + 1 := by omega
        simpa [this] using hjw
    · rintro ⟨j, hj, rfl, hjw⟩
      split
      · rename_i hlk
        have hk := Std.LawfulEqOrd.eq_of_compare hlk
        have hj0 : j = 0 := by
          have := congrArg Loc.n hk; simp at this; omega
        subst hj0; simpa using hjw
      · rename_i hlk
        have hj0 : j ≠ 0 := by
          rintro rfl; exact hlk (by simp)
        refine (ih _).mpr ⟨j - 1, by omega, ?_, ?_⟩
        · rw [Iris.HeapLang.loc_add_assoc]; congr 1; omega
        · have : j.toNat = (j - 1).toNat + 1 := by omega
          rw [this] at hjw; simpa using hjw

/-- Rocq states `heap_array l vs ##ₘ h`; stdpp's map disjointness is spelled out (it is
`Trillium.GMap.Disjoint`). -/
@[rocq_alias trillium.heap_lang.heap_lang.heap_array_map_disjoint]
theorem heapArray_map_disjoint (h : GMap Loc Val) (l : Loc) (vs : List Val) :
    (∀ i : Int, 0 ≤ i → i < vs.length → h[l + i]? = none) →
    ∀ k : Loc, (heapArray l vs)[k]? = none ∨ h[k]? = none := by
  intro hdisj k
  rcases hk : (heapArray l vs)[k]? with _ | w
  · exact .inl rfl
  · obtain ⟨j, hj, rfl, hjw⟩ := (heapArray_lookup l vs w k).mp hk
    have := (List.getElem?_eq_some_iff.mp hjw).1
    exact .inr (hdisj j hj (by omega))

/-- Allocate `n` copies of `v` starting at `l`. Rocq puts `h` on the right of stdpp's
left-biased union; with core's right-biased union it goes on the left. -/
@[rocq_alias trillium.heap_lang.heap_lang.state_init_heap]
def State.initHeap (σ : State) (l : Loc) (n : Int) (v : Val) : State :=
  σ.updHeap fun h => h ∪ heapArray l (List.replicate n.toNat v)

@[rocq_alias trillium.heap_lang.heap_lang.state_init_heap_singleton]
theorem State.initHeap_singleton (σ : State) (l : Loc) (v : Val) :
    σ.initHeap l 1 v = σ.updHeap (·.insert l v) := by
  simp only [State.initHeap, Int.toNat_one, List.replicate_one, heapArray_singleton]
  congr 1
  funext h
  ext1 k
  rw [Std.ExtTreeMap.getElem?_union, Std.ExtTreeMap.getElem?_insert,
    Std.ExtTreeMap.getElem?_insert]
  split <;> simp

/-- The head step relation of Trillium's HeapLang (Rocq `head_step`). -/
@[rocq_alias trillium.heap_lang.heap_lang.head_step]
inductive BaseStep : Expr → State → Expr → State → List Expr → Prop where
  | recS (f x : Binder) (e : Expr) (σ : State) :
      BaseStep (.rec_ f x e) σ (.val (.rec_ f x e)) σ []
  | pairS (v1 v2 : Val) (σ : State) :
      BaseStep (.pair (.val v1) (.val v2)) σ (.val (.pair v1 v2)) σ []
  | injLS (v : Val) (σ : State) :
      BaseStep (.injL (.val v)) σ (.val (.injL v)) σ []
  | injRS (v : Val) (σ : State) :
      BaseStep (.injR (.val v)) σ (.val (.injR v)) σ []
  | betaS (f x : Binder) (e1 : Expr) (v2 : Val) (e' : Expr) (σ : State) :
      e' = (e1.subst f (.rec_ f x e1)).subst x v2 →
      BaseStep (.app (.val (.rec_ f x e1)) (.val v2)) σ e' σ []
  | unOpS (op : UnOp) (v v' : Val) (σ : State) :
      unOpEval op v = some v' →
      BaseStep (.unop op (.val v)) σ (.val v') σ []
  | binOpS (op : BinOp) (v1 v2 v' : Val) (σ : State) :
      binOpEval op v1 v2 = some v' →
      BaseStep (.binop op (.val v1) (.val v2)) σ (.val v') σ []
  | ifTrueS (e1 e2 : Expr) (σ : State) :
      BaseStep (.if (.val (.lit (.bool true))) e1 e2) σ e1 σ []
  | ifFalseS (e1 e2 : Expr) (σ : State) :
      BaseStep (.if (.val (.lit (.bool false))) e1 e2) σ e2 σ []
  | fstS (v1 v2 : Val) (σ : State) :
      BaseStep (.fst (.val (.pair v1 v2))) σ (.val v1) σ []
  | sndS (v1 v2 : Val) (σ : State) :
      BaseStep (.snd (.val (.pair v1 v2))) σ (.val v2) σ []
  | caseLS (v : Val) (e1 e2 : Expr) (σ : State) :
      BaseStep (.case (.val (.injL v)) e1 e2) σ (.app e1 (.val v)) σ []
  | caseRS (v : Val) (e1 e2 : Expr) (σ : State) :
      BaseStep (.case (.val (.injR v)) e1 e2) σ (.app e2 (.val v)) σ []
  | forkS (e : Expr) (σ : State) :
      BaseStep (.fork e) σ (.val (.lit .unit)) σ [e]
  | allocNS (n : Int) (v : Val) (σ : State) (l : Loc) :
      0 < n →
      (∀ i : Int, 0 ≤ i → i < n → σ.heap[l + i]? = none) →
      BaseStep (.allocN (.val (.lit (.int n))) (.val v)) σ
        (.val (.lit (.loc l))) (σ.initHeap l n v) []
  | loadS (l : Loc) (v : Val) (σ : State) :
      σ.heap[l]? = some v →
      BaseStep (.load (.val (.lit (.loc l)))) σ (.val v) σ []
  | storeS (l : Loc) (v : Val) (σ : State) :
      (σ.heap[l]?).isSome →
      BaseStep (.store (.val (.lit (.loc l))) (.val v)) σ
        (.val (.lit .unit)) (σ.updHeap (·.insert l v)) []
  | cmpXchgS (l : Loc) (v1 v2 vl : Val) (σ : State) (b : Bool) :
      σ.heap[l]? = some vl →
      -- Crucially, this compares the same way as `EqOp`!
      vl.compareSafe v1 →
      b = decide (vl = v1) →
      BaseStep (.cmpXchg (.val (.lit (.loc l))) (.val v1) (.val v2)) σ
        (.val (.pair vl (.lit (.bool b)))) (if b then σ.updHeap (·.insert l v2) else σ) []
  | faaS (l : Loc) (i1 i2 : Int) (σ : State) :
      σ.heap[l]? = some (.lit (.int i1)) →
      BaseStep (.faa (.val (.lit (.loc l))) (.val (.lit (.int i2)))) σ
        (.val (.lit (.int i1))) (σ.updHeap (·.insert l (.lit (.int (i1 + i2))))) []
  | chooseNatS (n : Nat) (σ : State) :
      BaseStep .chooseNat σ (.val (.lit (.int n))) σ []

/-! ## Basic properties about the language -/

@[rocq_alias trillium.heap_lang.heap_lang.fill_item_inj]
theorem fill_item_inj (Ki : ECtxItem) : Function.Injective Ki.fill := by
  cases Ki <;> intro e₁ e₂ h <;> cases h <;> rfl

@[rocq_alias trillium.heap_lang.heap_lang.fill_item_val]
theorem fill_item_val (Ki : ECtxItem) (e : Expr) :
    ((Ki.fill e).toVal).isSome → (e.toVal).isSome := by
  cases Ki <;> simp [ECtxItem.fill, Expr.toVal]

@[rocq_alias trillium.heap_lang.heap_lang.val_head_stuck]
theorem val_head_stuck {e1 σ1 e2 σ2 efs} : BaseStep e1 σ1 e2 σ2 efs → e1.toVal = none := by
  intro h; cases h <;> rfl

@[rocq_alias trillium.heap_lang.heap_lang.head_ctx_step_val]
theorem head_ctx_step_val {Ki : ECtxItem} {e : Expr} {σ1 e2 σ2 efs} :
    BaseStep (Ki.fill e) σ1 e2 σ2 efs → (e.toVal).isSome := by
  cases Ki <;> intro h <;> cases h <;> rfl

@[rocq_alias trillium.heap_lang.heap_lang.fill_item_no_val_inj]
theorem fill_item_no_val_inj (Ki1 Ki2 : ECtxItem) {e1 e2 : Expr} :
    e1.toVal = none → e2.toVal = none → Ki1.fill e1 = Ki2.fill e2 → Ki1 = Ki2 := by
  intro h1 h2 h
  cases Ki1 <;> cases Ki2 <;> simp only [ECtxItem.fill] at h <;> cases h <;>
    simp_all [Expr.toVal]

@[rocq_alias trillium.heap_lang.heap_lang.alloc_fresh]
theorem alloc_fresh (v : Val) (n : Int) (σ : State) :
    let l := freshLocs (Std.ExtTreeSet.ofList σ.heap.keys compare)
    0 < n →
    BaseStep (.allocN (.val (.lit (.int n))) (.val v)) σ
      (.val (.lit (.loc l))) (σ.initHeap l n v) [] := by
  intro l hn
  refine .allocNS n v σ l hn fun i hi _ => ?_
  have := freshLocs_fresh (Std.ExtTreeSet.ofList σ.heap.keys compare) hi
  rw [Std.ExtTreeSet.mem_ofList] at this
  simp only [List.contains_iff_mem, Std.ExtTreeMap.mem_keys] at this
  exact Std.ExtTreeMap.getElem?_eq_none this

/-! ## Locales -/

@[rocq_alias trillium.heap_lang.heap_lang.base_locale]
abbrev BaseLocale := Nat

/-- The locale of a thread is its position in the thread pool. -/
@[rocq_alias trillium.heap_lang.heap_lang.locale_of]
def Expr.localeOf (c : List Expr) (_e : Expr) : BaseLocale := c.length

@[rocq_alias trillium.heap_lang.heap_lang.locale_step_same]
theorem locale_step_same {e1 e2 : Expr} (t1 : List Expr) {σ1 σ2 efs} :
    BaseStep e1 σ1 e2 σ2 efs → Expr.localeOf t1 e1 = Expr.localeOf t1 e2 :=
  fun _ => rfl

@[rocq_alias trillium.heap_lang.heap_lang.locale_fill]
theorem locale_fill (e : Expr) (K : ECtxItem) (t1 : List Expr) :
    Expr.localeOf t1 (K.fill e) = Expr.localeOf t1 e := rfl

@[rocq_alias trillium.heap_lang.heap_lang.heap_locale_injective]
theorem heap_locale_injective (tp0 : List Expr) (e0 : Expr) (tp1 tp : List Expr) (e : Expr) :
    (tp, e) ∈ prefixesFrom (tp0 ++ [e0]) tp1 → Expr.localeOf tp0 e0 ≠ Expr.localeOf tp e := by
  rw [mem_prefixesFrom_iff]
  rintro ⟨t, t', rfl, -⟩
  simp [Expr.localeOf]

theorem length_prefixesFrom {A : Type _} (pref l : List A) :
    (prefixesFrom pref l).length = l.length := by
  induction l generalizing pref with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- There are no configuration steps in HeapLang. -/
@[rocq_alias trillium.heap_lang.heap_lang.context_step]
def contextStep (_ _ : State) : Prop := False

/-- The `EctxiLanguage` structure of HeapLang (Rocq `heap_lang_mixin` and the canonical
structure `heap_ectxi_lang`). -/
@[rocq_alias trillium.heap_lang.heap_lang.heap_lang_mixin,
  rocq_alias trillium.heap_lang.heap_ectxi_lang]
instance instEctxiLanguage : EctxiLanguage Expr Val ECtxItem State BaseLocale where
  toToVal := instToVal
  configStep := contextStep
  localeOf := Expr.localeOf
  locale_equiv t t' _ h := by
    have := h.length_eq
    simpa [length_prefixesFrom, Expr.localeOf] using this
  locale_injective := heap_locale_injective
  headStep := BaseStep
  fillItem := ECtxItem.fill
  val_stuck := val_head_stuck
  fill_item_val := fill_item_val
  fill_item_inj := fill_item_inj
  fill_item_no_val_inj := fill_item_no_val_inj
  head_ctx_step_val := head_ctx_step_val
  locale_step := locale_step_same
  locale_fill := locale_fill

/-- The ectx language of HeapLang (Rocq canonical structure `heap_ectx_lang`); this is the
generic instance `EctxiLanguage.instEctxLanguage`. -/
@[rocq_alias trillium.heap_lang.heap_ectx_lang]
abbrev heapEctxLang : EctxLanguage Expr Val (List ECtxItem) State BaseLocale := inferInstance

/-- HeapLang as a Trillium language (Rocq canonical structure `heap_lang`); this is the
generic instance `EctxLanguage.instLanguage`. -/
@[rocq_alias trillium.heap_lang.heap_lang]
abbrev heapLang : Language Expr Val (List ECtxItem) State BaseLocale := inferInstance

@[simp]
theorem headStep_eq : (headStep : Expr → State → Expr → State → List Expr → Prop) = BaseStep :=
  rfl

@[simp]
theorem fillItem_eq : (fillItem : ECtxItem → Expr → Expr) = ECtxItem.fill := rfl

@[simp]
theorem localeOf_eq (c : List Expr) (e : Expr) : localeOf c e = c.length := rfl

theorem configStep_eq : LanguageCore.configStep (Expr := Expr) = contextStep := rfl

/-- The following lemma is not provable using the axioms of `EctxiLanguage`: the proof
requires a case analysis over context items, which in all cases yields a non-value. -/
@[rocq_alias trillium.heap_lang.to_val_fill_some]
theorem to_val_fill_some (K : List ECtxItem) (e : Expr) (v : Val) :
    toVal (fill K e) = some v → K = [] ∧ e = .val v := by
  intro h
  cases K with
  | nil => exact ⟨rfl, (of_to_val h).symm⟩
  | cons Ki K =>
    exfalso
    have hnv : toVal (Ki.fill e) = none := by cases Ki <;> rfl
    have := EctxiLanguage.fill_not_val K hnv
    rw [EctxiLanguage.fill_cons] at h
    rw [fillItem_eq] at h
    simp_all

@[rocq_alias trillium.heap_lang.prim_step_to_val_is_head_step]
theorem prim_step_to_val_is_head_step (e : Expr) (σ1 : State) (w : Val) (σ2 : State)
    (efs : List Expr) : primStep e σ1 (.val w) σ2 efs → BaseStep e σ1 (.val w) σ2 efs := by
  rintro ⟨K, e1, e2, rfl, h2, hs⟩
  have h3 : toVal (fill K e2) = some w := by rw [← h2]; rfl
  obtain ⟨rfl, rfl⟩ := to_val_fill_some K e2 w h3
  exact hs

/-- If `e1` makes a head step to a value under some state `σ1` then any head step from `e1`
under any other state `σ1'` must necessarily be to a value. -/
@[rocq_alias trillium.heap_lang.head_step_to_val]
theorem head_step_to_val {e1 : Expr} {σ1 e2 σ2 efs σ1' e2' σ2' efs'} :
    BaseStep e1 σ1 e2 σ2 efs → BaseStep e1 σ1' e2' σ2' efs' →
    (e2.toVal).isSome → (e2'.toVal).isSome := by
  intro h1 h2
  cases h1 <;> cases h2 <;> simp_all

end Trillium.HeapLang
