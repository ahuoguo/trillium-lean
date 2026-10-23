/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Iris.Std.RocqPorting
import Mathlib.Data.Seq.Basic

/-!
# Possibly-infinite lists
Port of `trillium/traces/infinite_trace.v`.

Rocq's `CoInductive inflist A := infnil | infcons (x : A) (il : inflist A)` is represented by
Mathlib's `Stream'.Seq A` (possibly-infinite sequences), via the reducible abbreviation
`Trillium.InfList`. Thus `infnil` is `Stream'.Seq.nil`, `infcons x il` is `Stream'.Seq.cons x il`,
case analysis is `cases il` (Mathlib's `@[cases_eliminator] Stream'.Seq.recOn`), corecursion is
`Stream'.Seq.corec`, and equality is proved by bisimulation (`Stream'.Seq.eq_of_bisim`).

The Rocq operations `inflist_take n il` and `inflist_drop n il` are Mathlib's
`Stream'.Seq.take n il` and `Stream'.Seq.drop il n` (note the argument order of `drop`), and the
`FMap` instance is `Stream'.Seq.map` (the `Functor Seq` instance). We write `il.take n` and
`il.drop n` throughout. Statements use `Stream'.Seq` directly rather than `InfList`, so that
`cases il` picks up Mathlib's `nil`/`cons` case eliminator.
-/

namespace Trillium

/-- Possibly-infinite lists (Rocq `inflist`), represented by Mathlib's `Stream'.Seq`. -/
@[rocq_alias trillium.inflist]
abbrev InfList (A : Type _) := Stream'.Seq A

attribute [rocq_alias trillium.inflist_take] Stream'.Seq.take
-- Rocq `inflist_drop n il` is `Stream'.Seq.drop il n` (arguments swapped).
attribute [rocq_alias trillium.inflist_drop] Stream'.Seq.drop
-- Rocq's `FMap inflist` instance is Mathlib's `Stream'.Seq.map` (`Functor Seq` instance).
attribute [rocq_alias trillium.ilist_fmap] Stream'.Seq.map

namespace InfList

open Stream'

variable {A B C : Type _}

/-- Rocq `inflist_unfold_fold` (the "frob" lemma for cofixpoints); in Lean it is the exhaustive
case split of a sequence. -/
@[rocq_alias trillium.inflist_unfold_fold]
theorem eq_nil_or_cons (il : Seq A) : il = .nil ∨ ∃ a il', il = .cons a il' := by
  cases il with
  | nil => exact .inl rfl
  | cons a il' => exact .inr ⟨a, il', rfl⟩

@[simp] theorem take_succ_nil (n : Nat) : (Seq.nil : Seq A).take (n + 1) = [] := rfl

@[rocq_alias trillium.inflist_take_add]
theorem take_add (n m : Nat) (il : Seq A) :
    il.take (n + m) = il.take n ++ (il.drop n).take m := by
  induction n generalizing il with
  | zero => simp
  | succ n IH =>
    cases il with
    | nil => simp
    | cons a il =>
      rw [Nat.add_right_comm, Seq.take_succ_cons, IH, Seq.take_succ_cons, Seq.drop_succ_cons]
      rfl

@[rocq_alias trillium.inflist_drop_add]
theorem drop_add (n m : Nat) (il : Seq A) : il.drop (n + m) = (il.drop m).drop n := by
  rw [Nat.add_comm, Seq.dropn_add]

/-- Two possibly-infinite lists have the same length (Rocq `inflist_same_length`). -/
@[rocq_alias trillium.inflist_same_length]
def SameLength (il : Seq A) (il' : Seq B) : Prop :=
  ∀ n, il.drop n = .nil ↔ il'.drop n = .nil

@[rocq_alias trillium.inflist_same_length_refl]
theorem SameLength.refl (il : Seq A) : SameLength il il := fun _ => .rfl

@[rocq_alias trillium.inflist_same_length_sym]
theorem SameLength.symm {il : Seq A} {il' : Seq B} :
    SameLength il il' → SameLength il' il := fun h n => (h n).symm

@[rocq_alias trillium.inflist_same_length_trans]
theorem SameLength.trans {il : Seq A} {il' : Seq B} {il'' : Seq C} :
    SameLength il il' → SameLength il' il'' → SameLength il il'' :=
  fun h h' n => (h n).trans (h' n)

@[rocq_alias trillium.inflist_same_length_nil]
theorem SameLength.nil : SameLength (.nil : Seq A) (.nil : Seq B) := by
  intro n; simp

@[rocq_alias trillium.inflist_same_length_nil_inv_l]
theorem not_sameLength_nil_cons (x : B) (il : Seq B) :
    ¬ SameLength (.nil : Seq A) (.cons x il) := by
  intro h
  have := (h 0).mp rfl
  exact Seq.cons_ne_nil this

@[rocq_alias trillium.inflist_same_length_nil_inv_r]
theorem not_sameLength_cons_nil (x : A) (il : Seq A) :
    ¬ SameLength (.cons x il) (.nil : Seq B) := by
  intro h
  have := (h 0).mpr rfl
  exact Seq.cons_ne_nil this

@[rocq_alias trillium.inflist_same_length_cons]
theorem sameLength_cons {x : A} {il : Seq A} {y : B} {il' : Seq B} :
    SameLength (.cons x il) (.cons y il') ↔ SameLength il il' := by
  constructor
  · intro h n
    simpa using h (n + 1)
  · intro h n
    cases n with
    | zero => simp [Seq.cons_ne_nil]
    | succ n => simpa using h n

@[rocq_alias trillium.inflist_same_length_drop]
theorem SameLength.drop (n : Nat) {il : Seq A} {il' : Seq B} :
    SameLength il il' → SameLength (il.drop n) (il'.drop n) := by
  intro h k
  rw [← drop_add, ← drop_add]
  exact h _

@[rocq_alias trillium.inflist_flength_map]
theorem sameLength_map (f : A → B) (il : Seq A) : SameLength il (il.map f) := by
  intro n
  induction n generalizing il with
  | zero => cases il <;> simp [Seq.map_cons, Seq.cons_ne_nil]
  | succ n IH => cases il <;> simp [Seq.map_cons, IH]

@[rocq_alias trillium.inflist_fmap_cons_inv]
theorem map_eq_cons_inv (f : A → B) (il : Seq A) (b : B) (il' : Seq B) :
    il.map f = .cons b il' → ∃ a il'', il = .cons a il'' ∧ b = f a ∧ il' = il''.map f := by
  cases il with
  | nil => simp [Seq.cons_ne_nil, eq_comm (a := Seq.nil)]
  | cons a il =>
    rw [Seq.map_cons]
    intro h
    obtain ⟨h1, h2⟩ := Seq.cons_injective2 h
    exact ⟨a, il, rfl, h1.symm, h2.symm⟩

@[rocq_alias trillium.inflist_take_of_same_length]
theorem length_take_of_sameLength (k : Nat) {il : Seq A} {il' : Seq B} :
    SameLength il il' → (il.take k).length = (il'.take k).length := by
  induction k generalizing il il' with
  | zero => simp
  | succ k IH =>
    intro h
    cases il with
    | nil =>
      cases il' with
      | nil => rfl
      | cons b il' => exact absurd h (not_sameLength_nil_cons _ _)
    | cons a il =>
      cases il' with
      | nil => exact absurd h (not_sameLength_cons_nil _ _)
      | cons b il' =>
        simp only [Seq.take_succ_cons, List.length_cons]
        rw [IH (sameLength_cons.mp h)]

end InfList

end Trillium
