/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Iris.Std.RocqPorting
import Mathlib.Order.Defs.Unbundled

/-!
# Natural numbers with infinity
Port of `fairness/nat_omega.v` (adapted from `HahnOmega` in coq-hahn).

The Rocq type `nat_omega` (constructors `NOinfinity`, `NOnum n`) is `NatOmega` with
constructors `NatOmega.infinity` and `NatOmega.num n`; the Rocq module `NOmega` becomes the
namespace `NatOmega`. The `lia_NO` tactics are not ported: Lean proofs do `cases` + `omega`.
-/

namespace Trillium.Fairness

/-- Natural numbers extended with infinity. -/
@[rocq_alias trillium.fairness.nat_omega]
inductive NatOmega where
  | infinity
  | num (n : Nat)

namespace NatOmega

@[rocq_alias trillium.fairness.nomega_eqdec]
instance instDecidableEq : DecidableEq NatOmega
  | infinity, infinity => .isTrue rfl
  | infinity, num _ => .isFalse nofun
  | num _, infinity => .isFalse nofun
  | num n, num m =>
    if h : n = m then .isTrue (h ▸ rfl) else .isFalse fun e => h (by injection e)

#rocq_ignore trillium.fairness.NOmega.t "Type alias for `nat_omega` inside the Rocq module; use `NatOmega`"

@[rocq_alias trillium.fairness.NOmega.zero]
def zero : NatOmega := num 0

@[rocq_alias trillium.fairness.NOmega.one]
def one : NatOmega := num 1

@[rocq_alias trillium.fairness.NOmega.two]
def two : NatOmega := num 2

@[rocq_alias trillium.fairness.NOmega.succ]
def succ : NatOmega → NatOmega
  | infinity => infinity
  | num n => num (n + 1)

@[rocq_alias trillium.fairness.NOmega.pred]
def pred : NatOmega → NatOmega
  | infinity => infinity
  | num n => num (Nat.pred n)

@[rocq_alias trillium.fairness.NOmega.add]
def add : NatOmega → NatOmega → NatOmega
  | num n, num m => num (n + m)
  | _, _ => infinity

@[rocq_alias trillium.fairness.NOmega.double]
def double : NatOmega → NatOmega
  | num n => num (2 * n)
  | _ => infinity

@[rocq_alias trillium.fairness.NOmega.sub]
def sub : NatOmega → NatOmega → NatOmega
  | num n, num m => num (n - m)
  | num _, infinity => num 0
  | infinity, _ => infinity

@[rocq_alias trillium.fairness.NOmega.eqb]
def eqb : NatOmega → NatOmega → Bool
  | num n, num m => n == m
  | infinity, infinity => true
  | _, _ => false

@[rocq_alias trillium.fairness.NOmega.ltb]
def ltb : NatOmega → NatOmega → Bool
  | num n, num m => Nat.blt n m
  | num _, infinity => true
  | infinity, _ => false

@[rocq_alias trillium.fairness.NOmega.max]
def max : NatOmega → NatOmega → NatOmega
  | num n, num m => num (Nat.max n m)
  | _, _ => infinity

@[rocq_alias trillium.fairness.NOmega.min]
def min : NatOmega → NatOmega → NatOmega
  | num n, num m => num (Nat.min n m)
  | num n, infinity => num n
  | infinity, m => m

@[rocq_alias trillium.fairness.NOmega.le]
def le : NatOmega → NatOmega → Prop
  | _, infinity => True
  | num n, num m => n ≤ m
  | _, _ => False

@[rocq_alias trillium.fairness.NOmega.nomega_le_eqdec]
instance decidableLe : ∀ x y, Decidable (le x y)
  | _, infinity => inferInstanceAs (Decidable True)
  | num n, num m => inferInstanceAs (Decidable (n ≤ m))
  | infinity, num _ => inferInstanceAs (Decidable False)

/-- Rocq's `TotalOrder NOmega.le`: a reflexive, transitive, antisymmetric and total relation. -/
@[rocq_alias trillium.fairness.NOmega.NOmega_le_TO]
instance le_isLinearOrder : IsLinearOrder NatOmega le where
  refl x := by cases x <;> simp [le]
  trans x y z := by cases x <;> cases y <;> cases z <;> simp [le]; omega
  antisymm x y := by
    cases x <;> cases y <;> simp [le]
    omega
  total x y := by cases x <;> cases y <;> simp [le]; omega

@[rocq_alias trillium.fairness.NOmega.lt]
def lt : NatOmega → NatOmega → Prop
  | infinity, _ => False
  | num n, num m => n < m
  | num _, infinity => True

@[rocq_alias trillium.fairness.NOmega.lt_nat_l]
def ltNatL (n : Nat) : NatOmega → Prop
  | num m => n < m
  | infinity => True

@[rocq_alias trillium.fairness.NOmega.no_lt_nat_l_dec]
instance decidableLtNatL : ∀ x y, Decidable (ltNatL x y)
  | _, infinity => inferInstanceAs (Decidable True)
  | n, num m => inferInstanceAs (Decidable (n < m))

@[rocq_alias trillium.fairness.NOmega.sub_nat_l]
def subNatL (n : Nat) : NatOmega → Nat
  | num m => n - m
  | infinity => 0

@[rocq_alias trillium.fairness.NOmega.pred_succ]
theorem pred_succ (n : NatOmega) : pred (succ n) = n := by cases n <;> rfl

@[rocq_alias trillium.fairness.NOmega.pred_0]
theorem pred_0 : pred zero = zero := rfl

@[rocq_alias trillium.fairness.NOmega.add_0_l]
theorem add_0_l (n : NatOmega) : add zero n = n := by
  cases n <;> simp [add, zero]

@[rocq_alias trillium.fairness.NOmega.add_0_r]
theorem add_0_r (n : NatOmega) : add n zero = n := by
  cases n <;> simp [add, zero]

@[rocq_alias trillium.fairness.NOmega.sub_0_r]
theorem sub_0_r (n : NatOmega) : sub n zero = n := by
  cases n <;> simp [sub, zero]

@[rocq_alias trillium.fairness.NOmega.eqb_eq]
theorem eqb_eq (n m : NatOmega) : eqb n m = true ↔ n = m := by
  cases n <;> cases m <;> simp [eqb]

@[rocq_alias trillium.fairness.NOmega.ltb_lt]
theorem ltb_lt (n m : NatOmega) : ltb n m = true ↔ lt n m := by
  cases n <;> cases m <;> simp [ltb, lt]

@[rocq_alias trillium.fairness.NOmega.max_l]
theorem max_l (n m : NatOmega) : le m n → max n m = n := by
  cases n <;> cases m <;> simp [le, max, Nat.max_def]; omega

@[rocq_alias trillium.fairness.NOmega.max_r]
theorem max_r (n m : NatOmega) : le n m → max n m = m := by
  cases n <;> cases m <;> simp [le, max, Nat.max_def]; omega

@[rocq_alias trillium.fairness.NOmega.min_l]
theorem min_l (n m : NatOmega) : le n m → min n m = n := by
  cases n <;> cases m <;> simp [le, min, Nat.min_def]; omega

@[rocq_alias trillium.fairness.NOmega.min_r]
theorem min_r (n m : NatOmega) : le m n → min n m = m := by
  cases n <;> cases m <;> simp [le, min, Nat.min_def]; omega

@[rocq_alias trillium.fairness.NOmega.lt_irrefl]
theorem lt_irrefl (x : NatOmega) : ¬ lt x x := by
  cases x <;> simp [lt]

@[rocq_alias trillium.fairness.NOmega.succ_inj]
theorem succ_inj (n m : NatOmega) : succ n = succ m → n = m := by
  cases n <;> cases m <;> simp [succ]

@[rocq_alias trillium.fairness.NOmega.lt_le_incl]
theorem lt_le_incl (n m : NatOmega) : lt n m → le n m := by
  cases n <;> cases m <;> simp [lt, le]; omega

@[rocq_alias trillium.fairness.NOmega.lt_trans]
theorem lt_trans (n m p : NatOmega) : lt n m → lt m p → lt n p := by
  cases n <;> cases m <;> cases p <;> simp [lt]; omega

@[rocq_alias trillium.fairness.NOmega.le_trans]
theorem le_trans (n m p : NatOmega) : le n m → le m p → le n p := by
  cases n <;> cases m <;> cases p <;> simp [le]; omega

@[rocq_alias trillium.fairness.NOmega.lt_lt_nat]
theorem lt_lt_nat (n m : Nat) (k : NatOmega) : n < m → ltNatL m k → ltNatL n k := by
  cases k <;> simp [ltNatL]; omega

@[rocq_alias trillium.fairness.NOmega.le_lt_nat]
theorem le_lt_nat (n m : Nat) (k : NatOmega) : n ≤ m → ltNatL m k → ltNatL n k := by
  cases k <;> simp [ltNatL]; omega

@[rocq_alias trillium.fairness.NOmega.lt_trichotomy]
theorem lt_trichotomy (x y : NatOmega) : lt x y ∨ x = y ∨ lt y x := by
  cases x <;> cases y <;> simp [lt]; omega

@[rocq_alias trillium.fairness.NOmega.le_iff_not_lt_nat]
theorem le_iff_not_lt_nat (n : Nat) (x : NatOmega) : le x (num n) ↔ ¬ ltNatL n x := by
  cases x <;> simp [le, ltNatL]

@[rocq_alias trillium.fairness.NOmega.nomega_le_lt_eq]
theorem le_iff_lt_or_eq (x y : NatOmega) : le x y ↔ lt x y ∨ x = y := by
  cases x <;> cases y <;> simp [le, lt]; omega

end NatOmega

end Trillium.Fairness
