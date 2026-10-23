/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.Fairness.Utils
import Trillium.Prelude.Finitary

/-!
# Finite branching via list approximations
Port of `fairness/fin_branch.v`.

`list_approx P` is the type of lists containing every element satisfying `P`; `nsteps` is
iris-lean's `Relation.Iterate`.
-/

namespace Trillium.Fairness

section ListApprox

variable {A : Type _}

/-- A list containing every element satisfying `P`. -/
@[rocq_alias trillium.fairness.list_approx]
def listApprox (P : A → Prop) : Type _ := {l : List A // ∀ a, P a → a ∈ l}

/-- A list containing every element reachable from `a` in `n` steps of `R`. -/
@[rocq_alias trillium.fairness.list_approx_repeat]
def listApproxRepeat (R : A → A → Prop) (APX : ∀ a, listApprox (R a)) : Nat → A → List A
  | 0, a => [a]
  | n + 1, a => (APX a).1.flatMap (listApproxRepeat R APX n)

@[rocq_alias trillium.fairness.list_approx_repeat_spec]
theorem listApproxRepeat_spec (R : A → A → Prop) (APX : ∀ a, listApprox (R a)) (n : Nat)
    (a : A) : ∀ b, Relation.Iterate R n a b → b ∈ listApproxRepeat R APX n a := by
  induction n generalizing a with
  | zero =>
    intro b h
    rw [nsteps_0] at h
    simp [listApproxRepeat, h]
  | succ n IHn =>
    intro b h
    obtain ⟨c, STEP, STEPS⟩ := (relCompose_nsteps_next' R n a b).2 h
    simp only [listApproxRepeat, List.mem_flatMap]
    exact ⟨c, (APX a).2 c STEP, IHn c b STEPS⟩

end ListApprox

section SmallerCardLA

variable {A : Type _} (P : A → Prop)

#rocq_ignore trillium.fairness.P_PI
  "`ProofIrrel (P a)` instance; proof irrelevance is definitional in Lean"

@[rocq_alias trillium.fairness.list_approx_smaller_card]
theorem listApprox_smaller_card (APX : listApprox P) : SmallerCard {a // P a} Nat :=
  finite_smaller_card_nat (in_list_finite APX.1 APX.2)

end SmallerCardLA

end Trillium.Fairness
