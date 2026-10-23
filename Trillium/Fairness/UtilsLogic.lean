/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Iris.Std.RocqPorting
import Mathlib.Order.Bounds.Defs
import Mathlib.Data.PNat.Basic

/-!
# Logic helpers
Port of `fairness/utils_logic.v`.

Representation decisions:
* Rocq's `ClassicalFacts.Minimal P n` (`P n ∧ ∀ k, P k → n ≤ k`) is Mathlib's
  `IsLeast {n | P n} n`, and `ClassicalFacts.Minimization_Property P` is unfolded.
* `Decision P` is `Decidable P`; stdpp's `is_Some o` is `o.isSome` (a `Bool` coerced to `Prop`).
* `BinNums.positive` is Mathlib's `ℕ+`.
-/

namespace Trillium.Fairness

section LogicHelpers

@[rocq_alias trillium.fairness.ex2_comm]
theorem ex2_comm {A B : Sort _} (P : A → B → Prop) :
    (∃ (a : A) (b : B), P a b) ↔ (∃ (b : B) (a : A), P a b) :=
  ⟨fun ⟨a, b, h⟩ => ⟨b, a, h⟩, fun ⟨b, a, h⟩ => ⟨a, b, h⟩⟩

@[rocq_alias trillium.fairness.iff_and_impl_helper]
theorem iff_and_impl_helper {A B : Prop} (AB : A → B) : A ∧ B ↔ A :=
  ⟨And.left, fun a => ⟨a, AB a⟩⟩

@[rocq_alias trillium.fairness.iff_True_helper]
theorem iff_true_helper {A : Prop} : (A ↔ True) ↔ A := by tauto

@[rocq_alias trillium.fairness.iff_False_helper]
theorem iff_false_helper {A : Prop} : (A ↔ False) ↔ ¬A := by tauto

@[rocq_alias trillium.fairness.ex_and_comm]
theorem ex_and_comm {T : Sort _} (A : Prop) (B : T → Prop) :
    (∃ t, A ∧ B t) ↔ A ∧ ∃ t, B t :=
  ⟨fun ⟨t, a, b⟩ => ⟨a, t, b⟩, fun ⟨a, t, b⟩ => ⟨t, a, b⟩⟩

@[rocq_alias trillium.fairness.ex_prod]
theorem ex_prod {A B : Type _} (P : A × B → Prop) :
    (∃ ab, P ab) ↔ (∃ a b, P (a, b)) :=
  ⟨fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩, fun ⟨a, b, h⟩ => ⟨(a, b), h⟩⟩

@[rocq_alias trillium.fairness.ex_prod']
theorem ex_prod' {A B : Type _} (P : A → B → Prop) :
    (∃ a b, P a b) ↔ (∃ ab : A × B, P ab.1 ab.2) :=
  ⟨fun ⟨a, b, h⟩ => ⟨(a, b), h⟩, fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩⟩

@[rocq_alias trillium.fairness.ex_proper3]
theorem ex_proper3 {A B C : Sort _} (P Q : A → B → C → Prop)
    (EQUIV : ∀ a b c, P a b c ↔ Q a b c) :
    (∃ a b c, P a b c) ↔ (∃ a b c, Q a b c) :=
  ⟨fun ⟨a, b, c, h⟩ => ⟨a, b, c, (EQUIV a b c).1 h⟩,
   fun ⟨a, b, c, h⟩ => ⟨a, b, c, (EQUIV a b c).2 h⟩⟩

@[rocq_alias trillium.fairness.ex_det_iff]
theorem ex_det_iff {A : Sort _} (P : A → Prop) (a : A)
    (DET : ∀ a', P a' → a' = a) :
    (∃ a', P a') ↔ P a :=
  ⟨fun ⟨a', h⟩ => DET a' h ▸ h, fun h => ⟨a, h⟩⟩

@[rocq_alias trillium.fairness.iff_and_pre]
theorem iff_and_pre {A B C : Prop} (BC : A → (B ↔ C)) : A ∧ B ↔ A ∧ C := by
  tauto

@[rocq_alias trillium.fairness.curry_uncurry_prop]
theorem curry_uncurry_prop {A B C : Prop} : (A → B → C) ↔ (A ∧ B → C) := by
  tauto

@[rocq_alias trillium.fairness.forall_eq_gen]
theorem forall_eq_gen {A : Sort _} (P : A → Prop) :
    ∀ a, P a ↔ (∀ a', a' = a → P a') :=
  fun _ => ⟨fun h _ e => e ▸ h, fun h => h _ rfl⟩

@[rocq_alias trillium.fairness.exist_impl_forall]
theorem exist_impl_forall {A : Sort _} {P : A → Prop} {Q : Prop} :
    ((∃ x, P x) → Q) ↔ (∀ x, P x → Q) :=
  ⟨fun h x px => h ⟨x, px⟩, fun h ⟨x, px⟩ => h x px⟩

@[rocq_alias trillium.fairness.forall_prod_helper]
theorem forall_prod_helper {A B : Type _} (P : A → B → Prop) :
    (∀ a b, P a b) ↔ (∀ ab : A × B, P ab.1 ab.2) :=
  ⟨fun h ab => h ab.1 ab.2, fun h a b => h (a, b)⟩

@[rocq_alias trillium.fairness.impl_iff_intro]
theorem impl_iff_intro {A B C : Prop} (PRE : A → (B ↔ C)) : (A → B) ↔ (A → C) := by
  tauto

end LogicHelpers

/-- The `m` returned is the least `n` satisfying `P`. -/
@[rocq_alias trillium.fairness.min_prop_dec_impl]
def minPropDecImpl (P : Nat → Prop) [DEC : ∀ n, Decidable (P n)] :
    ∀ n, P n → {m // IsLeast {n | P n} m} := by
  intro n Pn
  have MIN' : ∀ p, p ≤ n + 1 →
      (PSum {m // IsLeast {n | P n} m} (∀ k, k < p → ¬ P k)) := by
    intro p
    induction p with
    | zero => intro _; exact .inr (fun k hk => absurd hk (Nat.not_lt_zero k))
    | succ p IHp =>
      intro H
      match IHp (by omega) with
      | .inl m => exact .inl m
      | .inr n0 =>
        if hp : P p then
          exact .inl ⟨p, hp, fun k Pk => by
            rcases Nat.lt_or_ge k p with h | h
            · exact absurd Pk (n0 k h)
            · exact h⟩
        else
          exact .inr fun k hk => by
            rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | rfl
            · exact n0 k h
            · exact hp
  match MIN' (n + 1) le_rfl with
  | .inl m => exact m
  | .inr n0 => exact absurd Pn (n0 n (Nat.lt_succ_self n))

/-- Rocq's `ClassicalFacts.Minimization_Property P`, unfolded. -/
@[rocq_alias trillium.fairness.min_prop_dec]
theorem min_prop_dec (P : Nat → Prop) [∀ n, Decidable (P n)] :
    ∀ n, P n → ∃ m, IsLeast {n | P n} m :=
  fun n Pn => ⟨_, (minPropDecImpl P n Pn).2⟩

#rocq_ignore trillium.fairness.Minimal_proper
  "Rocq `Proper` instance for setoid rewriting under `Minimal`; Lean rewrites with `propext`/`funext`"

@[rocq_alias trillium.fairness.Minimal_pos]
def minimalPos (P : ℕ+ → Prop) (n : ℕ+) : Prop :=
  P n ∧ ∀ k, P k → n ≤ k

@[rocq_alias trillium.fairness.min_prop_dec_impl_pos]
def minPropDecImplPos (P : ℕ+ → Prop) [∀ n, Decidable (P n)] :
    ∀ n, P n → {m : ℕ+ // minimalPos P m} := by
  intro n Pn
  let Q : Nat → Prop := fun k => P (Nat.toPNat' k)
  have hQ : Q (n : Nat) := by simpa [Q] using Pn
  obtain ⟨m, Pm, MINm⟩ := minPropDecImpl Q n hQ
  refine ⟨Nat.toPNat' m, Pm, fun k Pk => ?_⟩
  have := MINm (show Q k by simpa [Q] using Pk)
  rw [← PNat.coe_le_coe]
  rcases m with _ | m
  · simp only [Nat.toPNat', Nat.succPNat_coe]; exact k.pos
  · simpa using this

/-- Transport decidability along an equivalence (this is core's `decidable_of_iff`). -/
@[rocq_alias trillium.fairness.Decision_iff_impl]
def decisionIffImpl (P Q : Prop) (PQ : P ↔ Q) [DEC_P : Decidable P] : Decidable Q :=
  decidable_of_iff P PQ

/-- Decidability of `∃ a, P a` when all witnesses lie in a known list. Not an instance, since
the list `l` cannot be inferred. -/
@[rocq_alias trillium.fairness.ex_fin_dec]
def exFinDec {T : Type _} (P : T → Prop) (l : List T)
    [DEC : ∀ a, Decidable (P a)] (IN : ∀ a, P a → a ∈ l) : Decidable (∃ a, P a) :=
  if h : ∃ a ∈ l, P a then
    .isTrue (let ⟨a, _, pa⟩ := h; ⟨a, pa⟩)
  else
    .isFalse fun ⟨a, pa⟩ => h ⟨a, IN a pa, pa⟩

/-- Useful for rewriting in equivalences. -/
@[rocq_alias trillium.fairness.is_Some_Some_True]
theorem isSome_some_iff_true {A : Type _} (a : A) : (some a).isSome ↔ True := by simp

/-- Useful for rewriting in equivalences. -/
@[rocq_alias trillium.fairness.is_Some_None_False]
theorem isSome_none_iff_false {A : Type _} : (none : Option A).isSome ↔ False := by simp

end Trillium.Fairness
