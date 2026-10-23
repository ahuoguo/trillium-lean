/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Iris.Std.RocqPorting
import Iris.Std.Relation
import Mathlib.Logic.Relation
import Mathlib.Order.Defs.Unbundled

/-!
# Relation helpers
Port of `fairness/utils_relations.v`.

Representation decisions:
* `relation A` is `A → A → Prop`.
* stdpp's `relations.nsteps R n` is iris-lean's `Relation.Iterate R n` (built by appending
  steps on the right; `Relation.Iterate.head` appends on the left).
* Rocq's `clos_refl`/`clos_trans_1n`/`clos_trans_n1` are Mathlib's `Relation.ReflGen` and
  `Relation.TransGen`.
* stdpp's `strict R x y` (`R x y ∧ ¬ R y x`) is `Trillium.Fairness.strict`.
* Rocq `Proper` instances are stated as plain monotonicity lemmas.
-/

namespace Trillium.Fairness

/-- stdpp's `strict R`: the strict part of a relation. -/
def strict {A : Type _} (R : A → A → Prop) (x y : A) : Prop := R x y ∧ ¬ R y x

section RelationsUtils

variable {A : Type _}

/-- Relation composition. -/
@[rocq_alias trillium.fairness.rel_compose]
def relCompose (R1 R2 : A → A → Prop) : A → A → Prop :=
  fun x y => ∃ z, R1 x z ∧ R2 z y

/-- Inclusion of relations (Rocq instance `SubsetEq (relation A)`). -/
@[rocq_alias trillium.fairness.rel_subseteq]
def relSubseteq (R1 R2 : A → A → Prop) : Prop :=
  ∀ x y, R1 x y → R2 x y

@[rocq_alias trillium.fairness.rel_compose_mono]
theorem relCompose_mono {R1 R1' R2 R2' : A → A → Prop}
    (H1 : relSubseteq R1 R1') (H2 : relSubseteq R2 R2') :
    relSubseteq (relCompose R1 R2) (relCompose R1' R2') :=
  fun _ _ ⟨z, h1, h2⟩ => ⟨z, H1 _ _ h1, H2 _ _ h2⟩

@[rocq_alias trillium.fairness.nsteps_0]
theorem nsteps_0 (R : A → A → Prop) (x y : A) : Relation.Iterate R 0 x y ↔ x = y := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .rfl _

@[rocq_alias trillium.fairness.nsteps_1]
theorem nsteps_1 (R : A → A → Prop) (x y : A) : Relation.Iterate R 1 x y ↔ R x y := by
  constructor
  · intro h
    cases h with
    | tail z h hz => cases h; exact hz
  · exact Relation.Iterate.once

@[rocq_alias trillium.fairness.rel_compose_nsteps_next']
theorem relCompose_nsteps_next' (r : A → A → Prop) (n : Nat) :
    ∀ x y, relCompose r (Relation.Iterate r n) x y ↔ Relation.Iterate r (n + 1) x y := by
  intro x y
  constructor
  · rintro ⟨z, h1, h2⟩; exact h2.head h1
  · intro h
    induction n generalizing y with
    | zero =>
      rw [nsteps_1] at h
      exact ⟨y, h, .rfl _⟩
    | succ n IH =>
      cases h with
      | tail w h hw =>
        obtain ⟨z, hz, hzw⟩ := IH w h
        exact ⟨z, hz, .tail w hzw hw⟩

@[rocq_alias trillium.fairness.rel_compose_assoc]
theorem relCompose_assoc (R1 R2 R3 : A → A → Prop) (x y : A) :
    relCompose (relCompose R1 R2) R3 x y ↔ relCompose R1 (relCompose R2 R3) x y :=
  ⟨fun ⟨_, ⟨z, h1, h2⟩, h3⟩ => ⟨z, h1, _, h2, h3⟩,
   fun ⟨_, h1, z, h2, h3⟩ => ⟨z, ⟨_, h1, h2⟩, h3⟩⟩

@[rocq_alias trillium.fairness.rel_compose_nsteps_plus]
theorem relCompose_nsteps_plus (r : A → A → Prop) (n m : Nat) :
    ∀ x y, relCompose (Relation.Iterate r n) (Relation.Iterate r m) x y ↔
      Relation.Iterate r (n + m) x y := by
  induction n with
  | zero =>
    intro x y
    simp only [relCompose, nsteps_0, Nat.zero_add]
    exact ⟨fun ⟨_, e, h⟩ => e ▸ h, fun h => ⟨x, rfl, h⟩⟩
  | succ n IHn =>
    intro x y
    rw [show n + 1 + m = (n + m) + 1 by omega, ← relCompose_nsteps_next']
    constructor
    · rintro ⟨z, h1, h2⟩
      obtain ⟨w, hw, h1'⟩ := (relCompose_nsteps_next' r n x z).2 h1
      exact ⟨w, hw, (IHn w y).1 ⟨z, h1', h2⟩⟩
    · rintro ⟨w, hw, h⟩
      obtain ⟨z, h1, h2⟩ := (IHn w y).2 h
      exact ⟨z, (relCompose_nsteps_next' r n x z).1 ⟨w, hw, h1⟩, h2⟩

@[rocq_alias trillium.fairness.rel_compose_nsteps_next]
theorem relCompose_nsteps_next (r : A → A → Prop) (n : Nat) :
    ∀ x y, relCompose (Relation.Iterate r n) r x y ↔ Relation.Iterate r (n + 1) x y := by
  intro x y
  rw [← relCompose_nsteps_plus r n 1]
  simp only [relCompose, nsteps_1]

@[rocq_alias trillium.fairness.rel_subseteq_po]
instance relSubseteq_po : IsPreorder (A → A → Prop) relSubseteq where
  refl _ _ _ h := h
  trans _ _ _ h1 h2 x y h := h2 x y (h1 x y h)

@[rocq_alias trillium.fairness.strict_not_both]
theorem strict_not_both (R : A → A → Prop) (x y : A) :
    strict R x y → strict R y x → False :=
  fun ⟨h, _⟩ ⟨_, h'⟩ => h' h

@[rocq_alias trillium.fairness.nsteps_mono]
theorem nsteps_mono (n : Nat) {R1 R2 : A → A → Prop} (H : relSubseteq R1 R2) :
    relSubseteq (Relation.Iterate R1 n) (Relation.Iterate R2 n) := by
  intro x y h
  induction h with
  | rfl => exact .rfl _
  | tail z _ hz IH => exact .tail z IH (H _ _ hz)

@[rocq_alias trillium.fairness.clos_refl_nsteps]
theorem clos_refl_nsteps (R : A → A → Prop) (x y : A) (CR : Relation.ReflGen R x y) :
    ∃ n, Relation.Iterate R n x y := by
  cases CR with
  | refl => exact ⟨0, .rfl _⟩
  | single h => exact ⟨1, Relation.Iterate.once h⟩

/-- Rocq's `Proper ((eq ==> eq ==> impl) ==> eq ==> (eq ==> eq ==> impl)) nsteps`. -/
@[rocq_alias trillium.fairness.nsteps_impl]
theorem nsteps_impl {R1 R2 : A → A → Prop} (H : ∀ x y, R1 x y → R2 x y) (n : Nat) (x y : A) :
    Relation.Iterate R1 n x y → Relation.Iterate R2 n x y :=
  nsteps_mono n H x y

/-- Rocq's `Proper (E ==> E ==> impl) (clos_trans_1n _ R)`. -/
@[rocq_alias trillium.fairness.clos_trans_1n_proper_impl]
theorem clos_trans_1n_proper_impl (R E : A → A → Prop) (REFL_E : ∀ x, E x x)
    (PR : ∀ x1 x2, E x1 x2 → ∀ y1 y2, E y1 y2 → R x1 y1 → R x2 y2) :
    ∀ x1 x2, E x1 x2 → ∀ y1 y2, E y1 y2 →
      Relation.TransGen R x1 y1 → Relation.TransGen R x2 y2 := by
  intro x1 x2 Ex y1 y2 Ey TR
  induction TR generalizing y2 with
  | single h => exact .single (PR _ _ Ex _ _ Ey h)
  | tail _ h IH => exact .tail (IH _ (REFL_E _)) (PR _ _ (REFL_E _) _ _ Ey h)

/-- Rocq's `Proper (E ==> E ==> iff) (clos_trans_1n _ R)`. -/
@[rocq_alias trillium.fairness.clos_trans_1n_proper_iff]
theorem clos_trans_1n_proper_iff (R E : A → A → Prop)
    (SYM_E : ∀ x y, E x y → E y x) (REFL_E : ∀ x, E x x)
    (PR : ∀ x1 x2, E x1 x2 → ∀ y1 y2, E y1 y2 → (R x1 y1 ↔ R x2 y2)) :
    ∀ x1 x2, E x1 x2 → ∀ y1 y2, E y1 y2 →
      (Relation.TransGen R x1 y1 ↔ Relation.TransGen R x2 y2) := by
  have PR' : ∀ x1 x2, E x1 x2 → ∀ y1 y2, E y1 y2 → R x1 y1 → R x2 y2 :=
    fun x1 x2 Ex y1 y2 Ey => (PR x1 x2 Ex y1 y2 Ey).1
  intro x1 x2 Ex y1 y2 Ey
  exact ⟨clos_trans_1n_proper_impl R E REFL_E PR' _ _ Ex _ _ Ey,
    clos_trans_1n_proper_impl R E REFL_E PR' _ _ (SYM_E _ _ Ex) _ _ (SYM_E _ _ Ey)⟩

#rocq_ignore trillium.fairness.clos_trans_tn1_t1n_iff
  "Both `clos_trans_n1` and `clos_trans_1n` are Mathlib's `Relation.TransGen`; the equivalence is `Iff.rfl`"

end RelationsUtils

end Trillium.Fairness
