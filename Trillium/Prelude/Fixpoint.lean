/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Iris.Std.RocqPorting

/-!
# Greatest fixpoints of monotone predicate transformers

Port of `trillium/prelude/fixpoint.v`.

`GFX Ψ` is the (impredicatively defined) greatest fixpoint of a predicate transformer
`Ψ : (A → Prop) → (A → Prop)`: the union of all post-fixpoints of `Ψ`. For monotone `Ψ` it is a
fixpoint (`GFX.fixpoint`), and by construction it contains every post-fixpoint, which gives the
coinduction principle (`GFX.coind`: just the constructor of the existential).
-/

namespace Trillium

/-- Monotonicity of a predicate transformer (Rocq `monotone`). -/
@[rocq_alias trillium.monotone]
def PredMonotone {A : Type _} (Ψ : (A → Prop) → (A → Prop)) : Prop :=
  ∀ P Q : A → Prop, (∀ x, P x → Q x) → ∀ x, Ψ P x → Ψ Q x

/-- The greatest fixpoint of `Ψ`: the union of all post-fixpoints of `Ψ`. -/
@[rocq_alias trillium.GFX]
def GFX {A : Type _} (Ψ : (A → Prop) → (A → Prop)) : A → Prop :=
  fun x => ∃ P : A → Prop, P x ∧ ∀ x, P x → Ψ P x

namespace GFX

variable {A : Type _} {Ψ : (A → Prop) → (A → Prop)}

/-- Coinduction: every post-fixpoint is below `GFX Ψ`. (Not a separate Rocq lemma; this is how
Rocq proofs build `GFX` proofs, by `exists P`.) -/
theorem coind (P : A → Prop) (HP : ∀ x, P x → Ψ P x) {x : A} (Hx : P x) : GFX Ψ x :=
  ⟨P, Hx, HP⟩

@[rocq_alias trillium.GFX_post_fixpoint]
theorem post_fixpoint (Hmono : PredMonotone Ψ) : ∀ x, GFX Ψ x → Ψ (GFX Ψ) x := by
  rintro x ⟨P, HP, HΨP⟩
  exact Hmono P _ (fun y Hy => ⟨P, Hy, HΨP⟩) x (HΨP x HP)

@[rocq_alias trillium.GFX_fixpoint]
theorem fixpoint (Hmono : PredMonotone Ψ) : ∀ x, Ψ (GFX Ψ) x ↔ GFX Ψ x := by
  intro x
  constructor
  · intro HΨ
    refine ⟨Ψ (GFX Ψ), HΨ, fun y Hy => ?_⟩
    exact Hmono _ _ (post_fixpoint Hmono) y Hy
  · exact post_fixpoint Hmono x

end GFX

end Trillium
