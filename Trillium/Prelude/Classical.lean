/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Iris.Std.RocqPorting

/-!
# Classical axioms

Port of `trillium/prelude/classical.v` and `trillium/prelude/classical_instances.v`.

Trillium axiomatizes functional extensionality, propositional extensionality and a
(type-theoretic) axiom of choice, and derives proof irrelevance, Hilbert's epsilon and excluded
middle from them. Lean's core already provides all of these (`funext` is a theorem, `propext` and
`Classical.choice` are axioms, proof irrelevance is definitional), so nothing is re-axiomatized
here: every declaration is recorded as ignored, naming its Lean replacement.

Downstream ports should use:
* `epsilon Hex` ↦ `Classical.choose Hex`, `epsilon_correct` ↦ `Classical.choose_spec`;
* `ExcludedMiddle` ↦ `Classical.em`, `NNP_P` ↦ `Classical.not_not.mp`;
* `make_decision P` ↦ `Classical.dec P` (or `open Classical` for the `Classical.propDecidable`
  instance);
* `make_proof_irrel` is unnecessary: proofs of a `Prop` are definitionally equal in Lean, so stdpp's
  `ProofIrrel` hypotheses are simply dropped.
-/

namespace Trillium

/-! ### `classical.v` -/

#rocq_ignore trillium.FunExt "Lean core theorem `funext` (derived from quotients)"
#rocq_ignore trillium.PropExt "Lean core axiom `propext`"
#rocq_ignore trillium.ProofIrrelevance
  "Lean core `proof_irrel`; proof irrelevance is definitional in Lean"
#rocq_ignore trillium.Choice
  "Lean core `Classical.axiomOfChoice`; the `sig` form is `⟨fun x => Classical.choose (h x), fun x => Classical.choose_spec (h x)⟩`"
#rocq_ignore trillium.epsilon "Lean core `Classical.choose`"
#rocq_ignore trillium.epsilon_correct "Lean core `Classical.choose_spec`"
#rocq_ignore trillium.ExcludedMiddle "Lean core `Classical.em`"
#rocq_ignore trillium.NNP_P "Lean core `Classical.not_not` (`Classical.not_not.mp`)"
#rocq_ignore trillium.P_NNP "Lean core `not_not_intro`"
#rocq_ignore trillium.contrapositive "Mathlib `not_imp_not` (`not_imp_not.mp`)"
#rocq_ignore trillium.not_exists_forall_not "Lean core `forall_not_of_not_exists`"
#rocq_ignore trillium.not_forall_exists_not "Lean core `Classical.not_forall` (`.mp`)"

/-! ### `classical_instances.v` -/

#rocq_ignore trillium.make_proof_irrel
  "proof irrelevance is definitional in Lean (`proof_irrel`); stdpp's `ProofIrrel` class is not needed"
#rocq_ignore trillium.make_decision
  "Lean core `Classical.dec` / the `Classical.propDecidable` instance (`open Classical`)"

end Trillium
