/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Iris.Std.RocqPorting
import Mathlib.Data.Subtype

/-!
# Subtype utilities

Port of `trillium/prelude/sigma.v`.

Rocq's `sig P` / `{x | P x}` is Lean's `Subtype P` / `{x // P x}`. Since proofs of propositions
are definitionally equal in Lean, stdpp's `ProofIrrel` hypotheses are dropped, and decidability of
equality is obtained classically where Rocq assumed `EqDecision`.
-/

namespace Trillium

attribute [rocq_alias trillium.sig_eq] Subtype.ext

/-- Pair two subtype elements into an element of the product subtype. -/
@[rocq_alias trillium.sig_prod_and]
def sigProdAnd {A B : Type _} {P : A → Prop} {Q : B → Prop} (a : {x : A // P x})
    (b : {x : B // Q x}) : {x : A × B // P x.1 ∧ Q x.2} :=
  ⟨(a.1, b.1), a.2, b.2⟩

@[rocq_alias trillium.sig_prod_or_l]
def sigProdOrL {A : Type _} {P Q : A → Prop} (a : {x : A // P x}) : {x : A // P x ∨ Q x} :=
  ⟨a.1, .inl a.2⟩

@[rocq_alias trillium.sig_prod_or_r]
def sigProdOrR {A : Type _} {P Q : A → Prop} (a : {x : A // Q x}) : {x : A // P x ∨ Q x} :=
  ⟨a.1, .inr a.2⟩

@[rocq_alias trillium.sig_and]
def sigAnd {A : Type _} {P Q : A → Prop} (a : {x : A // P x}) (HQ : Q a.1) :
    {x : A // P x ∧ Q x} :=
  ⟨a.1, a.2, HQ⟩

/-- Keep the elements of `enum` that also satisfy `Q`. -/
@[rocq_alias trillium.sig_and_list]
def sigAndList {A : Type _} (P Q : A → Prop) [DecidablePred Q] :
    List {x // P x} → List {x // P x ∧ Q x}
  | [] => []
  | x :: xs => if HQ : Q x.1 then sigAnd x HQ :: sigAndList P Q xs else sigAndList P Q xs

/-- (Rocq assumes `EqDecision A` and `ProofIrrel` instances, which are not needed in Lean.) -/
@[rocq_alias trillium.sig_and_list_le]
theorem sigAndList_le {A : Type _} (P Q : A → Prop) [DecidablePred Q]
    (enum : List {x // P x}) :
    ∀ x HQ, sigAnd x HQ ∈ sigAndList P Q enum → x ∈ enum := by
  intro x HQ Hin
  induction enum with
  | nil => simp [sigAndList] at Hin
  | cons a enum IH =>
    refine List.mem_cons.mpr ?_
    by_cases Hxa : x = a
    · exact .inl Hxa
    refine .inr ?_
    simp only [sigAndList] at Hin
    split at Hin
    · rcases List.mem_cons.mp Hin with Hin | Hin
      · exact absurd (Subtype.ext (congrArg (fun y => y.1) Hin)) Hxa
      · exact IH Hin
    · exact IH Hin

end Trillium
