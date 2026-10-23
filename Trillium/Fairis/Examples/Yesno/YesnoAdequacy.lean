/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.Fairis.Examples.Yesno.Yesno
import Trillium.Fairis.Adequacy
import Trillium.Fairis.FairnessFiniteness
import Trillium.Fairness.UtilsRelations

/-!
# Fair termination of the yes/no example
Port of `fairis/examples/yesno/yesno_adequacy.v`: the yes/no model is a fair terminating model
(ordered lexicographically by the counter and whose turn it is) and finitely branching, so every
fair execution of `start #N` terminates.

## Representation

* stdpp's `prod_relation R1 R2` is core's `Prod.RProd R1 R2` (an inductive with the single
  constructor `intro : R1 a₁ a₂ → R2 b₁ b₂ → RProd (a₁, b₁) (a₂, b₂)`), Rocq's
  `lexprod A B R1 R2` (on pairs) is core's `Prod.Lex R1 R2`, stdpp's `strict` is
  `Trillium.Fairness.strict`, `bool_le` is `(· ≤ ·)` on `Bool` (`false ≤ true`).
* stdpp's `lexico` on `nat * bool` is Mathlib's lexicographic order `toLex x < toLex y`.
* The order classes `Transitive`/`AntiSymm`/`PreOrder`/`PartialOrder` are Mathlib's
  `Transitive`, `Std.Antisymm`, `IsPreorder`, `IsPartialOrder`.
-/

namespace Trillium.Fairis.Yesno

open Iris Iris.BI Iris.ProofMode
open Trillium Trillium.Fairness Trillium.Fairis
open YN

section product_of_orders

variable {A B : Type _} (leA : A → A → Prop) (leB : B → B → Prop)

@[rocq_alias trillium.fairis.prod_trans]
theorem prod_trans : IsTrans A leA → IsTrans B leB → IsTrans (A × B) (Prod.RProd leA leB) := by
  intro tA tB
  constructor
  intro x y z H1 H2
  cases H1 with
  | intro h1 h2 =>
    cases H2 with
    | intro h3 h4 => exact .intro (_root_.trans h1 h3) (_root_.trans h2 h4)

@[rocq_alias trillium.fairis.wf_prod]
theorem wf_prod : WellFounded leA → WellFounded leB → WellFounded (Prod.RProd leA leB) := by
  intro wfA wfB
  constructor
  rintro ⟨x, y⟩
  induction (wfA.apply x) generalizing y with
  | intro x _ IHx =>
    induction (wfB.apply y) with
    | intro y _ IHy =>
      constructor
      rintro ⟨x', y'⟩ H
      cases H with
      | intro h1 h2 => exact IHx x' h1 y'

@[rocq_alias trillium.fairis.wf_prod_strict]
theorem wf_prod_strict [IsTrans A leA] :
    WellFounded (strict leA) → WellFounded (strict leB) →
    WellFounded (strict (Prod.RProd leA leB)) := by
  intro wfA wfB
  constructor
  rintro ⟨x, y⟩
  induction (wfA.apply x) generalizing y with
  | intro x _ IHx =>
    suffices H : ∀ y x0, (∀ x', strict leA x' x0 → ∀ y,
        Acc (strict (Prod.RProd leA leB)) (x', y)) →
        Acc (strict (Prod.RProd leA leB)) (x0, y) from H y x IHx
    intro y
    induction (wfB.apply y) with
    | intro y _ IHy =>
      intro x0 IH0
      constructor
      rintro ⟨x', y'⟩ ⟨H, Hn⟩
      cases H with
      | intro h1 h2 =>
        by_cases hx : leA x0 x'
        · have hy : ¬ leB y y' := fun hy => Hn (.intro hx hy)
          refine IHy y' ⟨h2, hy⟩ x' ?_
          intro x'' Hx'' y''
          exact IH0 x'' ⟨_root_.trans Hx''.1 h1, fun h => Hx''.2 (_root_.trans h1 h)⟩ y''
        · exact IH0 x' ⟨h1, hx⟩ y'

@[rocq_alias trillium.fairis.prod_relation_antisym]
theorem prod_relation_antisym :
    Std.Antisymm leA → Std.Antisymm leB → Std.Antisymm (Prod.RProd leA leB) := by
  intro hA hB
  constructor
  rintro ⟨x1, y1⟩ ⟨x2, y2⟩ H1 H2
  cases H1 with
  | intro h1 h2 =>
    cases H2 with
    | intro h3 h4 => rw [hA.antisymm _ _ h1 h3, hB.antisymm _ _ h2 h4]

@[rocq_alias trillium.fairis.prod_relation_preorder]
theorem prod_relation_preorder :
    IsPreorder A leA → IsPreorder B leB → IsPreorder (A × B) (Prod.RProd leA leB) := by
  intro hA hB
  exact { refl := fun ⟨x, y⟩ => .intro (refl_of leA x) (refl_of leB y)
          trans := (prod_trans leA leB inferInstance inferInstance).trans }

@[rocq_alias trillium.fairis.prod_relation_partialorder]
theorem prod_relation_partialorder :
    IsPartialOrder A leA → IsPartialOrder B leB →
    IsPartialOrder (A × B) (Prod.RProd leA leB) := by
  intro hA hB
  have := prod_relation_preorder leA leB inferInstance inferInstance
  have := prod_relation_antisym leA leB inferInstance inferInstance
  exact {}

end product_of_orders

section unstrict_order

variable {A : Type _} (lt : A → A → Prop)

/-- The reflexive closure of a relation. -/
@[rocq_alias trillium.fairis.unstrict]
def unstrict (x y : A) : Prop := x = y ∨ lt x y

end unstrict_order

/-- The order on the states of the yes/no model: lexicographic on the counter and whose turn it
is. -/
@[rocq_alias trillium.fairis.the_order]
def theOrder : Nat × Bool → Nat × Bool → Prop :=
  unstrict (Prod.Lex (strict (· ≤ · : Nat → Nat → Prop)) (strict (· ≤ · : Bool → Bool → Prop)))

/-- stdpp's `lexico` on `nat * bool` is Mathlib's lexicographic order. -/
@[rocq_alias trillium.fairis.lexprod_lexico]
theorem lexprod_lexico (x y : Nat × Bool) :
    Prod.Lex (strict (· ≤ · : Nat → Nat → Prop)) (strict (· ≤ · : Bool → Bool → Prop)) x y ↔
      toLex x < toLex y := by
  rw [Prod.lex_def, Prod.Lex.toLex_lt_toLex]
  simp only [strict]
  constructor
  · rintro (H | ⟨Heq, H⟩)
    · left; omega
    · right; exact ⟨Heq, lt_of_le_not_ge H.1 H.2⟩
  · rintro (H | ⟨Heq, H⟩)
    · left; omega
    · right; exact ⟨Heq, H.le, not_le.2 H⟩

@[rocq_alias trillium.fairis.yesno_adequacy.the_order_po]
instance the_order_po : IsPartialOrder (Nat × Bool) theOrder where
  refl _ := .inl rfl
  trans x y z H1 H2 := by
    rcases H1 with rfl | H1
    · exact H2
    rcases H2 with rfl | H2
    · exact .inr H1
    rw [lexprod_lexico] at H1 H2
    exact .inr ((lexprod_lexico _ _).2 (lt_trans H1 H2))
  antisymm x y H1 H2 := by
    rcases H1 with rfl | H1
    · rfl
    rcases H2 with rfl | H2
    · rfl
    rw [lexprod_lexico] at H1 H2
    exact absurd (lt_trans H1 H2) (lt_irrefl _)

/-- The role that decreases the state (Rocq `the_decreasing_role`). -/
@[rocq_alias trillium.fairis.the_decreasing_role]
def theDecreasingRole (s : theFairModel) : YN :=
  match (s : Nat × Bool).2, (s : Nat × Bool).1 with
  | false, 0 => Y
  | true, _ => Y
  | false, _ + 1 => No

@[rocq_alias trillium.fairis.eq_antisymm]
theorem eq_antisymm (A : Type _) : ∀ x y : A, x = y → y = x → x = y := fun _ _ h _ => h

@[rocq_alias trillium.fairis.strict_unstrict]
theorem strict_unstrict {A : Type _} (R : A → A → Prop) :
    ∀ x y, strict (unstrict R) x y → R x y := by
  rintro x y ⟨H | H, Hn⟩
  · exact absurd (.inl H.symm) Hn
  · exact H

@[rocq_alias trillium.fairis.wf_bool_le]
theorem wf_bool_le : WellFounded (strict (· ≤ · : Bool → Bool → Prop)) := by
  have Hf : Acc (strict (· ≤ · : Bool → Bool → Prop)) false :=
    .intro false fun b ⟨h1, h2⟩ => by cases b <;> simp_all
  constructor
  intro b
  cases b with
  | false => exact Hf
  | true =>
    constructor
    intro b ⟨h1, h2⟩
    cases b with
    | false => exact Hf
    | true => exact absurd h1 h2

@[rocq_alias trillium.fairis.lex_trans]
theorem lex_trans {A B : Type _} {R1 : A → A → Prop} {R2 : B → B → Prop} [IsTrans A R1]
    [IsTrans B R2] : IsTrans (A × B) (Prod.Lex R1 R2) := by
  constructor
  intro x y z Ha Hb
  cases Ha with
  | left _ _ h1 =>
    cases Hb with
    | left _ _ h2 => exact .left _ _ (_root_.trans h1 h2)
    | right _ _ => exact .left _ _ h1
  | right _ h1 =>
    cases Hb with
    | left _ _ h2 => exact .left _ _ h2
    | right _ h2 => exact .right _ (_root_.trans h1 h2)

theorem theOrder_iff (x y : Nat × Bool) :
    theOrder x y ↔ x = y ∨ x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 = false ∧ y.2 = true) := by
  unfold theOrder unstrict
  rw [Prod.lex_def]
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  cases x2 <;> cases y2 <;> simp [strict] <;> omega

@[rocq_alias trillium.fairis.the_model_terminates]
instance the_model_terminates : FairTerminatingModel theFairModel where
  ftmLeq := theOrder
  ftm_order := the_order_po.toIsPreorder
  ftm_wf := by
    have H : WellFounded (Prod.Lex (strict (· ≤ · : Nat → Nat → Prop))
        (strict (· ≤ · : Bool → Bool → Prop))) := by
      refine (Prod.lex ⟨_, ?_⟩ ⟨_, wf_bool_le⟩).wf
      refine Subrelation.wf (r := (· < ·)) ?_ Nat.lt_wfRel.wf
      intro a b h
      exact lt_of_le_not_ge h.1 h.2
    exact Subrelation.wf (fun {x y} h => strict_unstrict _ x y h) H
  ftmDecreasingRole := theDecreasingRole
  ftm_decr := by
    rintro ⟨N, B⟩ ⟨ρ', s', Hex⟩
    change YnTrans (N, B) ρ' s' at Hex
    cases B with
    | true =>
      have hN : N > 0 := by cases Hex <;> omega
      obtain ⟨N, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
      refine ⟨show Y ∈ ynLiveRoles (N + 1, true) by simp [ynLiveRoles], ?_⟩
      intro s' H
      change YnTrans _ _ _ at H
      simp only [theDecreasingRole] at H
      cases H
      simp [theOrder_iff]
    | false =>
      have hN : N > 0 := by cases Hex <;> omega
      obtain ⟨N, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
      refine ⟨?_, ?_⟩
      · show No ∈ ynLiveRoles (N + 1, false)
        cases N <;> simp [ynLiveRoles]
      · intro s' H
        change YnTrans _ _ _ at H
        simp only [theDecreasingRole] at H
        cases H
        simp [theOrder_iff]
  ftm_decreasing_role_preserved := by
    rintro s s' ρ' Htrans Hnex
    change YnTrans s ρ' s' at Htrans
    cases Htrans with
    | yes_trans n Hn => exact absurd rfl Hnex
    | yes_fail n Hn => rfl
    | no_trans n => exact absurd rfl Hnex
    | no_fail n Hn => rfl
  ftm_notinc := by
    rintro s ρ s' Htrans
    change YnTrans s ρ s' at Htrans
    cases Htrans <;> simp [theOrder_iff]

/-- The candidate successors of a state (the model is finitely branching). -/
@[rocq_alias trillium.fairis.yesno_adequacy.steppable]
def steppable : Nat × Bool → List ((Nat × Bool) × Option YN)
  | (n, w) =>
    [n, n - 1].flatMap fun n' => [w, !w].flatMap fun w' =>
      [some Y, some No].map fun ℓ => ((n', w'), ℓ)

#rocq_ignore trillium.fairis.yesno_adequacy.proof_irrel_trans
  "stdpp `ProofIrrel` instance for the finiteness of a sigma type; Lean's `Prop` is proof-irrelevant (`Finite` of a subtype needs no such instance)"

@[rocq_alias trillium.fairis.yesno_adequacy.model_finitary]
theorem model_finitary (s : theFairModel) :
    Finite {p : theFairModel.fmstate × Option theFairModel.fmrole //
      theFairModel.fmtrans s p.2 p.1} := by
  refine in_list_finite (steppable s) ?_
  rintro ⟨s', ℓ⟩ Htrans
  change YnTrans s ℓ s' at Htrans
  cases Htrans with
  | yes_trans n _ => show (((n, false), some Y) : (Nat × Bool) × Option YN) ∈ steppable _; simp [steppable]
  | yes_fail n _ => show (((n, false), some Y) : (Nat × Bool) × Option YN) ∈ steppable _; simp [steppable]
  | no_trans n => show (((n, true), some No) : (Nat × Bool) × Option YN) ∈ steppable _; simp [steppable]
  | no_fail n _ => show (((n, true), some No) : (Nat × Bool) × Option YN) ∈ steppable _; simp [steppable]

theorem liveRoles_start (N : Nat) (HN : N > 1) :
    theFairModel.liveRoles (N, true) = ({No, Y} : GSet YN) := by
  obtain ⟨N, rfl⟩ : ∃ k, N = k + 2 := ⟨N - 2, by omega⟩
  rfl

theorem toGMap_start (N : Nat) (HN : N > 1) :
    GSet.toGMap (theModel.lmFl (N, true)) (theFairModel.liveRoles (N, true)) =
      (GMap.singleton No 61).insert Y 61 := by
  rw [liveRoles_start N HN, theModel_lmFl]
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  rw [GSet.getElem?_toGMap]
  cases k with
  | Y => simp [GMap.singleton]
  | No => simp [GMap.singleton]; rfl

theorem empty_diff_live (X : GSet YN) : (∅ : GSet YN) \ X = ∅ := by
  apply Std.ExtTreeSet.ext_mem
  intro k
  simp [Iris.Std.LawfulSet.mem_diff]

@[rocq_alias trillium.fairis.yesno_terminates]
theorem yesno_terminates (GF : Iris.BundledGFunctors) [HeapGpreS theModel GF] [YesnoPreG GF]
    (N : Nat) (HN : N > 1) (extr : HeapLangExtrace) (Hvex : ExtraceValid extr)
    (Hexfirst : extr.first.1 = [tl(v(&start) #(.int N))]) :
    (∀ tid, fairEx tid extr) → terminatingTrace extr := by
  intro Hfair
  refine simulation_adequacy_terminate_ftm GF theModel .NotStuck _ ((N, true) : theFairModel.fmstate)
    ∅ extr Hexfirst ?_ ?_ ?_ Hvex Hfair
  · exact valid_state_evolution_finitary_fairness_simple model_finitary _
  · rw [liveRoles_start N HN]
    intro h
    have := congrArg (Y ∈ ·) h
    simp at this
  · intro _
    iintro !> Hm HFR Hf !>
    rw [toGMap_start N HN, empty_diff_live]
    iapply start_spec 0 N 61 (by omega) $$ [Hm Hf HFR] []
    · iframe
      ipureintro
      omega
    · inext
      iintro H
      iexact H

end Trillium.Fairis.Yesno
