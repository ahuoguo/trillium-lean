/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.Fairness.Fairness

/-!
# Fair termination of models
Port of `fairis/fair_termination.v`.

A `FairTerminatingModel` is a fair model equipped with a well-founded preorder on its states,
such that every step does not increase the state, and, in every non-final state, a designated
live role (`ftmDecreasingRole`) strictly decreases the state when it steps and stays the
designated role as long as other roles step. The main theorem
`fair_terminating_traces_terminate` shows that every valid fair trace of such a model is finite.

Representation: stdpp's `PreOrder ftm_leq` is Mathlib's `IsPreorder`; stdpp's
`strict R x y := R x y ∧ ¬ R y x` is `FairTerminatingModel.ftmLt` (Rocq notation `ftm_lt`);
`well_founded` is `WellFounded`.
-/

namespace Trillium.Fairis

open Trillium Trillium.Fairness Trillium.Fairness.Trace

/-- A model trace is fairly terminating if it terminates whenever it is valid and fair for
every role. -/
@[rocq_alias trillium.fairis.mtrace_fairly_terminating]
def MtraceFairlyTerminating {Mdl : FairModel} (mtr : Mtrace Mdl) : Prop :=
  MtraceValid mtr → (∀ ρ, fairModelTrace ρ mtr) → terminatingTrace mtr

/-- A fair model whose fair traces terminate because of a well-founded preorder on states that
is decreased by a designated live role. -/
@[rocq_alias trillium.fairis.FairTerminatingModel]
class FairTerminatingModel (Mdl : FairModel) where
  /-- The preorder on states (Rocq `ftm_leq`). -/
  ftmLeq : Mdl → Mdl → Prop
  ftm_order : IsPreorder Mdl ftmLeq
  /-- The strict order `strict ftmLeq` is well-founded. -/
  ftm_wf : WellFounded (fun a b => ftmLeq a b ∧ ¬ ftmLeq b a)
  /-- The role responsible for decreasing the state (Rocq `ftm_decreasing_role`). -/
  ftmDecreasingRole : Mdl → Mdl.fmrole
  ftm_decr : ∀ s : Mdl, (∃ ρ' s', Mdl.fmtrans s ρ' s') →
    ftmDecreasingRole s ∈ Mdl.liveRoles s ∧
      ∀ s', Mdl.fmtrans s (some (ftmDecreasingRole s)) s' → ftmLeq s' s ∧ ¬ ftmLeq s s'
  ftm_decreasing_role_preserved : ∀ (s s' : Mdl) ρ',
    Mdl.fmtrans s ρ' s' → ρ' ≠ some (ftmDecreasingRole s) →
      ftmDecreasingRole s = ftmDecreasingRole s'
  ftm_notinc : ∀ (s : Mdl) ρ s', Mdl.fmtrans s ρ s' → ftmLeq s' s

attribute [instance] FairTerminatingModel.ftm_order

namespace FairTerminatingModel

variable {Mdl : FairModel} [FairTerminatingModel Mdl]

/-- The strict order associated with `ftmLeq` (Rocq notation `ftm_lt := strict ftm_leq`). -/
abbrev ftmLt (a b : Mdl) : Prop := ftmLeq a b ∧ ¬ ftmLeq b a

theorem ftmLeq_refl (a : Mdl) : ftmLeq a a := refl_of ftmLeq a

theorem ftmLeq_trans {a b c : Mdl} : ftmLeq a b → ftmLeq b c → ftmLeq a c := trans_of ftmLeq

@[rocq_alias trillium.fairis.ftm_trans']
theorem ftm_trans' {a b c : Mdl} : ftmLt a b → ftmLeq b c → ftmLt a c := by
  rintro ⟨H1, H1'⟩ H2
  exact ⟨ftmLeq_trans H1 H2, fun H' => H1' (ftmLeq_trans H2 H')⟩

end FairTerminatingModel

open FairTerminatingModel

variable {Mdl : FairModel} [FairTerminatingModel Mdl]

/-- The inner induction of `fair_terminating_traces_terminate_rec`: induction on the number of
steps until the decreasing role of the first state is scheduled. -/
private theorem fair_terminating_traces_terminate_rec_aux (s0 : Mdl)
    (IH : ∀ y, ftmLt y s0 → ∀ mtr : Mtrace Mdl, ftmLeq mtr.first y → MtraceValid mtr →
      (∀ ρ, fairModelTrace ρ mtr) → terminatingTrace mtr) :
    ∀ (n : Nat) (s : Mdl) (ℓ : Option Mdl.fmrole) (r : Mtrace Mdl),
      MtraceValid (cons s ℓ r) → ftmLeq s s0 → (∀ ρ, fairModelTrace ρ (cons s ℓ r)) →
      ftmDecreasingRole s ∈ Mdl.liveRoles s →
      predAt (cons s ℓ r) n (fairnessSat roleEnabledModel roleMatch (ftmDecreasingRole s)) →
      (∀ s', Mdl.fmtrans s (some (ftmDecreasingRole s)) s' → ftmLt s' s) →
      terminatingTrace (cons s ℓ r) := by
  -- The case where the decreasing role steps: apply the outer induction hypothesis.
  have Hdec : ∀ (s : Mdl) (r : Mtrace Mdl), MtraceValid (cons s (some (ftmDecreasingRole s)) r) →
      ftmLeq s s0 → (∀ ρ, fairModelTrace ρ (cons s (some (ftmDecreasingRole s)) r)) →
      (∀ s', Mdl.fmtrans s (some (ftmDecreasingRole s)) s' → ftmLt s' s) →
      terminatingTrace (cons s (some (ftmDecreasingRole s)) r) := by
    intro s r Hval Hleq Hfair Htrdec
    have ⟨Hval', Htrans⟩ := trace_valid_cons_inv _ _ _ Hval
    apply terminating_trace_cons
    exact IH r.first (ftm_trans' (Htrdec _ Htrans) Hleq) r (ftmLeq_refl _) Hval'
      (fair_by_cons_forall _ _ _ _ _ Hfair)
  intro n
  induction n with
  | zero =>
    intro s ℓ r Hval Hleq Hfair Hlive Hev Htrdec
    rw [pred_at_0] at Hev
    rcases Hev with Hev | ⟨_, Heq, EQ⟩
    · exact absurd Hlive Hev
    · cases Heq; cases EQ
      exact Hdec s r Hval Hleq Hfair Htrdec
  | succ n IHn =>
    intro s ℓ r Hval Hleq Hfair Hlive Hev Htrdec
    rw [pred_at_S] at Hev
    have ⟨Hval', Htrans⟩ := trace_valid_cons_inv _ _ _ Hval
    by_cases Hnoteq : ℓ = some (ftmDecreasingRole s)
    · subst Hnoteq
      exact Hdec s r Hval Hleq Hfair Htrdec
    · cases r using Trace.casesOn' with
      | singl s' => exact ⟨2, by simp⟩
      | cons s' ℓ' r'' =>
        have ⟨Hlive', Htrdec'⟩ :=
          ftm_decr s' ⟨ℓ', r''.first, (trace_valid_cons_inv _ _ _ Hval').2⟩
        have Hpres := ftm_decreasing_role_preserved s s' ℓ Htrans Hnoteq
        apply terminating_trace_cons
        refine IHn s' ℓ' r'' Hval' (ftmLeq_trans (ftm_notinc s ℓ s' Htrans) Hleq)
          (fair_by_cons_forall _ _ _ _ _ Hfair) Hlive' ?_ Htrdec'
        rw [← Hpres]
        exact Hev

@[rocq_alias trillium.fairis.fair_terminating_traces_terminate_rec]
theorem fair_terminating_traces_terminate_rec (s0 : Mdl) (mtr : Mtrace Mdl) :
    ftmLeq mtr.first s0 → MtraceValid mtr → (∀ ρ, fairModelTrace ρ mtr) →
      terminatingTrace mtr := by
  refine (ftm_wf (Mdl := Mdl)).induction s0
    (C := fun s0 => ∀ mtr : Mtrace Mdl, ftmLeq mtr.first s0 → MtraceValid mtr →
      (∀ ρ, fairModelTrace ρ mtr) → terminatingTrace mtr) ?_ mtr
  intro s0 IH mtr Hleq Hval Hfair
  cases mtr using Trace.casesOn' with
  | singl s => exact ⟨1, by simp⟩
  | cons s ℓ r =>
    have ⟨Hlive, Htrdec⟩ := ftm_decr s ⟨ℓ, r.first, (trace_valid_cons_inv _ _ _ Hval).2⟩
    obtain ⟨n, Hev⟩ := Hfair (ftmDecreasingRole s) 0 (by
      rw [pred_at_0]; exact Hlive)
    rw [Nat.zero_add] at Hev
    exact fair_terminating_traces_terminate_rec_aux s0 IH n s ℓ r Hval Hleq Hfair Hlive Hev Htrdec

@[rocq_alias trillium.fairis.fair_terminating_traces_terminate]
theorem fair_terminating_traces_terminate (mtr : Mtrace Mdl) : MtraceFairlyTerminating mtr :=
  fun Hval Hfair => fair_terminating_traces_terminate_rec mtr.first mtr (ftmLeq_refl _) Hval Hfair

end Trillium.Fairis
