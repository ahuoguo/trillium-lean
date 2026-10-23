/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.Fairness.NatOmega
import Trillium.Fairness.Inftraces
import Trillium.Fairness.UtilsLogic

/-!
# Length of traces
Port of `fairness/trace_len.v`.

`trace_len_is tr len` (`traceLenIs tr len`) says that the trace `tr` has `len ∈ ℕ ∪ {∞}`
states: `after i tr` is defined exactly for `i < len`.
-/

namespace Trillium.Fairness

open Trace NatOmega

section TraceLen

variable {St L : Type _}

@[rocq_alias trillium.fairness.NOmega_lt_le]
instance NOmega_lt_le : ∀ x y : NatOmega, Decidable (NatOmega.lt x y)
  | .infinity, _ => inferInstanceAs (Decidable False)
  | .num n, .num m => inferInstanceAs (Decidable (n < m))
  | .num _, .infinity => inferInstanceAs (Decidable True)

/-- The trace `tr` has length `len`. -/
@[rocq_alias trillium.fairness.trace_len_is]
def traceLenIs (tr : Trace St L) (len : NatOmega) : Prop :=
  ∀ i : Nat, (after i tr).isSome ↔ ltNatL i len

@[rocq_alias trillium.fairness.trace_has_len]
theorem trace_has_len (tr : Trace St L) : ∃ len, traceLenIs tr len := by
  rcases infinite_or_finite tr with INF | FIN_
  · exact ⟨.infinity, fun i => ⟨fun _ => trivial, fun _ => INF i⟩⟩
  classical
  obtain ⟨n0, Hn0⟩ := FIN_
  obtain ⟨n, SIZE, MIN⟩ := min_prop_dec (fun n => after n tr = none) n0 Hn0
  refine ⟨.num n, fun i => ⟨fun SOME => ?_, fun LT => ?_⟩⟩
  · simp only [ltNatL]
    by_contra LE
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt LE)
    rw [after_sum' d n tr, show after n tr = none from SIZE] at SOME
    simp at SOME
  · simp only [ltNatL] at LT
    cases h : after i tr with
    | some _ => rfl
    | none => exact absurd (MIN (show after i tr = none from h)) (Nat.not_le_of_lt LT)

@[rocq_alias trillium.fairness.trace_len_cons]
theorem trace_len_cons (s : St) (l : L) (tr : Trace St L) (len : NatOmega)
    (LEN : traceLenIs tr len) : traceLenIs (cons s l tr) (NatOmega.succ len) := by
  intro i
  cases i with
  | zero => cases len <;> simp [ltNatL, NatOmega.succ]
  | succ i =>
    rw [after_succ_cons, LEN i]
    cases len <;> simp [ltNatL, NatOmega.succ]

@[rocq_alias trillium.fairness.trace_len_uniq]
theorem trace_len_uniq (tr : Trace St L) (len1 len2 : NatOmega)
    (LEN1 : traceLenIs tr len1) (LEN2 : traceLenIs tr len2) : len1 = len2 := by
  rcases NatOmega.lt_trichotomy len1 len2 with h | h | h
  · cases len1 with
    | infinity => exact h.elim
    | num n =>
      have L2 := (LEN2 n).2 (by cases len2 <;> simp_all [NatOmega.lt, ltNatL])
      have := (LEN1 n).1 L2
      simp [ltNatL] at this
  · exact h
  · cases len2 with
    | infinity => exact h.elim
    | num n =>
      have L1 := (LEN1 n).2 (by cases len1 <;> simp_all [NatOmega.lt, ltNatL])
      have := (LEN2 n).1 L1
      simp [ltNatL] at this

@[rocq_alias trillium.fairness.trace_len_tail]
theorem trace_len_tail (s : St) (l : L) (tr : Trace St L) (len : NatOmega)
    (LEN : traceLenIs (cons s l tr) len) : traceLenIs tr (NatOmega.pred len) := by
  obtain ⟨len', LEN'⟩ := trace_has_len tr
  have H := trace_len_cons s l _ _ LEN'
  obtain rfl := trace_len_uniq _ _ _ LEN H
  rwa [NatOmega.pred_succ]

@[rocq_alias trillium.fairness.trace_len_singleton]
theorem trace_len_singleton (s : St) : traceLenIs (singl s : Trace St L) (.num 1) := by
  intro i
  cases i with
  | zero => simp [ltNatL]
  | succ i => simp [ltNatL]

@[rocq_alias trillium.fairness.trace_len_after]
theorem trace_len_after (tr tr' : Trace St L) (i : Nat) (len : NatOmega)
    (LEN : traceLenIs tr len) (AFTER : after i tr = some tr') :
    traceLenIs tr' (NatOmega.sub len (.num i)) := by
  induction i generalizing tr tr' len with
  | zero =>
    simp only [after_0_id, Option.some.injEq] at AFTER
    subst AFTER
    have : NatOmega.sub len (.num 0) = len := NatOmega.sub_0_r len
    rwa [this]
  | succ i IHi =>
    cases tr with
    | singl s => simp at AFTER
    | cons s ℓ r =>
      rw [after_succ_cons] at AFTER
      have H := trace_len_tail _ _ _ _ LEN
      have := IHi _ _ _ H AFTER
      cases len with
      | infinity => exact this
      | num n =>
        simp only [NatOmega.pred, NatOmega.sub] at this ⊢
        rwa [show n - (i + 1) = Nat.pred n - i by rw [Nat.pred_eq_sub_one]; omega]

@[rocq_alias trillium.fairness.trace_len_0_inv]
theorem trace_len_0_inv (tr : Trace St L) (LEN1 : traceLenIs tr (.num 0)) : False := by
  have := (LEN1 0).1 (by simp)
  simp [ltNatL] at this

@[rocq_alias trillium.fairness.trace_len_gt_0]
theorem trace_len_gt_0 (tr : Trace St L) : ∀ len, traceLenIs tr len → ltNatL 0 len := by
  intro len H
  cases len with
  | infinity => trivial
  | num n =>
    cases n with
    | zero => exact (trace_len_0_inv tr H).elim
    | succ n => simp [ltNatL]

@[rocq_alias trillium.fairness.trace_len_1_inv]
theorem trace_len_1_inv (tr : Trace St L) (LEN1 : traceLenIs tr (.num 1)) :
    ∃ s, tr = singl s := by
  cases tr with
  | singl s => exact ⟨s, rfl⟩
  | cons s ℓ r =>
    have := (LEN1 1).1 (by simp)
    simp [ltNatL] at this

@[rocq_alias trillium.fairness.trace_len_neg]
theorem trace_len_neg (tr : Trace St L) (len : NatOmega) (LEN : traceLenIs tr len) :
    ∀ i : Nat, after i tr = none ↔ NatOmega.le len (.num i) := by
  intro i
  have H := LEN i
  rw [NatOmega.le_iff_not_lt_nat, ← H, Option.not_isSome_iff_eq_none]

@[rocq_alias trillium.fairness.terminating_trace_equiv]
theorem terminating_trace_equiv (tr : Trace St L) (len : NatOmega) (LEN : traceLenIs tr len) :
    terminatingTrace tr ↔ ∃ n, len = .num n := by
  constructor
  · rintro ⟨i, N⟩
    have := (trace_len_neg tr len LEN i).1 N
    cases len with
    | infinity => exact this.elim
    | num n => exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, (trace_len_neg tr _ LEN n).2 (by simp [NatOmega.le])⟩

@[rocq_alias trillium.fairness.infinite_trace_equiv]
theorem infinite_trace_equiv (tr : Trace St L) (len : NatOmega) (LEN : traceLenIs tr len) :
    infiniteTrace tr ↔ len = .infinity := by
  constructor
  · intro A
    cases len with
    | infinity => rfl
    | num n =>
      have := (trace_len_neg tr _ LEN n).2 (by simp [NatOmega.le])
      have := A n
      simp_all
  · rintro rfl i
    exact (LEN i).2 trivial

end TraceLen

section TracesMatch

@[rocq_alias trillium.fairness.traces_match_same_length_impl]
theorem traces_match_same_length_impl {L1 L2 S1 S2 : Type _}
    (R1 : L1 → L2 → Prop) (R2 : S1 → S2 → Prop) (step1 : S1 → L1 → S1 → Prop)
    (step2 : S2 → L2 → S2 → Prop) (tr1 : Trace S1 L1) (tr2 : Trace S2 L2) (len1 len2 : NatOmega)
    (LEN1 : traceLenIs tr1 len1) (LEN2 : traceLenIs tr2 len2)
    (MATCH : TracesMatch R1 R2 step1 step2 tr1 tr2) (LT : NatOmega.lt len1 len2) : False := by
  cases len1 with
  | infinity => exact LT.elim
  | num n =>
    have LL2 := (LEN2 n).2 (by cases len2 <;> simp_all [NatOmega.lt, ltNatL])
    obtain ⟨atr2, AFTER2⟩ := Option.isSome_iff_exists.1 LL2
    obtain ⟨atr1, AFTER1, _⟩ := traces_match_after tr1 tr2 n atr2 MATCH AFTER2
    have := (LEN1 n).1 (by simp [AFTER1])
    simp [ltNatL] at this

@[rocq_alias trillium.fairness.traces_match_same_length]
theorem traces_match_same_length {L1 L2 S1 S2 : Type _}
    (R1 : L1 → L2 → Prop) (R2 : S1 → S2 → Prop) (step1 : S1 → L1 → S1 → Prop)
    (step2 : S2 → L2 → S2 → Prop) (tr1 : Trace S1 L1) (tr2 : Trace S2 L2) (len1 len2 : NatOmega)
    (LEN1 : traceLenIs tr1 len1) (LEN2 : traceLenIs tr2 len2)
    (MATCH : TracesMatch R1 R2 step1 step2 tr1 tr2) : len1 = len2 := by
  rcases NatOmega.lt_trichotomy len1 len2 with h | h | h
  · exact (traces_match_same_length_impl R1 R2 step1 step2 tr1 tr2 len1 len2 LEN1 LEN2 MATCH h).elim
  · exact h
  · rw [traces_match_flip] at MATCH
    exact (traces_match_same_length_impl _ _ _ _ tr2 tr1 len2 len1 LEN2 LEN1 MATCH h).elim

end TracesMatch

end Trillium.Fairness
