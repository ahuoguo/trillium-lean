/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.Traces.Trace
import Iris.Algebra.CMRA
import Iris.Algebra.LocalUpdates

/-!
# The resource algebra of traces
Port of `trillium/algebra/trace.v`.

`TraceAlg A L` is a finite trace or the invalid element `bot`. Composition of two traces is the
longer one if one is a prefix of the other, and `bot` otherwise; the core is the identity. This is
a discrete, total CMRA (built with iris-lean's `CMRA.ofDiscreteTotal`, the counterpart of Rocq's
`ra_total_mixin` + `discreteR`) in which `trace ft ≼ trace ft'` iff `ft` is a prefix of `ft'`.
As in iris-lean, the discrete OFEs are Leibniz, so Rocq `≡` is `=`.
-/

namespace Trillium

open Iris OFE ORA FiniteTrace

/-- Traces with a bottom (invalid) element (Rocq `trace_alg`). -/
@[rocq_alias trillium.trace_alg]
inductive TraceAlg (A L : Type _) where
  /-- A finite trace (Rocq `trace_alg_trace`). -/
  | trace (ft : FiniteTrace A L)
  /-- The invalid element (Rocq `trace_alg_bot`). -/
  | bot

variable {A L : Type _}

/-- The discrete (Leibniz) OFE on finite traces (Rocq `traceO`). -/
@[rocq_alias trillium.traceO]
instance FiniteTrace.instCOFE : COFE (FiniteTrace A L) := COFE.ofDiscrete _

instance FiniteTrace.instDiscrete : OFE.Discrete (FiniteTrace A L) where
  discrete_0 h := h

/-- The discrete (Leibniz) OFE on `TraceAlg` (Rocq `trace_algO`). -/
@[rocq_alias trillium.trace_algO]
instance TraceAlg.instCOFE : COFE (TraceAlg A L) := COFE.ofDiscrete _

instance TraceAlg.instDiscrete : OFE.Discrete (TraceAlg A L) where
  discrete_0 h := h

namespace TraceAlg

variable [DecidableEq A] [DecidableEq L]

/-- Composition of `TraceAlg` elements (Rocq `trace_alg_op`). -/
@[rocq_alias trillium.trace_alg_op]
def op : TraceAlg A L → TraceAlg A L → TraceAlg A L
  | trace ft, trace ft' =>
    if ft.IsPrefix ft' then trace ft' else if ft'.IsPrefix ft then trace ft else bot
  | trace _, bot => bot
  | bot, _ => bot

/-- Validity (Rocq `trace_alg_valid_instance`): everything but `bot` is valid. -/
@[rocq_alias trillium.trace_alg_valid_instance]
def Valid : TraceAlg A L → Prop
  | trace _ => True
  | bot => False

#rocq_ignore trillium.trace_alg_pcore_instance
  "The core is the identity; it is passed as `id` to `CMRA.ofDiscreteTotal` (see `TraceAlg.pcore_eq`)."

@[rocq_alias trillium.trace_alg_op_traces]
theorem op_traces (ft ft' : FiniteTrace A L) :
    (op (trace ft) (trace ft') = bot ∧ ¬ ft.IsPrefix ft' ∧ ¬ ft'.IsPrefix ft) ∨
      (op (trace ft) (trace ft') = trace ft' ∧ ft.IsPrefix ft') ∨
      (op (trace ft) (trace ft') = trace ft ∧ ft'.IsPrefix ft) := by
  simp only [op]
  by_cases h1 : ft.IsPrefix ft' <;> by_cases h2 : ft'.IsPrefix ft <;> simp [h1, h2]

@[rocq_alias trillium.trace_alg_op_eq_right']
theorem op_eq_right' {ft ft' : FiniteTrace A L} (h : ft.IsPrefix ft') :
    op (trace ft) (trace ft') = trace ft' := by
  simp [op, h]

@[rocq_alias trillium.trace_alg_op_eq_left']
theorem op_eq_left' {ft ft' : FiniteTrace A L} (h : ft'.IsPrefix ft) :
    op (trace ft) (trace ft') = trace ft := by
  simp only [op, h, ↓reduceIte]
  split
  · next h' => rw [IsPrefix.antisymm h' h]
  · rfl

@[rocq_alias trillium.trace_alg_op_eq_neither']
theorem op_eq_neither' {ft ft' : FiniteTrace A L} (h1 : ¬ ft.IsPrefix ft')
    (h2 : ¬ ft'.IsPrefix ft) : op (trace ft) (trace ft') = bot := by
  simp [op, h1, h2]

@[rocq_alias trillium.trace_alg_op_right_bot']
theorem op_right_bot' (fa : TraceAlg A L) : op fa bot = bot := by
  cases fa <;> rfl

@[rocq_alias trillium.trace_alg_op_left_bot']
theorem op_left_bot' (fa : TraceAlg A L) : op bot fa = bot := rfl

@[rocq_alias trillium.trace_alg_op_com]
theorem op_comm (fa fa' : TraceAlg A L) : op fa fa' = op fa' fa := by
  rcases fa with ft | _ <;> rcases fa' with ft' | _ <;> try rfl
  by_cases h1 : ft.IsPrefix ft'
  · rw [op_eq_right' h1, op_eq_left' h1]
  by_cases h2 : ft'.IsPrefix ft
  · rw [op_eq_left' h2, op_eq_right' h2]
  rw [op_eq_neither' h1 h2, op_eq_neither' h2 h1]

theorem op_assoc_traces (ft ft' ft'' : FiniteTrace A L) :
    op (trace ft) (op (trace ft') (trace ft'')) = op (op (trace ft) (trace ft')) (trace ft'') := by
  rcases op_traces ft ft' with ⟨hf, hf1, hf2⟩ | ⟨hf, hf'⟩ | ⟨hf, hf'⟩ <;> rw [hf]
  · rcases op_traces ft' ft'' with ⟨hg, hg1, hg2⟩ | ⟨hg, hg'⟩ | ⟨hg, hg'⟩ <;> rw [hg]
    · rfl
    · by_cases h : ft.IsPrefix ft''
      · rcases isPrefix_total_of_isPrefix h hg' with h' | h' <;> contradiction
      · exact op_eq_neither' h fun h' => hf2 (hg'.trans h')
    · exact op_eq_neither' hf1 hf2
  · rcases op_traces ft' ft'' with ⟨hg, hg1, hg2⟩ | ⟨hg, hg'⟩ | ⟨hg, hg'⟩ <;> rw [hg]
    · rfl
    · exact op_eq_right' (hf'.trans hg')
    · exact op_eq_right' hf'
  · rcases op_traces ft' ft'' with ⟨hg, hg1, hg2⟩ | ⟨hg, hg'⟩ | ⟨hg, hg'⟩ <;> rw [hg]
    · have n1 : ¬ ft.IsPrefix ft'' := fun h => hg1 (hf'.trans h)
      have n2 : ¬ ft''.IsPrefix ft := fun h => by
        rcases isPrefix_total_of_isPrefix h hf' with h' | h' <;> contradiction
      rw [op_eq_neither' n1 n2]; rfl
    · rw [op_eq_left' (hg'.trans hf'), op_eq_left' hf']

@[rocq_alias trillium.trace_alg_op_assoc]
theorem op_assoc (fa fa' fa'' : TraceAlg A L) : op fa (op fa' fa'') = op (op fa fa') fa'' := by
  rcases fa with ft | _
  · rcases fa' with ft' | _
    · rcases fa'' with ft'' | _
      · exact op_assoc_traces ft ft' ft''
      · simp [op_right_bot']
    · simp [op_right_bot', op_left_bot']
  · rfl

@[rocq_alias trillium.trace_alg_op_idemp']
theorem op_idem (fa : TraceAlg A L) : op fa fa = fa := by
  cases fa with
  | trace ft => exact op_eq_left' (.refl ft)
  | bot => rfl

/-- The CMRA of traces (Rocq `trace_alg_RAMixin` and `trace_algR := discreteR …`). -/
@[rocq_alias trillium.trace_alg_RAMixin, rocq_alias trillium.trace_algR]
instance instCMRA : CMRA (TraceAlg A L) :=
  CMRA.ofDiscreteTotal id op Valid op_assoc op_comm op_idem (fun _ => rfl)
    (fun x y h => by cases x <;> cases y <;> trivial)
    (fun x y => ⟨y, rfl⟩)

theorem op_eq (fa fa' : TraceAlg A L) : fa • fa' = op fa fa' := rfl

theorem pcore_eq (fa : TraceAlg A L) : pcore fa = some fa := rfl

@[rocq_alias trillium.trace_alg_cmra_total]
instance instIsTotal : IsTotal (TraceAlg A L) where
  total x := ⟨x, rfl⟩

@[rocq_alias trillium.trace_alg_cmra_discrete]
instance instCMRADiscrete : ORA.Discrete (TraceAlg A L) where
  discrete_0 h := h
  discrete_valid := id

@[rocq_alias trillium.trace_alg_core_id]
instance instCoreId (fa : TraceAlg A L) : CoreId fa := ⟨rfl⟩

@[rocq_alias trillium.trace_alg_included]
theorem trace_included {ft ft' : FiniteTrace A L} :
    trace ft ≼ trace ft' ↔ ft.IsPrefix ft' := by
  constructor
  · rintro ⟨fa'', heq⟩
    rcases fa'' with ft'' | _
    · rw [op_eq] at heq
      rcases op_traces ft ft'' with ⟨hop, -⟩ | ⟨hop, hf⟩ | ⟨hop, -⟩ <;> rw [hop] at heq
      · cases heq
      · cases heq; exact hf
      · cases heq; exact .refl _
    · rw [op_eq, op_right_bot'] at heq; cases heq
  · intro h
    exact ⟨trace ft', (op_eq_right' h).symm⟩

@[rocq_alias trillium.trace_alg_includedN]
theorem trace_includedN {ft ft' : FiniteTrace A L} (n : Nat) :
    trace ft ≼{n} trace ft' ↔ ft.IsPrefix ft' := trace_included

@[rocq_alias trillium.trace_alg_op_idemp'']
instance instIdempotentOp : Std.IdempotentOp (α := TraceAlg A L) (· • ·) where
  idempotent := op_idem

@[rocq_alias trillium.trace_alg_op_idemp]
theorem op_self (fa : TraceAlg A L) : fa • fa = fa := op_idem fa

@[rocq_alias trillium.trace_alg_op_eq_right]
theorem op_eq_right {ft ft' : FiniteTrace A L} (h : ft.IsPrefix ft') :
    trace ft • trace ft' = trace ft' := op_eq_right' h

@[rocq_alias trillium.trace_alg_op_eq_left]
theorem op_eq_left {ft ft' : FiniteTrace A L} (h : ft'.IsPrefix ft) :
    trace ft • trace ft' = trace ft := op_eq_left' h

@[rocq_alias trillium.trace_alg_op_eq_neither]
theorem op_eq_neither {ft ft' : FiniteTrace A L} (h1 : ¬ ft.IsPrefix ft')
    (h2 : ¬ ft'.IsPrefix ft) : trace ft • trace ft' = bot := op_eq_neither' h1 h2

@[rocq_alias trillium.trace_alg_op_right_bot, simp]
theorem op_right_bot (fa : TraceAlg A L) : fa • bot = bot := op_right_bot' fa

@[rocq_alias trillium.trace_alg_op_left_bot, simp]
theorem op_left_bot (fa : TraceAlg A L) : bot • fa = bot := op_left_bot' fa

@[rocq_alias trillium.trace_alg_validN]
theorem exists_of_validN {fa : TraceAlg A L} {n : Nat} : ✓{n} fa → ∃ ft, fa = trace ft := by
  cases fa with
  | trace ft => exact fun _ => ⟨ft, rfl⟩
  | bot => exact False.elim

@[rocq_alias trillium.trace_alg_valid]
theorem exists_of_valid {fa : TraceAlg A L} : ✓ fa → ∃ ft, fa = trace ft := by
  cases fa with
  | trace ft => exact fun _ => ⟨ft, rfl⟩
  | bot => exact False.elim

@[rocq_alias trillium.trace_alg_pcore]
theorem pcore_eq_some (fa : TraceAlg A L) : pcore fa = some fa := rfl

@[rocq_alias trillium.trace_alg_core]
theorem core_eq (fa : TraceAlg A L) : PCore.core fa = fa := rfl

@[rocq_alias trillium.trace_alg_local_update]
theorem local_update {ft ft' : FiniteTrace A L} (fa : TraceAlg A L) (Hpf : ft.IsPrefix ft') :
    (trace ft, fa) ~l~> (trace ft', trace ft') := by
  refine LocalUpdate.total_valid (α := TraceAlg A L) fun _ hv hfts => ?_
  obtain ⟨ft'', rfl⟩ := exists_of_valid hv
  have hfts := trace_included.mp hfts
  have e1 : trace ft' • trace ft = trace ft' := op_eq_left Hpf
  have e2 : trace ft' • trace ft'' = trace ft' := op_eq_left (hfts.trans Hpf)
  have := LocalUpdate.op (x := trace ft) (y := trace ft'') (z := trace ft') fun _ _ => by
    rw [e1]; trivial
  rwa [e1, e2] at this

end TraceAlg

end Trillium
