/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.Traces.InfiniteTrace
import Trillium.Traces.Trace
import Mathlib.Data.Fintype.Card

/-!
# Temporal properties of traces
Port of `trillium/traces/trace_properties.v`.

A trace property `ψ : FiniteTrace A L → Stream'.Seq (L × A) → Prop` looks at the finite past
`f` and the (possibly infinite) future `inftr` of an execution. `Eventually ψ` (inductive) holds
if `ψ` holds after finitely many steps; `Always ψ` (coinductive, Lean's `coinductive` command)
holds if `ψ` holds after every number of steps. `Eventually2`/`Always2` (and `…3`) are the
versions for two (three) traces that are advanced in lockstep and must have the same length.

Coinductive proofs (Rocq `cofix`) are done with the generated `Always.coinduct` principle:
`Always.coinduct ψ P step f inftr hP`, where `step` shows that the invariant `P` implies `ψ` and
is preserved by every step. Most derived lemmas are proved through the characterisations
`always_take_drop` / `eventually_take_drop` (and the `2`/`3` variants), as in Rocq.

The Rocq `Finite B`/`EqDecision B` assumptions of the `…_forall_combine` lemmas become
`[Finite B]`, and `Inhabited` becomes `Nonempty`.
-/

namespace Trillium

open Stream' FiniteTrace InfList

/-! ## Single traces -/

/-- `ψ` eventually holds (Rocq `eventually`). -/
@[rocq_alias trillium.eventually]
inductive Eventually {A L : Type _} (ψ : FiniteTrace A L → Seq (L × A) → Prop) :
    FiniteTrace A L → Seq (L × A) → Prop
  | now f inftr : ψ f inftr → Eventually ψ f inftr
  | later f ℓ a inftr : Eventually ψ (f :tr[ℓ]: a) inftr → Eventually ψ f (.cons (ℓ, a) inftr)

/-- `ψ` always holds (Rocq `always`). -/
@[rocq_alias trillium.always]
coinductive Always {A L : Type _} (ψ : FiniteTrace A L → Seq (L × A) → Prop) :
    FiniteTrace A L → Seq (L × A) → Prop where
  | continued f inftr :
    ψ f inftr →
    (∀ ℓ a inftr', inftr = .cons (ℓ, a) inftr' → Always ψ (f :tr[ℓ]: a) inftr') →
    Always ψ f inftr

section single

variable {A L : Type _}

/-- Destructor of `Always` (one unfolding step). -/
theorem Always.dest {ψ : FiniteTrace A L → Seq (L × A) → Prop} {f : FiniteTrace A L}
    {inftr : Seq (L × A)} (h : Always ψ f inftr) :
    ψ f inftr ∧ ∀ ℓ a inftr', inftr = .cons (ℓ, a) inftr' → Always ψ (f :tr[ℓ]: a) inftr' := by
  cases h with
  | continued _ _ h1 h2 => exact ⟨h1, h2⟩

/-! ### `Always` is a comonad -/

@[rocq_alias trillium.always_mono]
theorem Always.mono {ψ ψ' : FiniteTrace A L → Seq (L × A) → Prop} {f : FiniteTrace A L}
    {inftr : Seq (L × A)} (Hψs : ∀ f' inftr', ψ f' inftr' → ψ' f' inftr') :
    Always ψ f inftr → Always ψ' f inftr := by
  refine Always.coinduct ψ' (Always ψ) ?_ f inftr
  intro f inftr h
  obtain ⟨h1, h2⟩ := h.dest
  exact ⟨Hψs _ _ h1, h2⟩

@[rocq_alias trillium.always_holds]
theorem Always.holds {ψ : FiniteTrace A L → Seq (L × A) → Prop} {f : FiniteTrace A L}
    {inftr : Seq (L × A)} : Always ψ f inftr → ψ f inftr := by
  exact fun h => h.dest.1

@[rocq_alias trillium.always_idemp]
theorem Always.idemp {ψ : FiniteTrace A L → Seq (L × A) → Prop} {f : FiniteTrace A L}
    {inftr : Seq (L × A)} : Always ψ f inftr → Always (Always ψ) f inftr := by
  refine Always.coinduct (Always ψ) (Always ψ) ?_ f inftr
  intro f inftr h
  exact ⟨h, h.dest.2⟩

@[rocq_alias trillium.always_unroll]
theorem Always.unroll {ψ : FiniteTrace A L → Seq (L × A) → Prop} {f : FiniteTrace A L} {ℓ : L}
    {a : A} {inftr : Seq (L × A)} :
    Always ψ f (.cons (ℓ, a) inftr) → Always ψ (f :tr[ℓ]: a) inftr := by
  exact fun h => h.dest.2 _ _ _ rfl

@[rocq_alias trillium.always_unroll_n]
theorem Always.unroll_n {ψ : FiniteTrace A L → Seq (L × A) → Prop} (n : Nat)
    {f : FiniteTrace A L} {inftr : Seq (L × A)} :
    Always ψ f inftr → Always ψ (f +trl+ inftr.take n) (inftr.drop n) := by
  induction n generalizing f inftr with
  | zero => simp
  | succ n IH =>
    intro h
    cases inftr with
    | nil => simpa using h
    | cons p inftr =>
      obtain ⟨ℓ, a⟩ := p
      simpa using IH h.unroll

@[rocq_alias trillium.always_take_drop]
theorem always_take_drop {ψ : FiniteTrace A L → Seq (L × A) → Prop} {f : FiniteTrace A L}
    {inftr : Seq (L × A)} :
    Always ψ f inftr ↔ ∀ n, ψ (f +trl+ inftr.take n) (inftr.drop n) := by
  constructor
  · exact fun h n => (h.unroll_n n).holds
  · refine Always.coinduct ψ (fun f inftr => ∀ n, ψ (f +trl+ inftr.take n) (inftr.drop n)) ?_ f
      inftr
    intro f inftr Hn
    refine ⟨by simpa using Hn 0, ?_⟩
    rintro ℓ a inftr' rfl n
    simpa using Hn (n + 1)

@[rocq_alias trillium.always_and]
theorem always_and {ψ1 ψ2 : FiniteTrace A L → Seq (L × A) → Prop} {f : FiniteTrace A L}
    {inftr : Seq (L × A)} :
    Always ψ1 f inftr ∧ Always ψ2 f inftr ↔
      Always (fun f' inftr' => ψ1 f' inftr' ∧ ψ2 f' inftr') f inftr := by
  simp only [always_take_drop, ← forall_and]

@[rocq_alias trillium.always_forall]
theorem always_forall {B : Sort _} {Ψ : B → FiniteTrace A L → Seq (L × A) → Prop}
    {f : FiniteTrace A L} {inftr : Seq (L × A)} :
    (∀ b, Always (Ψ b) f inftr) ↔ Always (fun f' inftr' => ∀ b, Ψ b f' inftr') f inftr := by
  simp only [always_take_drop]
  exact forall_comm

@[rocq_alias trillium.always_impl]
theorem always_impl {P : Prop} {Ψ : FiniteTrace A L → Seq (L × A) → Prop} {f : FiniteTrace A L}
    {inftr : Seq (L × A)} :
    (P → Always Ψ f inftr) ↔ Always (fun f' inftr' => P → Ψ f' inftr') f inftr := by
  simp only [always_take_drop]
  exact forall_comm

/-! ### `Eventually` is a monad -/

@[rocq_alias trillium.eventually_mono]
theorem Eventually.mono {ψ ψ' : FiniteTrace A L → Seq (L × A) → Prop} {f : FiniteTrace A L}
    {inftr : Seq (L × A)} (Hψs : ∀ f' inftr', ψ f' inftr' → ψ' f' inftr') :
    Eventually ψ f inftr → Eventually ψ' f inftr := by
  intro h
  induction h with
  | now f inftr h => exact .now _ _ (Hψs _ _ h)
  | later f ℓ a inftr _ IH => exact .later _ _ _ _ IH

@[rocq_alias trillium.holds_eventually]
theorem Eventually.of_holds {ψ : FiniteTrace A L → Seq (L × A) → Prop} {f : FiniteTrace A L}
    {inftr : Seq (L × A)} : ψ f inftr → Eventually ψ f inftr := .now _ _

@[rocq_alias trillium.eventually_idemp]
theorem Eventually.idemp {ψ : FiniteTrace A L → Seq (L × A) → Prop} {f : FiniteTrace A L}
    {inftr : Seq (L × A)} : Eventually (Eventually ψ) f inftr → Eventually ψ f inftr := by
  intro h
  induction h with
  | now f inftr h => exact h
  | later f ℓ a inftr _ IH => exact .later _ _ _ _ IH

@[rocq_alias trillium.eventually_take_drop]
theorem eventually_take_drop {ψ : FiniteTrace A L → Seq (L × A) → Prop} {f : FiniteTrace A L}
    {inftr : Seq (L × A)} :
    Eventually ψ f inftr ↔ ∃ n, ψ (f +trl+ inftr.take n) (inftr.drop n) := by
  constructor
  · intro h
    induction h with
    | now f inftr h => exact ⟨0, by simpa using h⟩
    | later f ℓ a inftr _ IH =>
      obtain ⟨n, hn⟩ := IH
      exact ⟨n + 1, by simpa using hn⟩
  · rintro ⟨n, hn⟩
    induction n generalizing f inftr with
    | zero => exact .now _ _ (by simpa using hn)
    | succ n IH =>
      cases inftr with
      | nil => exact .now _ _ (by simpa using hn)
      | cons p inftr =>
        obtain ⟨ℓ, a⟩ := p
        exact .later _ _ _ _ (IH (by simpa using hn))

@[rocq_alias trillium.eventually_exists]
theorem eventually_exists {B : Sort _} {Ψ : B → FiniteTrace A L → Seq (L × A) → Prop}
    {f : FiniteTrace A L} {inftr : Seq (L × A)} :
    (∃ b, Eventually (Ψ b) f inftr) ↔
      Eventually (fun f' inftr' => ∃ b, Ψ b f' inftr') f inftr := by
  simp only [eventually_take_drop]
  exact exists_comm

/-! ### Other properties -/

@[rocq_alias trillium.always_eventually_idemp]
theorem Always.eventually_idemp {ψ : FiniteTrace A L → Seq (L × A) → Prop}
    {f : FiniteTrace A L} {inftr : Seq (L × A)} :
    Always (Eventually ψ) f inftr → Always (Eventually (Always (Eventually ψ))) f inftr :=
  fun h => h.idemp.mono fun _ _ h => .of_holds h

@[rocq_alias trillium.eventually_always_combine]
theorem Eventually.always_combine {ψ1 ψ2 : FiniteTrace A L → Seq (L × A) → Prop}
    {f : FiniteTrace A L} {inftr : Seq (L × A)} :
    Eventually (Always ψ1) f inftr → Eventually (Always ψ2) f inftr →
      Eventually (fun f' inftr' => Always ψ1 f' inftr' ∧ Always ψ2 f' inftr') f inftr := by
  simp only [eventually_take_drop]
  rintro ⟨n, hn⟩ ⟨m, hm⟩
  refine ⟨max n m, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.le_max_left n m)
    rw [hk, InfList.take_add, Seq.dropn_add, ← appendList_appendList]
    exact hn.unroll_n k
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.le_max_right n m)
    rw [hk, InfList.take_add, Seq.dropn_add, ← appendList_appendList]
    exact hm.unroll_n k

@[rocq_alias trillium.eventually_and_always]
theorem Eventually.and_always {ψ1 ψ2 : FiniteTrace A L → Seq (L × A) → Prop}
    {f : FiniteTrace A L} {inftr : Seq (L × A)} :
    Eventually ψ1 f inftr → Always ψ2 f inftr →
      Eventually (fun f' inftr' => ψ1 f' inftr' ∧ Always ψ2 f' inftr') f inftr := by
  intro hev hal
  obtain ⟨n, hn⟩ := eventually_take_drop.mp hev
  exact eventually_take_drop.mpr ⟨n, hn, hal.unroll_n n⟩

@[rocq_alias trillium.eventually_forall_combine]
theorem Eventually.forall_combine {B : Type _} [Finite B]
    {Ψ : B → FiniteTrace A L → Seq (L × A) → Prop} {f : FiniteTrace A L}
    {inftr : Seq (L × A)} :
    (∀ b, Eventually (Always (Ψ b)) f inftr) →
      Eventually (fun f' inftr' => ∀ b, Always (Ψ b) f' inftr') f inftr := by
  intro Hfa
  obtain ⟨enum, -, Henum⟩ := Finite.exists_univ_list B
  suffices H : Eventually (fun f' inftr' => ∀ b, b ∈ enum → Always (Ψ b) f' inftr') f inftr from
    H.mono fun _ _ h b => h b (Henum b)
  clear Henum
  induction enum with
  | nil => exact .of_holds fun _ h => absurd h List.not_mem_nil
  | cons b l IHl =>
    have IHl' : Eventually (Always fun f' inftr' => ∀ b, b ∈ l → Ψ b f' inftr') f inftr :=
      IHl.mono fun _ _ Hfa' => always_forall.mp fun b' => always_impl.mp (Hfa' b')
    refine (Eventually.always_combine (Hfa b) IHl').mono ?_
    rintro f' inftr' ⟨Hal1, Hal2⟩ b' hb'
    rcases List.mem_cons.mp hb' with rfl | hb'
    · exact Hal1
    · exact always_impl.mpr (always_forall.mpr Hal2 b') hb'

end single

/-! ## Pairs of traces -/

/-- Rocq `eventually2`. -/
@[rocq_alias trillium.eventually2]
inductive Eventually2 {A B L1 L2 : Type _}
    (ψ : FiniteTrace A L1 → FiniteTrace B L2 → Seq (L1 × A) → Seq (L2 × B) → Prop) :
    FiniteTrace A L1 → FiniteTrace B L2 → Seq (L1 × A) → Seq (L2 × B) → Prop
  | now f g inftr inftrb :
    SameLength inftr inftrb → ψ f g inftr inftrb → Eventually2 ψ f g inftr inftrb
  | later f ℓ1 ℓ2 a g b inftr inftrb :
    Eventually2 ψ (f :tr[ℓ1]: a) (g :tr[ℓ2]: b) inftr inftrb →
    Eventually2 ψ f g (.cons (ℓ1, a) inftr) (.cons (ℓ2, b) inftrb)

/-- Rocq `always2`. -/
@[rocq_alias trillium.always2]
coinductive Always2 {A B L1 L2 : Type _}
    (ψ : FiniteTrace A L1 → FiniteTrace B L2 → Seq (L1 × A) → Seq (L2 × B) → Prop) :
    FiniteTrace A L1 → FiniteTrace B L2 → Seq (L1 × A) → Seq (L2 × B) → Prop where
  | continued f g inftr inftrb :
    ψ f g inftr inftrb →
    SameLength inftr inftrb →
    (∀ a inftr' b inftrb' ℓ1 ℓ2,
      inftr = .cons (ℓ1, a) inftr' → inftrb = .cons (ℓ2, b) inftrb' →
      Always2 ψ (f :tr[ℓ1]: a) (g :tr[ℓ2]: b) inftr' inftrb') →
    Always2 ψ f g inftr inftrb

section two

variable {A B L1 L2 : Type _}
variable {ψ ψ' ψ1 ψ2 : FiniteTrace A L1 → FiniteTrace B L2 → Seq (L1 × A) → Seq (L2 × B) → Prop}
variable {f : FiniteTrace A L1} {g : FiniteTrace B L2} {inftr : Seq (L1 × A)}
  {inftrb : Seq (L2 × B)}

/-- Destructor of `Always2` (one unfolding step). -/
theorem Always2.dest (h : Always2 ψ f g inftr inftrb) :
    ψ f g inftr inftrb ∧ SameLength inftr inftrb ∧
      ∀ a inftr' b inftrb' ℓ1 ℓ2, inftr = .cons (ℓ1, a) inftr' → inftrb = .cons (ℓ2, b) inftrb' →
        Always2 ψ (f :tr[ℓ1]: a) (g :tr[ℓ2]: b) inftr' inftrb' := by
  cases h with
  | continued _ _ _ _ h1 h2 h3 => exact ⟨h1, h2, h3⟩

/-! ### `Always2` is a comonad -/

@[rocq_alias trillium.always2_mono]
theorem Always2.mono (Hψs : ∀ f' inftr' g' inftrb', ψ f' g' inftr' inftrb' → ψ' f' g' inftr' inftrb') :
    Always2 ψ f g inftr inftrb → Always2 ψ' f g inftr inftrb := by
  refine Always2.coinduct ψ' (Always2 ψ) ?_ f g inftr inftrb
  intro f g inftr inftrb h
  obtain ⟨h1, h2, h3⟩ := h.dest
  exact ⟨Hψs _ _ _ _ h1, h2, h3⟩

@[rocq_alias trillium.always2_holds]
theorem Always2.holds : Always2 ψ f g inftr inftrb → ψ f g inftr inftrb := by
  exact fun h => h.dest.1

@[rocq_alias trillium.always2_idemp]
theorem Always2.idemp : Always2 ψ f g inftr inftrb → Always2 (Always2 ψ) f g inftr inftrb := by
  refine Always2.coinduct (Always2 ψ) (Always2 ψ) ?_ f g inftr inftrb
  intro f g inftr inftrb h
  exact ⟨h, h.dest.2⟩

@[rocq_alias trillium.always2_unroll]
theorem Always2.unroll {a : A} {b : B} {ℓ1 : L1} {ℓ2 : L2} :
    Always2 ψ f g (.cons (ℓ1, a) inftr) (.cons (ℓ2, b) inftrb) →
      Always2 ψ (f :tr[ℓ1]: a) (g :tr[ℓ2]: b) inftr inftrb := by
  exact fun h => h.dest.2.2 _ _ _ _ _ _ rfl rfl

@[rocq_alias trillium.always2_inflist_same_length]
theorem Always2.sameLength : Always2 ψ f g inftr inftrb → SameLength inftr inftrb := by
  exact fun h => h.dest.2.1

@[rocq_alias trillium.always2_unroll_n]
theorem Always2.unroll_n (n : Nat) :
    Always2 ψ f g inftr inftrb →
      Always2 ψ (f +trl+ inftr.take n) (g +trl+ inftrb.take n) (inftr.drop n) (inftrb.drop n) := by
  induction n generalizing f g inftr inftrb with
  | zero => simp
  | succ n IH =>
    intro h
    have hsl := h.sameLength
    cases inftr with
    | nil =>
      cases inftrb with
      | nil => simpa using h
      | cons q inftrb => exact absurd hsl (not_sameLength_nil_cons _ _)
    | cons p inftr =>
      cases inftrb with
      | nil => exact absurd hsl (not_sameLength_cons_nil _ _)
      | cons q inftrb =>
        obtain ⟨ℓ1, a⟩ := p
        obtain ⟨ℓ2, b⟩ := q
        simpa using IH h.unroll

@[rocq_alias trillium.always2_and_inflist_same_length]
theorem always2_and_sameLength :
    Always2 ψ f g inftr inftrb ↔
      Always2 (fun f' g' inftr' inftrb' => ψ f' g' inftr' inftrb' ∧ SameLength inftr' inftrb')
        f g inftr inftrb := by
  refine ⟨?_, Always2.mono fun _ _ _ _ h => h.1⟩
  refine Always2.coinduct _ (Always2 ψ) ?_ f g inftr inftrb
  intro f g inftr inftrb h
  obtain ⟨h1, h2, h3⟩ := h.dest
  exact ⟨⟨h1, h2⟩, h2, h3⟩

@[rocq_alias trillium.always2_take_drop]
theorem always2_take_drop :
    Always2 ψ f g inftr inftrb ↔
      ∀ n, ψ (f +trl+ inftr.take n) (g +trl+ inftrb.take n) (inftr.drop n) (inftrb.drop n) ∧
        SameLength inftr inftrb := by
  constructor
  · exact fun h n => ⟨(h.unroll_n n).holds, h.sameLength⟩
  · refine Always2.coinduct ψ (fun f g inftr inftrb => ∀ n,
      ψ (f +trl+ inftr.take n) (g +trl+ inftrb.take n) (inftr.drop n) (inftrb.drop n) ∧
        SameLength inftr inftrb) ?_ f g inftr inftrb
    intro f g inftr inftrb Hn
    refine ⟨by simpa using (Hn 0).1, (Hn 0).2, ?_⟩
    rintro a inftr' b inftrb' ℓ1 ℓ2 rfl rfl n
    simpa [sameLength_cons] using Hn (n + 1)

@[rocq_alias trillium.always2_and]
theorem always2_and :
    Always2 ψ1 f g inftr inftrb ∧ Always2 ψ2 f g inftr inftrb ↔
      Always2 (fun f' g' inftr' inftrb' => ψ1 f' g' inftr' inftrb' ∧ ψ2 f' g' inftr' inftrb')
        f g inftr inftrb := by
  simp only [always2_take_drop]
  exact ⟨fun ⟨h1, h2⟩ n => ⟨⟨(h1 n).1, (h2 n).1⟩, (h1 n).2⟩,
    fun h => ⟨fun n => ⟨(h n).1.1, (h n).2⟩, fun n => ⟨(h n).1.2, (h n).2⟩⟩⟩

@[rocq_alias trillium.always2_forall]
theorem always2_forall {C : Sort _} [Nonempty C]
    {Ψ : C → FiniteTrace A L1 → FiniteTrace B L2 → Seq (L1 × A) → Seq (L2 × B) → Prop} :
    (∀ b, Always2 (Ψ b) f g inftr inftrb) ↔
      Always2 (fun f' g' inftr' inftrb' => ∀ b, Ψ b f' g' inftr' inftrb') f g inftr inftrb := by
  simp only [always2_take_drop]
  obtain ⟨c⟩ := ‹Nonempty C›
  exact ⟨fun h n => ⟨fun b => (h b n).1, (h c n).2⟩, fun h b n => ⟨(h n).1 b, (h n).2⟩⟩

@[rocq_alias trillium.always2_impl]
theorem always2_impl {P : Prop} (hsl : SameLength inftr inftrb) :
    (P → Always2 ψ f g inftr inftrb) ↔
      Always2 (fun f' g' inftr' inftrb' => P → ψ f' g' inftr' inftrb') f g inftr inftrb := by
  simp only [always2_take_drop]
  exact ⟨fun h n => ⟨fun p => (h p n).1, hsl⟩, fun h p n => ⟨(h n).1 p, (h n).2⟩⟩

/-! ### `Eventually2` is a monad -/

@[rocq_alias trillium.eventually2_mono]
theorem Eventually2.mono
    (Hψs : ∀ f' g' inftr' inftrb', ψ f' g' inftr' inftrb' → ψ' f' g' inftr' inftrb') :
    Eventually2 ψ f g inftr inftrb → Eventually2 ψ' f g inftr inftrb := by
  intro h
  induction h with
  | now f g inftr inftrb hsl h => exact .now _ _ _ _ hsl (Hψs _ _ _ _ h)
  | later _ _ _ _ _ _ _ _ _ IH => exact .later _ _ _ _ _ _ _ _ IH

@[rocq_alias trillium.holds_eventually2]
theorem Eventually2.of_holds :
    SameLength inftr inftrb → ψ f g inftr inftrb → Eventually2 ψ f g inftr inftrb := .now _ _ _ _

@[rocq_alias trillium.eventually2_idemp]
theorem Eventually2.idemp :
    Eventually2 (Eventually2 ψ) f g inftr inftrb → Eventually2 ψ f g inftr inftrb := by
  intro h
  induction h with
  | now _ _ _ _ _ h => exact h
  | later _ _ _ _ _ _ _ _ _ IH => exact .later _ _ _ _ _ _ _ _ IH

@[rocq_alias trillium.eventually2_inflist_same_length]
theorem Eventually2.sameLength : Eventually2 ψ f g inftr inftrb → SameLength inftr inftrb := by
  intro h
  induction h with
  | now _ _ _ _ hsl _ => exact hsl
  | later _ _ _ _ _ _ _ _ _ IH => exact sameLength_cons.mpr IH

@[rocq_alias trillium.eventually2_and_inflist_same_length]
theorem eventually2_and_sameLength :
    Eventually2 ψ f g inftr inftrb ↔
      Eventually2 (fun f' g' inftr' inftrb' => ψ f' g' inftr' inftrb' ∧ SameLength inftr' inftrb')
        f g inftr inftrb := by
  refine ⟨fun h => ?_, Eventually2.mono fun _ _ _ _ h => h.1⟩
  induction h with
  | now _ _ _ _ hsl h => exact .now _ _ _ _ hsl ⟨h, hsl⟩
  | later _ _ _ _ _ _ _ _ _ IH => exact .later _ _ _ _ _ _ _ _ IH

@[rocq_alias trillium.eventually2_take_drop]
theorem eventually2_take_drop :
    Eventually2 ψ f g inftr inftrb ↔
      ∃ n, ψ (f +trl+ inftr.take n) (g +trl+ inftrb.take n) (inftr.drop n) (inftrb.drop n) ∧
        SameLength inftr inftrb := by
  constructor
  · intro h
    induction h with
    | now f g inftr inftrb hsl h => exact ⟨0, by simpa using h, hsl⟩
    | later f ℓ1 ℓ2 a g b inftr inftrb _ IH =>
      obtain ⟨n, hn, hsl⟩ := IH
      exact ⟨n + 1, by simpa using hn, sameLength_cons.mpr hsl⟩
  · rintro ⟨n, hn, hsl⟩
    induction n generalizing f g inftr inftrb with
    | zero => exact .now _ _ _ _ hsl (by simpa using hn)
    | succ n IH =>
      cases inftr with
      | nil =>
        cases inftrb with
        | nil => exact .now _ _ _ _ hsl (by simpa using hn)
        | cons q inftrb => exact absurd hsl (not_sameLength_nil_cons _ _)
      | cons p inftr =>
        cases inftrb with
        | nil => exact absurd hsl (not_sameLength_cons_nil _ _)
        | cons q inftrb =>
          obtain ⟨ℓ1, a⟩ := p
          obtain ⟨ℓ2, b⟩ := q
          exact .later _ _ _ _ _ _ _ _ (IH (by simpa using hn) (sameLength_cons.mp hsl))

@[rocq_alias trillium.eventually2_exists]
theorem eventually2_exists {C : Sort _}
    {Ψ : C → FiniteTrace A L1 → FiniteTrace B L2 → Seq (L1 × A) → Seq (L2 × B) → Prop} :
    (∃ b, Eventually2 (Ψ b) f g inftr inftrb) ↔
      Eventually2 (fun f' g' inftr' inftrb' => ∃ b, Ψ b f' g' inftr' inftrb') f g inftr inftrb := by
  simp only [eventually2_take_drop]
  exact ⟨fun ⟨b, n, h, hsl⟩ => ⟨n, ⟨b, h⟩, hsl⟩, fun ⟨n, ⟨b, h⟩, hsl⟩ => ⟨b, n, h, hsl⟩⟩

/-! ### Other properties -/

@[rocq_alias trillium.always2_eventually2_idemp]
theorem Always2.eventually2_idemp :
    Always2 (Eventually2 ψ) f g inftr inftrb →
      Always2 (Eventually2 (Always2 (Eventually2 ψ))) f g inftr inftrb :=
  fun h => h.idemp.mono fun _ _ _ _ h => .of_holds h.sameLength h

@[rocq_alias trillium.eventually2_always2_combine]
theorem Eventually2.always2_combine :
    Eventually2 (Always2 ψ1) f g inftr inftrb → Eventually2 (Always2 ψ2) f g inftr inftrb →
      Eventually2 (fun f' g' inftr' inftrb' =>
        Always2 ψ1 f' g' inftr' inftrb' ∧ Always2 ψ2 f' g' inftr' inftrb') f g inftr inftrb := by
  simp only [eventually2_take_drop]
  rintro ⟨n, hn, hsl⟩ ⟨m, hm, -⟩
  refine ⟨max n m, ⟨?_, ?_⟩, hsl⟩
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.le_max_left n m)
    rw [hk, InfList.take_add, InfList.take_add, Seq.dropn_add, Seq.dropn_add, ← appendList_appendList,
      ← appendList_appendList]
    exact hn.unroll_n k
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.le_max_right n m)
    rw [hk, InfList.take_add, InfList.take_add, Seq.dropn_add, Seq.dropn_add, ← appendList_appendList,
      ← appendList_appendList]
    exact hm.unroll_n k

@[rocq_alias trillium.eventually2_and_always2]
theorem Eventually2.and_always2 :
    Eventually2 ψ1 f g inftr inftrb → Always2 ψ2 f g inftr inftrb →
      Eventually2 (fun f' g' inftr' inftrb' =>
        ψ1 f' g' inftr' inftrb' ∧ Always2 ψ2 f' g' inftr' inftrb') f g inftr inftrb := by
  intro hev hal
  obtain ⟨n, hn, hsl⟩ := eventually2_take_drop.mp hev
  exact eventually2_take_drop.mpr ⟨n, ⟨hn, hal.unroll_n n⟩, hsl⟩

@[rocq_alias trillium.eventually2_forall_combine]
theorem Eventually2.forall_combine {C : Type _} [Finite C] [Nonempty C]
    {Ψ : C → FiniteTrace A L1 → FiniteTrace B L2 → Seq (L1 × A) → Seq (L2 × B) → Prop} :
    (∀ c, Eventually2 (Always2 (Ψ c)) f g inftr inftrb) →
      Eventually2 (fun f' g' inftr' inftrb' => ∀ c, Always2 (Ψ c) f' g' inftr' inftrb')
        f g inftr inftrb := by
  intro Hfa
  obtain ⟨enum, -, Henum⟩ := Finite.exists_univ_list C
  suffices H : Eventually2 (fun f' g' inftr' inftrb' =>
      ∀ c, c ∈ enum → Always2 (Ψ c) f' g' inftr' inftrb') f g inftr inftrb from
    H.mono fun _ _ _ _ h c => h c (Henum c)
  clear Henum
  induction enum with
  | nil =>
    obtain ⟨c⟩ := ‹Nonempty C›
    exact .of_holds (Hfa c).sameLength fun _ h => absurd h List.not_mem_nil
  | cons c l IHl =>
    have IHl' : Eventually2 (Always2 fun f' g' inftr' inftrb' =>
        ∀ c, c ∈ l → Ψ c f' g' inftr' inftrb') f g inftr inftrb := by
      refine (eventually2_and_sameLength.mp IHl).mono ?_
      rintro f' g' inftr' inftrb' ⟨Hfa', hsl⟩
      exact always2_forall.mp fun c' => (always2_impl hsl).mp (Hfa' c')
    refine (Eventually2.always2_combine (Hfa c) IHl').mono ?_
    rintro f' g' inftr' inftrb' ⟨Hal1, Hal2⟩ c' hc'
    rcases List.mem_cons.mp hc' with rfl | hc'
    · exact Hal1
    · exact (always2_impl Hal1.sameLength).mpr (always2_forall.mpr Hal2 c') hc'

end two

/-! ## Triples of traces -/

/-- Rocq `eventually3`. -/
@[rocq_alias trillium.eventually3]
inductive Eventually3 {A B C L1 L2 L3 : Type _}
    (ψ : FiniteTrace A L1 → FiniteTrace B L2 → FiniteTrace C L3 →
      Seq (L1 × A) → Seq (L2 × B) → Seq (L3 × C) → Prop) :
    FiniteTrace A L1 → FiniteTrace B L2 → FiniteTrace C L3 →
      Seq (L1 × A) → Seq (L2 × B) → Seq (L3 × C) → Prop
  | now f g h inftr inftrb inftrc :
    SameLength inftr inftrb → SameLength inftrb inftrc → ψ f g h inftr inftrb inftrc →
    Eventually3 ψ f g h inftr inftrb inftrc
  | later f a g b h c ℓ1 ℓ2 ℓ3 inftr inftrb inftrc :
    Eventually3 ψ (f :tr[ℓ1]: a) (g :tr[ℓ2]: b) (h :tr[ℓ3]: c) inftr inftrb inftrc →
    Eventually3 ψ f g h (.cons (ℓ1, a) inftr) (.cons (ℓ2, b) inftrb) (.cons (ℓ3, c) inftrc)

/-- Rocq `always3`. -/
@[rocq_alias trillium.always3]
coinductive Always3 {A B C L1 L2 L3 : Type _}
    (ψ : FiniteTrace A L1 → FiniteTrace B L2 → FiniteTrace C L3 →
      Seq (L1 × A) → Seq (L2 × B) → Seq (L3 × C) → Prop) :
    FiniteTrace A L1 → FiniteTrace B L2 → FiniteTrace C L3 →
      Seq (L1 × A) → Seq (L2 × B) → Seq (L3 × C) → Prop where
  | continued f g h inftr inftrb inftrc :
    ψ f g h inftr inftrb inftrc →
    SameLength inftr inftrb →
    SameLength inftrb inftrc →
    (∀ a ℓ1 inftr' b ℓ2 inftrb' c ℓ3 inftrc',
      inftr = .cons (ℓ1, a) inftr' → inftrb = .cons (ℓ2, b) inftrb' →
      inftrc = .cons (ℓ3, c) inftrc' →
      Always3 ψ (f :tr[ℓ1]: a) (g :tr[ℓ2]: b) (h :tr[ℓ3]: c) inftr' inftrb' inftrc') →
    Always3 ψ f g h inftr inftrb inftrc

section three

variable {A B C L1 L2 L3 : Type _}
variable {ψ ψ' ψ1 ψ2 : FiniteTrace A L1 → FiniteTrace B L2 → FiniteTrace C L3 →
  Seq (L1 × A) → Seq (L2 × B) → Seq (L3 × C) → Prop}
variable {f : FiniteTrace A L1} {g : FiniteTrace B L2} {h : FiniteTrace C L3}
  {inftr : Seq (L1 × A)} {inftrb : Seq (L2 × B)} {inftrc : Seq (L3 × C)}

/-- Destructor of `Always3` (one unfolding step). -/
theorem Always3.dest (H : Always3 ψ f g h inftr inftrb inftrc) :
    ψ f g h inftr inftrb inftrc ∧ SameLength inftr inftrb ∧ SameLength inftrb inftrc ∧
      ∀ a ℓ1 inftr' b ℓ2 inftrb' c ℓ3 inftrc',
        inftr = .cons (ℓ1, a) inftr' → inftrb = .cons (ℓ2, b) inftrb' →
        inftrc = .cons (ℓ3, c) inftrc' →
        Always3 ψ (f :tr[ℓ1]: a) (g :tr[ℓ2]: b) (h :tr[ℓ3]: c) inftr' inftrb' inftrc' := by
  cases H with
  | continued _ _ _ _ _ _ h1 h2 h3 h4 => exact ⟨h1, h2, h3, h4⟩

/-! ### `Always3` is a comonad -/

@[rocq_alias trillium.always3_mono]
theorem Always3.mono
    (Hψs : ∀ f' g' h' inftr' inftrb' inftrc',
      ψ f' g' h' inftr' inftrb' inftrc' → ψ' f' g' h' inftr' inftrb' inftrc') :
    Always3 ψ f g h inftr inftrb inftrc → Always3 ψ' f g h inftr inftrb inftrc := by
  refine Always3.coinduct ψ' (Always3 ψ) ?_ f g h inftr inftrb inftrc
  intro f g h inftr inftrb inftrc H
  obtain ⟨h1, h2, h3, h4⟩ := H.dest
  exact ⟨Hψs _ _ _ _ _ _ h1, h2, h3, h4⟩

@[rocq_alias trillium.always3_holds]
theorem Always3.holds : Always3 ψ f g h inftr inftrb inftrc → ψ f g h inftr inftrb inftrc := by
  exact fun H => H.dest.1

@[rocq_alias trillium.always3_idemp]
theorem Always3.idemp :
    Always3 ψ f g h inftr inftrb inftrc → Always3 (Always3 ψ) f g h inftr inftrb inftrc := by
  refine Always3.coinduct (Always3 ψ) (Always3 ψ) ?_ f g h inftr inftrb inftrc
  intro f g h inftr inftrb inftrc H
  exact ⟨H, H.dest.2⟩

@[rocq_alias trillium.always3_unroll]
theorem Always3.unroll {a : A} {b : B} {c : C} {ℓ1 : L1} {ℓ2 : L2} {ℓ3 : L3} :
    Always3 ψ f g h (.cons (ℓ1, a) inftr) (.cons (ℓ2, b) inftrb) (.cons (ℓ3, c) inftrc) →
      Always3 ψ (f :tr[ℓ1]: a) (g :tr[ℓ2]: b) (h :tr[ℓ3]: c) inftr inftrb inftrc := by
  exact fun H => H.dest.2.2.2 _ _ _ _ _ _ _ _ _ rfl rfl rfl

@[rocq_alias trillium.always3_inflist_same_length]
theorem Always3.sameLength :
    Always3 ψ f g h inftr inftrb inftrc → SameLength inftr inftrb ∧ SameLength inftrb inftrc := by
  exact fun H => ⟨H.dest.2.1, H.dest.2.2.1⟩

@[rocq_alias trillium.always3_unroll_n]
theorem Always3.unroll_n (n : Nat) :
    Always3 ψ f g h inftr inftrb inftrc →
      Always3 ψ (f +trl+ inftr.take n) (g +trl+ inftrb.take n) (h +trl+ inftrc.take n)
        (inftr.drop n) (inftrb.drop n) (inftrc.drop n) := by
  induction n generalizing f g h inftr inftrb inftrc with
  | zero => simp
  | succ n IH =>
    intro H
    obtain ⟨hsl1, hsl2⟩ := H.sameLength
    cases inftr with
    | nil =>
      cases inftrb with
      | nil =>
        cases inftrc with
        | nil => simpa using H
        | cons _ _ => exact absurd hsl2 (not_sameLength_nil_cons _ _)
      | cons _ _ => exact absurd hsl1 (not_sameLength_nil_cons _ _)
    | cons p inftr =>
      cases inftrb with
      | nil => exact absurd hsl1 (not_sameLength_cons_nil _ _)
      | cons q inftrb =>
        cases inftrc with
        | nil => exact absurd hsl2 (not_sameLength_cons_nil _ _)
        | cons r inftrc =>
          obtain ⟨ℓ1, a⟩ := p
          obtain ⟨ℓ2, b⟩ := q
          obtain ⟨ℓ3, c⟩ := r
          simpa using IH H.unroll

@[rocq_alias trillium.always3_and_inflist_same_length]
theorem always3_and_sameLength :
    Always3 ψ f g h inftr inftrb inftrc ↔
      Always3 (fun f' g' h' inftr' inftrb' inftrc' =>
        ψ f' g' h' inftr' inftrb' inftrc' ∧ SameLength inftr' inftrb' ∧
          SameLength inftrb' inftrc') f g h inftr inftrb inftrc := by
  refine ⟨?_, Always3.mono fun _ _ _ _ _ _ H => H.1⟩
  refine Always3.coinduct _ (Always3 ψ) ?_ f g h inftr inftrb inftrc
  intro f g h inftr inftrb inftrc H
  obtain ⟨h1, h2, h3, h4⟩ := H.dest
  exact ⟨⟨h1, h2, h3⟩, h2, h3, h4⟩

@[rocq_alias trillium.always3_take_drop]
theorem always3_take_drop :
    Always3 ψ f g h inftr inftrb inftrc ↔
      ∀ n, ψ (f +trl+ inftr.take n) (g +trl+ inftrb.take n) (h +trl+ inftrc.take n)
          (inftr.drop n) (inftrb.drop n) (inftrc.drop n) ∧
        SameLength inftr inftrb ∧ SameLength inftrb inftrc := by
  constructor
  · exact fun H n => ⟨(H.unroll_n n).holds, H.sameLength⟩
  · refine Always3.coinduct ψ (fun f g h inftr inftrb inftrc => ∀ n,
      ψ (f +trl+ inftr.take n) (g +trl+ inftrb.take n) (h +trl+ inftrc.take n)
          (inftr.drop n) (inftrb.drop n) (inftrc.drop n) ∧
        SameLength inftr inftrb ∧ SameLength inftrb inftrc) ?_ f g h inftr inftrb inftrc
    intro f g h inftr inftrb inftrc Hn
    refine ⟨by simpa using (Hn 0).1, (Hn 0).2.1, (Hn 0).2.2, ?_⟩
    rintro a ℓ1 inftr' b ℓ2 inftrb' c ℓ3 inftrc' rfl rfl rfl n
    simpa [sameLength_cons] using Hn (n + 1)

@[rocq_alias trillium.always3_and]
theorem always3_and :
    Always3 ψ1 f g h inftr inftrb inftrc ∧ Always3 ψ2 f g h inftr inftrb inftrc ↔
      Always3 (fun f' g' h' inftr' inftrb' inftrc' =>
        ψ1 f' g' h' inftr' inftrb' inftrc' ∧ ψ2 f' g' h' inftr' inftrb' inftrc')
        f g h inftr inftrb inftrc := by
  simp only [always3_take_drop]
  exact ⟨fun ⟨h1, h2⟩ n => ⟨⟨(h1 n).1, (h2 n).1⟩, (h1 n).2⟩,
    fun H => ⟨fun n => ⟨(H n).1.1, (H n).2⟩, fun n => ⟨(H n).1.2, (H n).2⟩⟩⟩

@[rocq_alias trillium.always3_forall]
theorem always3_forall {D : Sort _} [Nonempty D]
    {Ψ : D → FiniteTrace A L1 → FiniteTrace B L2 → FiniteTrace C L3 →
      Seq (L1 × A) → Seq (L2 × B) → Seq (L3 × C) → Prop} :
    (∀ d, Always3 (Ψ d) f g h inftr inftrb inftrc) ↔
      Always3 (fun f' g' h' inftr' inftrb' inftrc' => ∀ b, Ψ b f' g' h' inftr' inftrb' inftrc')
        f g h inftr inftrb inftrc := by
  simp only [always3_take_drop]
  obtain ⟨d⟩ := ‹Nonempty D›
  exact ⟨fun H n => ⟨fun b => (H b n).1, (H d n).2⟩, fun H b n => ⟨(H n).1 b, (H n).2⟩⟩

@[rocq_alias trillium.always3_impl]
theorem always3_impl {P : Prop} (hsl1 : SameLength inftr inftrb)
    (hsl2 : SameLength inftrb inftrc) :
    (P → Always3 ψ f g h inftr inftrb inftrc) ↔
      Always3 (fun f' g' h' inftr' inftrb' inftrc' => P → ψ f' g' h' inftr' inftrb' inftrc')
        f g h inftr inftrb inftrc := by
  simp only [always3_take_drop]
  exact ⟨fun H n => ⟨fun p => (H p n).1, hsl1, hsl2⟩, fun H p n => ⟨(H n).1 p, (H n).2⟩⟩

/-! ### `Eventually3` is a monad -/

@[rocq_alias trillium.eventually3_mono]
theorem Eventually3.mono
    (Hψs : ∀ f' g' h' inftr' inftrb' inftrc',
      ψ f' g' h' inftr' inftrb' inftrc' → ψ' f' g' h' inftr' inftrb' inftrc') :
    Eventually3 ψ f g h inftr inftrb inftrc → Eventually3 ψ' f g h inftr inftrb inftrc := by
  intro H
  induction H with
  | now _ _ _ _ _ _ hsl1 hsl2 H => exact .now _ _ _ _ _ _ hsl1 hsl2 (Hψs _ _ _ _ _ _ H)
  | later _ _ _ _ _ _ _ _ _ _ _ _ _ IH => exact .later _ _ _ _ _ _ _ _ _ _ _ _ IH

@[rocq_alias trillium.holds_eventually3]
theorem Eventually3.of_holds :
    SameLength inftr inftrb → SameLength inftrb inftrc → ψ f g h inftr inftrb inftrc →
      Eventually3 ψ f g h inftr inftrb inftrc := .now _ _ _ _ _ _

@[rocq_alias trillium.eventually3_idemp]
theorem Eventually3.idemp :
    Eventually3 (Eventually3 ψ) f g h inftr inftrb inftrc →
      Eventually3 ψ f g h inftr inftrb inftrc := by
  intro H
  induction H with
  | now _ _ _ _ _ _ _ _ H => exact H
  | later _ _ _ _ _ _ _ _ _ _ _ _ _ IH => exact .later _ _ _ _ _ _ _ _ _ _ _ _ IH

@[rocq_alias trillium.eventually3_inflist_same_length]
theorem Eventually3.sameLength :
    Eventually3 ψ f g h inftr inftrb inftrc →
      SameLength inftr inftrb ∧ SameLength inftrb inftrc := by
  intro H
  induction H with
  | now _ _ _ _ _ _ hsl1 hsl2 _ => exact ⟨hsl1, hsl2⟩
  | later _ _ _ _ _ _ _ _ _ _ _ _ _ IH => exact ⟨sameLength_cons.mpr IH.1, sameLength_cons.mpr IH.2⟩

@[rocq_alias trillium.eventually3_and_inflist_same_length]
theorem eventually3_and_sameLength :
    Eventually3 ψ f g h inftr inftrb inftrc ↔
      Eventually3 (fun f' g' h' inftr' inftrb' inftrc' =>
        ψ f' g' h' inftr' inftrb' inftrc' ∧ SameLength inftr' inftrb' ∧
          SameLength inftrb' inftrc') f g h inftr inftrb inftrc := by
  refine ⟨fun H => ?_, Eventually3.mono fun _ _ _ _ _ _ H => H.1⟩
  induction H with
  | now _ _ _ _ _ _ hsl1 hsl2 H => exact .now _ _ _ _ _ _ hsl1 hsl2 ⟨H, hsl1, hsl2⟩
  | later _ _ _ _ _ _ _ _ _ _ _ _ _ IH => exact .later _ _ _ _ _ _ _ _ _ _ _ _ IH

@[rocq_alias trillium.eventually3_take_drop]
theorem eventually3_take_drop :
    Eventually3 ψ f g h inftr inftrb inftrc ↔
      ∃ n, ψ (f +trl+ inftr.take n) (g +trl+ inftrb.take n) (h +trl+ inftrc.take n)
          (inftr.drop n) (inftrb.drop n) (inftrc.drop n) ∧
        SameLength inftr inftrb ∧ SameLength inftrb inftrc := by
  constructor
  · intro H
    induction H with
    | now _ _ _ _ _ _ hsl1 hsl2 H => exact ⟨0, by simpa using H, hsl1, hsl2⟩
    | later _ _ _ _ _ _ _ _ _ _ _ _ _ IH =>
      obtain ⟨n, hn, hsl1, hsl2⟩ := IH
      exact ⟨n + 1, by simpa using hn, sameLength_cons.mpr hsl1, sameLength_cons.mpr hsl2⟩
  · rintro ⟨n, hn, hsl1, hsl2⟩
    induction n generalizing f g h inftr inftrb inftrc with
    | zero => exact .now _ _ _ _ _ _ hsl1 hsl2 (by simpa using hn)
    | succ n IH =>
      cases inftr with
      | nil =>
        cases inftrb with
        | nil =>
          cases inftrc with
          | nil => exact .now _ _ _ _ _ _ hsl1 hsl2 (by simpa using hn)
          | cons _ _ => exact absurd hsl2 (not_sameLength_nil_cons _ _)
        | cons _ _ => exact absurd hsl1 (not_sameLength_nil_cons _ _)
      | cons p inftr =>
        cases inftrb with
        | nil => exact absurd hsl1 (not_sameLength_cons_nil _ _)
        | cons q inftrb =>
          cases inftrc with
          | nil => exact absurd hsl2 (not_sameLength_cons_nil _ _)
          | cons r inftrc =>
            obtain ⟨ℓ1, a⟩ := p
            obtain ⟨ℓ2, b⟩ := q
            obtain ⟨ℓ3, c⟩ := r
            exact .later _ _ _ _ _ _ _ _ _ _ _ _
              (IH (by simpa using hn) (sameLength_cons.mp hsl1) (sameLength_cons.mp hsl2))

@[rocq_alias trillium.eventually3_exists]
theorem eventually3_exists {D : Sort _}
    {Ψ : D → FiniteTrace A L1 → FiniteTrace B L2 → FiniteTrace C L3 →
      Seq (L1 × A) → Seq (L2 × B) → Seq (L3 × C) → Prop} :
    (∃ d, Eventually3 (Ψ d) f g h inftr inftrb inftrc) ↔
      Eventually3 (fun f' g' h' inftr' inftrb' inftrc' => ∃ b, Ψ b f' g' h' inftr' inftrb' inftrc')
        f g h inftr inftrb inftrc := by
  simp only [eventually3_take_drop]
  exact ⟨fun ⟨b, n, H, hsl⟩ => ⟨n, ⟨b, H⟩, hsl⟩, fun ⟨n, ⟨b, H⟩, hsl⟩ => ⟨b, n, H, hsl⟩⟩

/-! ### Other properties -/

@[rocq_alias trillium.always3_eventually3_idemp]
theorem Always3.eventually3_idemp :
    Always3 (Eventually3 ψ) f g h inftr inftrb inftrc →
      Always3 (Eventually3 (Always3 (Eventually3 ψ))) f g h inftr inftrb inftrc :=
  fun H => H.idemp.mono fun _ _ _ _ _ _ H => .of_holds H.sameLength.1 H.sameLength.2 H

@[rocq_alias trillium.eventually3_always3_combine]
theorem Eventually3.always3_combine :
    Eventually3 (Always3 ψ1) f g h inftr inftrb inftrc →
      Eventually3 (Always3 ψ2) f g h inftr inftrb inftrc →
      Eventually3 (fun f' g' h' inftr' inftrb' inftrc' =>
        Always3 ψ1 f' g' h' inftr' inftrb' inftrc' ∧ Always3 ψ2 f' g' h' inftr' inftrb' inftrc')
        f g h inftr inftrb inftrc := by
  simp only [eventually3_take_drop]
  rintro ⟨n, hn, hsl⟩ ⟨m, hm, -⟩
  refine ⟨max n m, ⟨?_, ?_⟩, hsl⟩
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.le_max_left n m)
    rw [hk, InfList.take_add, InfList.take_add, InfList.take_add, Seq.dropn_add, Seq.dropn_add, Seq.dropn_add,
      ← appendList_appendList, ← appendList_appendList, ← appendList_appendList]
    exact hn.unroll_n k
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.le_max_right n m)
    rw [hk, InfList.take_add, InfList.take_add, InfList.take_add, Seq.dropn_add, Seq.dropn_add, Seq.dropn_add,
      ← appendList_appendList, ← appendList_appendList, ← appendList_appendList]
    exact hm.unroll_n k

@[rocq_alias trillium.eventually3_and_always3]
theorem Eventually3.and_always3 :
    Eventually3 ψ1 f g h inftr inftrb inftrc → Always3 ψ2 f g h inftr inftrb inftrc →
      Eventually3 (fun f' g' h' inftr' inftrb' inftrc' =>
        ψ1 f' g' h' inftr' inftrb' inftrc' ∧ Always3 ψ2 f' g' h' inftr' inftrb' inftrc')
        f g h inftr inftrb inftrc := by
  intro hev hal
  obtain ⟨n, hn, hsl⟩ := eventually3_take_drop.mp hev
  exact eventually3_take_drop.mpr ⟨n, ⟨hn, hal.unroll_n n⟩, hsl⟩

@[rocq_alias trillium.eventually3_forall_combine]
theorem Eventually3.forall_combine {D : Type _} [Finite D] [Nonempty D]
    {Ψ : D → FiniteTrace A L1 → FiniteTrace B L2 → FiniteTrace C L3 →
      Seq (L1 × A) → Seq (L2 × B) → Seq (L3 × C) → Prop} :
    (∀ c, Eventually3 (Always3 (Ψ c)) f g h inftr inftrb inftrc) →
      Eventually3 (fun f' g' h' inftr' inftrb' inftrc' =>
        ∀ d, Always3 (Ψ d) f' g' h' inftr' inftrb' inftrc') f g h inftr inftrb inftrc := by
  intro Hfa
  obtain ⟨enum, -, Henum⟩ := Finite.exists_univ_list D
  suffices H : Eventually3 (fun f' g' h' inftr' inftrb' inftrc' =>
      ∀ d, d ∈ enum → Always3 (Ψ d) f' g' h' inftr' inftrb' inftrc') f g h inftr inftrb inftrc from
    H.mono fun _ _ _ _ _ _ H d => H d (Henum d)
  clear Henum
  induction enum with
  | nil =>
    obtain ⟨d⟩ := ‹Nonempty D›
    obtain ⟨hsl1, hsl2⟩ := (Hfa d).sameLength
    exact .of_holds hsl1 hsl2 fun _ H => absurd H List.not_mem_nil
  | cons d l IHl =>
    have IHl' : Eventually3 (Always3 fun f' g' h' inftr' inftrb' inftrc' =>
        ∀ d, d ∈ l → Ψ d f' g' h' inftr' inftrb' inftrc') f g h inftr inftrb inftrc := by
      refine (eventually3_and_sameLength.mp IHl).mono ?_
      rintro f' g' h' inftr' inftrb' inftrc' ⟨Hfa', hsl1, hsl2⟩
      exact always3_forall.mp fun c' => (always3_impl hsl1 hsl2).mp (Hfa' c')
    refine (Eventually3.always3_combine (Hfa d) IHl').mono ?_
    rintro f' g' h' inftr' inftrb' inftrc' ⟨Hal1, Hal2⟩ d' hd'
    rcases List.mem_cons.mp hd' with rfl | hd'
    · exact Hal1
    · obtain ⟨hsl1, hsl2⟩ := Hal1.sameLength
      exact (always3_impl hsl1 hsl2).mpr (always3_forall.mpr Hal2 d') hd'

end three

end Trillium
