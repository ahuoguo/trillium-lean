/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Iris.Std.RocqPorting
import Mathlib.Logic.Relation
import Mathlib.Data.List.Induction
import Mathlib.Order.Defs.PartialOrder

/-!
# Finite traces
Port of `trillium/traces/trace.v`.

A finite trace `FiniteTrace A L` is a non-empty sequence of states `A`, consecutive states being
separated by labels `L`; it grows to the right:
`{tr[a]}` is the singleton trace and `ft :tr[ℓ]: a` extends `ft` by the label `ℓ` and state `a`.
These notations (and `ft +trl+ l`) are `scoped` in the `Trillium` namespace, so they are available
inside `namespace Trillium` or after `open Trillium`.

Rocq names → Lean names (in namespace `Trillium.FiniteTrace` unless noted):
`trace_first`/`trace_last` → `first`/`last`, `trace_starts_in`/`trace_ends_in` → `StartsIn`/`EndsIn`,
`trace_append_list` → `appendList` (notation `+trl+`), ``trace_prefix_of`` → `IsPrefix`
(also the `≤` of the `PartialOrder` instance), `trace_length` → `length`, the lookup `ft !! i` →
`ft.lookup i`, `trace_steps` → `Trillium.TraceSteps`, `trace_forall` → `Trillium.TraceForall`, ...

`rtc` is Mathlib's `Relation.ReflTransGen`.
-/

namespace Trillium

/-- Finite (non-empty) traces of states `A` and labels `L`. -/
@[rocq_alias trillium.finite_trace]
inductive FiniteTrace (A : Type _) (L : Type _) where
  /-- The trace consisting of the single state `a` (Rocq `trace_singleton`). -/
  | singleton (a : A)
  /-- `ft` extended by a step with label `ℓ` to state `a` (Rocq `trace_extend`). -/
  | extend (ft : FiniteTrace A L) (ℓ : L) (a : A)
  deriving DecidableEq

attribute [rocq_alias trillium.finite_trace_eq_dec] instDecidableEqFiniteTrace

@[inherit_doc] scoped notation "{tr[" a "]}" => FiniteTrace.singleton a
@[inherit_doc] scoped notation:60 t:60 " :tr[" ℓ "]: " a:61 => FiniteTrace.extend t ℓ a

namespace FiniteTrace

variable {A L : Type _}

/-- The first state of a trace. -/
@[rocq_alias trillium.trace_first, simp]
def first : FiniteTrace A L → A
  | {tr[a]} => a
  | ft :tr[_]: _ => ft.first

/-- The last state of a trace. -/
@[rocq_alias trillium.trace_last, simp]
def last : FiniteTrace A L → A
  | {tr[a]} => a
  | _ :tr[_]: a => a

@[rocq_alias trillium.trace_starts_in]
def StartsIn (ft : FiniteTrace A L) (a : A) : Prop := ft.first = a

@[rocq_alias trillium.trace_ends_in]
def EndsIn (ft : FiniteTrace A L) (a : A) : Prop := ft.last = a

/-- Extend a trace by a list of (label, state) pairs. -/
@[rocq_alias trillium.trace_append_list]
def appendList : FiniteTrace A L → List (L × A) → FiniteTrace A L
  | ft, [] => ft
  | ft, p :: l => appendList (ft :tr[p.1]: p.2) l

end FiniteTrace

/-- `ft +trl+ l` extends the trace `ft` by the list `l` of (label, state) pairs. -/
scoped infixl:60 " +trl+ " => FiniteTrace.appendList

namespace FiniteTrace

variable {A L : Type _}

@[simp] theorem appendList_nil (ft : FiniteTrace A L) : ft +trl+ [] = ft := rfl
@[simp] theorem appendList_cons (ft : FiniteTrace A L) (p : L × A) (l : List (L × A)) :
    ft +trl+ (p :: l) = (ft :tr[p.1]: p.2) +trl+ l := rfl

/-- Rocq ``ft `trace_prefix_of` ft'``. -/
@[rocq_alias trillium.trace_prefix]
def IsPrefix (ft ft' : FiniteTrace A L) : Prop := ∃ l, ft' = ft +trl+ l

/-! ## Instances and properties -/

@[rocq_alias trillium.trace_starts_in_first]
theorem startsIn_first (ft : FiniteTrace A L) : ft.StartsIn ft.first := rfl

@[rocq_alias trillium.trace_ends_in_last]
theorem endsIn_last (ft : FiniteTrace A L) : ft.EndsIn ft.last := rfl

@[rocq_alias trillium.first_eq_trace_starts_in]
theorem StartsIn.first_eq {ft : FiniteTrace A L} {a : A} : ft.StartsIn a → ft.first = a := id

@[rocq_alias trillium.last_eq_trace_ends_in]
theorem EndsIn.last_eq {ft : FiniteTrace A L} {a : A} : ft.EndsIn a → ft.last = a := id

@[simp] theorem startsIn_iff {ft : FiniteTrace A L} {a : A} : ft.StartsIn a ↔ ft.first = a := .rfl
@[simp] theorem endsIn_iff {ft : FiniteTrace A L} {a : A} : ft.EndsIn a ↔ ft.last = a := .rfl

@[rocq_alias trillium.trace_singleton_starts_in]
theorem singleton_startsIn (c : A) : ({tr[c]} : FiniteTrace A L).StartsIn c := rfl

@[rocq_alias trillium.trace_singleton_starts_in_inv]
theorem singleton_startsIn_inv {c c' : A} : ({tr[c']} : FiniteTrace A L).StartsIn c → c' = c := id

@[rocq_alias trillium.trace_singleton_ends_in]
theorem singleton_endsIn (c : A) : ({tr[c]} : FiniteTrace A L).EndsIn c := rfl

@[rocq_alias trillium.trace_singleton_ends_in_inv]
theorem singleton_endsIn_inv {c c' : A} : ({tr[c']} : FiniteTrace A L).EndsIn c → c' = c := id

@[rocq_alias trillium.trace_starts_in_inj]
theorem StartsIn.inj {ft : FiniteTrace A L} {c c' : A} :
    ft.StartsIn c → ft.StartsIn c' → c = c' := fun h h' => h.symm.trans h'

@[rocq_alias trillium.trace_ends_in_inj]
theorem EndsIn.inj {ft : FiniteTrace A L} {c c' : A} :
    ft.EndsIn c → ft.EndsIn c' → c = c' := fun h h' => h.symm.trans h'

/-- `ft` is `ft'` extended by one step with label `ℓ` (Rocq `trace_contract`). -/
@[rocq_alias trillium.trace_contract]
def Contract (ft : FiniteTrace A L) (ℓ : L) (ft' : FiniteTrace A L) : Prop :=
  ∃ a, ft = ft' :tr[ℓ]: a

@[rocq_alias trillium.trace_contract_of_extend]
theorem contract_extend {ft : FiniteTrace A L} {ℓ : L} {a : A} {ft' : FiniteTrace A L} {ℓ' : L} :
    (ft :tr[ℓ]: a).Contract ℓ' ft' → ft' = ft ∧ ℓ = ℓ' := by
  rintro ⟨_, h⟩
  cases h
  exact ⟨rfl, rfl⟩

@[rocq_alias trillium.not_trace_contract_singleton]
theorem not_contract_singleton (a : A) (ft : FiniteTrace A L) (ℓ : L) :
    ¬ ({tr[a]} : FiniteTrace A L).Contract ℓ ft := by
  rintro ⟨_, h⟩
  cases h

@[rocq_alias trillium.trace_extend_starts_in]
theorem StartsIn.extend {ft : FiniteTrace A L} {a' : A} (ℓ : L) (a : A) :
    ft.StartsIn a' → (ft :tr[ℓ]: a).StartsIn a' := id

@[rocq_alias trillium.trace_extend_starts_in_inv]
theorem StartsIn.of_extend {ft : FiniteTrace A L} {a' : A} {ℓ : L} {a : A} :
    (ft :tr[ℓ]: a).StartsIn a' → ft.StartsIn a' := id

@[rocq_alias trillium.trace_extend_ends_in]
theorem extend_endsIn (ft : FiniteTrace A L) (c : A) (ℓ : L) : (ft :tr[ℓ]: c).EndsIn c := rfl

@[rocq_alias trillium.trace_does_end_in]
theorem exists_endsIn (ft : FiniteTrace A L) : ∃ a, ft.EndsIn a := ⟨_, rfl⟩

@[rocq_alias trillium.trace_extend_neq_singleton]
theorem extend_ne_singleton (ft : FiniteTrace A L) (a a' : A) (ℓ : L) :
    (ft :tr[ℓ]: a) ≠ {tr[a']} := nofun

@[rocq_alias trillium.trace_prefix_append]
theorem IsPrefix.exists_appendList {ft ft' : FiniteTrace A L} :
    ft.IsPrefix ft' → ∃ l, ft' = ft +trl+ l := id

@[rocq_alias trillium.trace_append_list_assoc, simp]
theorem appendList_appendList (ft : FiniteTrace A L) (l l' : List (L × A)) :
    (ft +trl+ l) +trl+ l' = ft +trl+ (l ++ l') := by
  induction l generalizing ft with
  | nil => rfl
  | cons p l IH => exact IH _

@[rocq_alias trillium.trace_appned_list_eq_singleton_inv]
theorem appendList_eq_singleton_inv {ft : FiniteTrace A L} {l : List (L × A)} {a : A} :
    ft +trl+ l = {tr[a]} → ft = {tr[a]} ∧ l = [] := by
  induction l generalizing ft with
  | nil => exact fun h => ⟨h, rfl⟩
  | cons p l IH =>
    intro h
    obtain ⟨h, -⟩ := IH h
    cases h

@[rocq_alias trillium.trace_append_list_snoc]
theorem appendList_concat (ft : FiniteTrace A L) (l : List (L × A)) (ℓ : L) (a : A) :
    ft +trl+ (l ++ [(ℓ, a)]) = (ft +trl+ l) :tr[ℓ]: a := by
  rw [← appendList_appendList]; rfl

@[rocq_alias trillium.trace_extend_eq_trace_append_list]
theorem extend_eq_appendList {ft ft' : FiniteTrace A L} {l : List (L × A)} {ℓ : L} {a : A} :
    (ft :tr[ℓ]: a) = ft' +trl+ l → (ft' = ft :tr[ℓ]: a ∧ l = []) ∨ ∃ l', l = l' ++ [(ℓ, a)] := by
  intro h
  rcases List.eq_nil_or_concat l with rfl | ⟨l', p, rfl⟩
  · exact .inl ⟨h.symm, rfl⟩
  · rw [List.concat_eq_append, show p = (p.1, p.2) from rfl, appendList_concat] at h
    cases h
    exact .inr ⟨l', by simp⟩

/-- The length (number of states) of a trace (Rocq `trace_length`). -/
@[rocq_alias trillium.trace_length, simp]
def length : FiniteTrace A L → Nat
  | {tr[_]} => 1
  | ft' :tr[_]: _ => ft'.length + 1

@[simp] theorem length_appendList (ft : FiniteTrace A L) (l : List (L × A)) :
    (ft +trl+ l).length = ft.length + l.length := by
  induction l generalizing ft with
  | nil => rfl
  | cons p l IH => simp [IH]; omega

@[rocq_alias trillium.trace_append_list_eq_self_inv]
theorem eq_appendList_self_inv {ft : FiniteTrace A L} {l : List (L × A)} :
    ft = ft +trl+ l → l = [] := by
  intro h
  have := congrArg length h
  simp at this
  exact this

@[rocq_alias trillium.trace_prefix_antisym]
theorem IsPrefix.antisymm {ft ft' : FiniteTrace A L} :
    ft.IsPrefix ft' → ft'.IsPrefix ft → ft = ft' := by
  rintro ⟨l, rfl⟩ ⟨l', h⟩
  rw [appendList_appendList] at h
  obtain h' := List.append_eq_nil_iff.mp (eq_appendList_self_inv h)
  rw [h'.1]; rfl

@[refl] theorem IsPrefix.refl (ft : FiniteTrace A L) : ft.IsPrefix ft := ⟨[], rfl⟩

theorem IsPrefix.trans {ft ft' ft'' : FiniteTrace A L} :
    ft.IsPrefix ft' → ft'.IsPrefix ft'' → ft.IsPrefix ft'' := by
  rintro ⟨l, rfl⟩ ⟨l', rfl⟩
  exact ⟨l ++ l', appendList_appendList _ _ _⟩

/-- The prefix order on traces (Rocq `trace_prefix_equivalence : PartialOrder trace_prefix`). -/
@[rocq_alias trillium.trace_prefix_equivalence]
instance instPartialOrder : PartialOrder (FiniteTrace A L) where
  le := IsPrefix
  le_refl := IsPrefix.refl
  le_trans _ _ _ := IsPrefix.trans
  le_antisymm _ _ := IsPrefix.antisymm

@[simp] theorem le_iff_isPrefix {ft ft' : FiniteTrace A L} : ft ≤ ft' ↔ ft.IsPrefix ft' := .rfl

@[rocq_alias trillium.trace_append_list_first, simp]
theorem first_appendList (ft : FiniteTrace A L) (l : List (L × A)) :
    (ft +trl+ l).first = ft.first := by
  induction l generalizing ft with
  | nil => rfl
  | cons p l IH => exact IH _

@[rocq_alias trillium.trace_prefix_eq_firsts]
theorem IsPrefix.first_eq {ft ft' : FiniteTrace A L} : ft.IsPrefix ft' → ft.first = ft'.first := by
  rintro ⟨l, rfl⟩
  rw [first_appendList]

@[rocq_alias trillium.trace_prefix_trace_append]
theorem IsPrefix.appendList_right {ft ft' : FiniteTrace A L} (l : List (L × A)) :
    ft.IsPrefix ft' → ft.IsPrefix (ft' +trl+ l) := by
  rintro ⟨l', rfl⟩
  exact ⟨l' ++ l, appendList_appendList _ _ _⟩

@[rocq_alias trillium.trace_prefix_trace_extend]
theorem IsPrefix.extend_right {ft ft' : FiniteTrace A L} (ℓ : L) (a : A) :
    ft.IsPrefix ft' → ft.IsPrefix (ft' :tr[ℓ]: a) := by
  rintro ⟨l, rfl⟩
  exact ⟨l ++ [(ℓ, a)], (appendList_concat _ _ _ _).symm⟩

@[rocq_alias trillium.trace_prefix_of_singleton]
theorem singleton_isPrefix {ft : FiniteTrace A L} {a : A} :
    ft.StartsIn a → ({tr[a]} : FiniteTrace A L).IsPrefix ft := by
  induction ft with
  | singleton b => rintro rfl; exact .refl _
  | extend ft ℓ b IH => exact fun h => (IH h.of_extend).extend_right ℓ b

@[rocq_alias trillium.trace_append_prefix]
theorem IsPrefix.of_appendList_left {ft ft' : FiniteTrace A L} {l : List (L × A)} :
    (ft +trl+ l).IsPrefix ft' → ft.IsPrefix ft' := by
  rintro ⟨l', rfl⟩
  exact ⟨l ++ l', appendList_appendList _ _ _⟩

@[rocq_alias trillium.trace_extend_prefix]
theorem IsPrefix.of_extend_left {ft ft' : FiniteTrace A L} {ℓ : L} {a : A} :
    (ft :tr[ℓ]: a).IsPrefix ft' → ft.IsPrefix ft' := by
  rintro ⟨l, rfl⟩
  exact ⟨(ℓ, a) :: l, rfl⟩

@[rocq_alias trillium.trace_prefix_of_singleton_inv]
theorem isPrefix_singleton_inv {ft : FiniteTrace A L} {a : A} :
    ft.IsPrefix {tr[a]} → ft = {tr[a]} :=
  fun ⟨_, h⟩ => (appendList_eq_singleton_inv h.symm).1

@[rocq_alias trillium.trace_prefix_of_extend]
theorem isPrefix_extend_inv {ft ft' : FiniteTrace A L} {ℓ : L} {a : A} :
    ft.IsPrefix (ft' :tr[ℓ]: a) → ft = (ft' :tr[ℓ]: a) ∨ ft.IsPrefix ft' := by
  rintro ⟨l, hl⟩
  rcases extend_eq_appendList hl with ⟨h, -⟩ | ⟨l', rfl⟩
  · exact .inl h
  · rw [appendList_concat] at hl
    cases hl
    exact .inr ⟨l', rfl⟩

/-- Decidability of the prefix relation (Rocq `trace_prefix_dec`). -/
@[rocq_alias trillium.trace_prefix_dec]
instance decIsPrefix [DecidableEq A] [DecidableEq L] :
    ∀ ft ft' : FiniteTrace A L, Decidable (ft.IsPrefix ft')
  | ft, {tr[a']} =>
    if h : ft = {tr[a']} then isTrue (h ▸ .refl _)
    else isFalse fun hp => h (isPrefix_singleton_inv hp)
  | ft, ft' :tr[ℓ']: a' =>
    match decIsPrefix ft ft' with
    | isTrue h => isTrue (h.extend_right ℓ' a')
    | isFalse hn =>
      if h : ft = (ft' :tr[ℓ']: a') then isTrue (h ▸ .refl _)
      else isFalse fun hp => (isPrefix_extend_inv hp).elim h hn

@[rocq_alias trillium.trace_prefixes_related]
theorem isPrefix_total_of_isPrefix {ft ft' ft'' : FiniteTrace A L} :
    ft.IsPrefix ft'' → ft'.IsPrefix ft'' → ft.IsPrefix ft' ∨ ft'.IsPrefix ft := by
  rintro ⟨l, rfl⟩ ⟨l', hl'⟩
  induction l generalizing ft ft' l' with
  | nil => exact .inr ⟨l', hl'⟩
  | cons p l IH =>
    rcases IH (ft := ft :tr[p.1]: p.2) l' hl' with hpf | hpf
    · exact .inl hpf.of_extend_left
    · rcases isPrefix_extend_inv hpf with rfl | hpf
      · exact .inl ((IsPrefix.refl _).extend_right _ _)
      · exact .inr hpf

@[rocq_alias trillium.trace_last_of_append_list]
theorem last_appendList_eq_getElem? (ft : FiniteTrace A L) (l : List (L × A)) (oζ : L) :
    ∃ oζ', ((oζ, ft.last) :: l)[l.length]? = some (oζ', (ft +trl+ l).last) := by
  induction l generalizing ft oζ with
  | nil => exact ⟨oζ, rfl⟩
  | cons p l IH =>
    obtain ⟨oζ', h⟩ := IH (ft :tr[p.1]: p.2) p.1
    exact ⟨oζ', by simpa using h⟩

@[rocq_alias trillium.trace_last_of_append_list_map]
theorem last_appendList_eq_getElem?_map (ft : FiniteTrace A L) (l : List (L × A)) :
    (ft.last :: l.map Prod.snd)[l.length]? = some (ft +trl+ l).last := by
  induction l generalizing ft with
  | nil => rfl
  | cons p l IH => simpa using IH (ft :tr[p.1]: p.2)

@[rocq_alias trillium.trace_append_list_inj2]
theorem appendList_inj {ft : FiniteTrace A L} {l l' : List (L × A)} :
    ft +trl+ l = ft +trl+ l' → l = l' := by
  induction l using List.reverseRecOn generalizing l' with
  | nil => exact fun h => (eq_appendList_self_inv h).symm
  | append_singleton l p IH =>
    intro h
    rcases List.eq_nil_or_concat l' with rfl | ⟨l', q, rfl⟩
    · exact eq_appendList_self_inv h.symm
    · rw [List.concat_eq_append] at h ⊢
      rw [show p = (p.1, p.2) from rfl, show q = (q.1, q.2) from rfl,
        appendList_concat, appendList_concat] at h
      injection h with h1 h2 h3
      rw [IH h1, show p = (p.1, p.2) from rfl, show q = (q.1, q.2) from rfl, h2, h3]

/-! ## Lookup -/

/-- Lookup of the `i`-th state of a trace (Rocq's `Lookup nat A (finite_trace A L)` instance,
`ft !! i`). -/
@[rocq_alias trillium.trace_lookup]
def lookup : FiniteTrace A L → Nat → Option A
  | {tr[a]}, 0 => some a
  | {tr[_]}, _ + 1 => none
  | ft' :tr[_]: a, n => if ft'.length = n then some a else ft'.lookup n

@[simp] theorem lookup_singleton_zero (a : A) : ({tr[a]} : FiniteTrace A L).lookup 0 = some a := rfl
@[simp] theorem lookup_singleton_succ (a : A) (n : Nat) :
    ({tr[a]} : FiniteTrace A L).lookup (n + 1) = none := rfl
theorem lookup_extend (ft : FiniteTrace A L) (ℓ : L) (a : A) (n : Nat) :
    (ft :tr[ℓ]: a).lookup n = if ft.length = n then some a else ft.lookup n := rfl

@[rocq_alias trillium.trace_lookup_lt_Some]
theorem isSome_lookup_iff (ft : FiniteTrace A L) (i : Nat) :
    (ft.lookup i).isSome ↔ i < ft.length := by
  induction ft generalizing i with
  | singleton a => cases i <;> simp
  | extend ft ℓ a IH =>
    rw [lookup_extend]
    split
    · simp; omega
    · rw [IH]; simp; omega

@[rocq_alias trillium.trace_length_at_least]
theorem one_le_length (ft : FiniteTrace A L) : 1 ≤ ft.length := by
  cases ft <;> simp

@[rocq_alias trillium.trace_lookup_lt_Some_1]
theorem lt_length_of_lookup_eq_some {ft : FiniteTrace A L} {i : Nat} {a : A} :
    ft.lookup i = some a → i < ft.length := fun h => (isSome_lookup_iff ft i).mp (by simp [h])

@[rocq_alias trillium.trace_lookup_lt_Some_2]
theorem isSome_lookup_of_lt {ft : FiniteTrace A L} {i : Nat} :
    i < ft.length → (ft.lookup i).isSome := (isSome_lookup_iff ft i).mpr

@[rocq_alias trillium.trace_lookup_extend]
theorem lookup_extend_of_eq {ft : FiniteTrace A L} {a : A} {i : Nat} (ℓ : L) :
    i = ft.length → (ft :tr[ℓ]: a).lookup i = some a := by
  rintro rfl; simp [lookup_extend]

@[rocq_alias trillium.trace_lookup_extend_lt]
theorem lookup_extend_of_lt {ft : FiniteTrace A L} {a : A} {i : Nat} (ℓ : L) :
    i < ft.length → (ft :tr[ℓ]: a).lookup i = ft.lookup i := by
  intro h; have : ft.length ≠ i := by omega
  simp [lookup_extend, this]

@[rocq_alias trillium.trace_lookup_singelton]
theorem lookup_singleton_eq_some_iff (a : A) (i : Nat) :
    ({tr[a]} : FiniteTrace A L).lookup i = some a ↔ i = 0 := by
  cases i <;> simp

@[rocq_alias trillium.trace_lookup_singelton_1]
theorem lookup_singleton_eq_some {a : A} {i : Nat} {b : A} :
    ({tr[a]} : FiniteTrace A L).lookup i = some b → i = 0 ∧ b = a := by
  cases i <;> simp [eq_comm]

@[rocq_alias trillium.trace_lookup_singelton_2]
theorem lookup_singleton (a : A) : ({tr[a]} : FiniteTrace A L).lookup 0 = some a := rfl

@[rocq_alias trillium.trace_lookup_first, simp]
theorem lookup_zero (ft : FiniteTrace A L) : ft.lookup 0 = some ft.first := by
  induction ft with
  | singleton a => rfl
  | extend ft ℓ a IH =>
    have := one_le_length ft
    have : ft.length ≠ 0 := by omega
    simp [lookup_extend, this, IH]

@[rocq_alias trillium.trace_lookup_last]
theorem lookup_eq_last {ft : FiniteTrace A L} {i : Nat} :
    i + 1 = ft.length → ft.lookup i = some ft.last := by
  cases ft with
  | singleton a => intro h; simp at h; subst h; rfl
  | extend ft ℓ a => intro h; simp at h; subst h; simp [lookup_extend]

@[rocq_alias trillium.trace_lookup_append_list]
theorem lookup_appendList {ft : FiniteTrace A L} (l : List (L × A)) {i : Nat} :
    i < ft.length → (ft +trl+ l).lookup i = ft.lookup i := by
  induction l generalizing ft with
  | nil => intro; rfl
  | cons p l IH =>
    intro h
    rw [appendList_cons, IH (by simp; omega), lookup_extend_of_lt _ h]

@[rocq_alias trillium.trace_lookup_append_list_inv]
theorem exists_appendList_of_lookup {ft : FiniteTrace A L} {i : Nat} {a : A} :
    ft.lookup i = some a → ∃ ft' l, ft = ft' +trl+ l ∧ i + 1 = ft'.length := by
  induction ft generalizing i a with
  | singleton b =>
    intro h
    obtain ⟨rfl, rfl⟩ := lookup_singleton_eq_some h
    exact ⟨{tr[a]}, [], rfl, rfl⟩
  | extend ft ℓ b IH =>
    intro h
    by_cases hi : i = ft.length
    · exact ⟨ft :tr[ℓ]: b, [], rfl, by simp [hi]⟩
    · have hlt := lt_length_of_lookup_eq_some h
      simp at hlt
      rw [lookup_extend_of_lt _ (by omega)] at h
      obtain ⟨ft', l, rfl, hl⟩ := IH h
      exact ⟨ft', l ++ [(ℓ, b)], (appendList_concat _ _ _ _).symm, hl⟩

end FiniteTrace

open FiniteTrace

/-! ## Traces following a step relation -/

/-- Every step of the trace is an `R`-step (Rocq `trace_steps`). -/
@[rocq_alias trillium.trace_steps]
inductive TraceSteps {A L : Type _} (R : A → L → A → Prop) : FiniteTrace A L → Prop
  | singleton x : TraceSteps R {tr[x]}
  | step ex x ℓ y : ex.EndsIn x → R x ℓ y → TraceSteps R ex → TraceSteps R (ex :tr[ℓ]: y)

/-- Every step of the two traces is a (joint) `R`-step (Rocq `trace_steps2`). -/
@[rocq_alias trillium.trace_steps2]
inductive TraceSteps2 {A B L1 L2 : Type _} (R : A → B → L1 → L2 → A → B → Prop) :
    FiniteTrace A L1 → FiniteTrace B L2 → Prop
  | singleton x y : TraceSteps2 R {tr[x]} {tr[y]}
  | step ex1 ex2 x1 y1 ℓ1 ℓ2 x2 y2 :
    ex1.EndsIn x1 → ex2.EndsIn y1 → R x1 y1 ℓ1 ℓ2 x2 y2 → TraceSteps2 R ex1 ex2 →
    TraceSteps2 R (ex1 :tr[ℓ1]: x2) (ex2 :tr[ℓ2]: y2)

namespace TraceSteps

variable {A L : Type _} {R : A → L → A → Prop}

@[rocq_alias trillium.trace_steps_step_inv]
theorem step_inv {ex : FiniteTrace A L} {ℓ : L} {x : A} :
    TraceSteps R (ex :tr[ℓ]: x) → TraceSteps R ex ∧ ∃ y, ex.EndsIn y ∧ R y ℓ x := by
  rintro (_ | ⟨_, y, _, _, h1, h2, h3⟩)
  exact ⟨h3, y, h1, h2⟩

@[rocq_alias trillium.trace_steps_impl]
theorem impl {R' : A → L → A → Prop} (HR : ∀ x ℓ y, R x ℓ y → R' x ℓ y) :
    ∀ ex, TraceSteps R ex → TraceSteps R' ex := by
  intro ex Hex
  induction Hex with
  | singleton x => exact .singleton x
  | step ex x ℓ y h1 h2 _ IH => exact .step ex x ℓ y h1 (HR _ _ _ h2) IH

@[rocq_alias trillium.trace_steps_rtc]
theorem rtc_iff (x y : A) :
    Relation.ReflTransGen (fun x y => ∃ ℓ, R x ℓ y) x y ↔
      ∃ ex, TraceSteps R ex ∧ ex.StartsIn x ∧ ex.EndsIn y := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨{tr[x]}, .singleton x, rfl, rfl⟩
    | tail _ hst IH =>
      obtain ⟨ℓ, hst⟩ := hst
      obtain ⟨ex, hex, h1, h2⟩ := IH
      exact ⟨ex :tr[ℓ]: _, .step _ _ _ _ h2 hst hex, h1, rfl⟩
  · rintro ⟨ex, hex, h1, h2⟩
    induction hex generalizing x y with
    | singleton z => cases h1; cases h2; exact .refl
    | step ex z ℓ w hz hR _ IH =>
      cases h2
      exact .tail (IH x z h1 hz) ⟨ℓ, hR⟩

@[rocq_alias trillium.trace_steps_rtc_1]
theorem exists_of_rtc {x y : A} (h : Relation.ReflTransGen (fun x y => ∃ ℓ, R x ℓ y) x y) :
    ∃ ex, TraceSteps R ex ∧ ex.StartsIn x ∧ ex.EndsIn y := (rtc_iff x y).mp h

@[rocq_alias trillium.trace_steps_rtc_2]
theorem rtc {ex : FiniteTrace A L} (h : TraceSteps R ex) :
    Relation.ReflTransGen (fun x y => ∃ ℓ, R x ℓ y) ex.first ex.last :=
  (rtc_iff _ _).mpr ⟨ex, h, rfl, rfl⟩

@[rocq_alias trillium.trace_steps_append_list_inv]
theorem of_appendList {ft : FiniteTrace A L} {l : List (L × A)} :
    TraceSteps R (ft +trl+ l) → TraceSteps R ft := by
  induction l using List.reverseRecOn with
  | nil => exact id
  | append_singleton l p IH =>
    rw [show p = (p.1, p.2) from rfl, appendList_concat]
    exact fun h => IH h.step_inv.1

/-! ### Binary (label-ignoring) step relations -/

section binary

variable {R : A → A → Prop}

@[rocq_alias trillium.trace_steps_step_inv_bin]
theorem step_inv_bin {ex : FiniteTrace A L} {x : A} {ℓ : L} :
    TraceSteps (fun x (_ : L) y => R x y) (ex :tr[ℓ]: x) →
      TraceSteps (fun x (_ : L) y => R x y) ex ∧ ∃ y, ex.EndsIn y ∧ R y x :=
  step_inv

@[rocq_alias trillium.trace_steps_impl_bin]
theorem impl_bin {R' : A → A → Prop} (HR : ∀ x y, R x y → R' x y) :
    ∀ ex : FiniteTrace A L, TraceSteps (fun x _ y => R x y) ex → TraceSteps (fun x _ y => R' x y) ex :=
  impl fun x _ y => HR x y

@[rocq_alias trillium.trace_steps_rtc_bin]
theorem rtc_iff_bin [Inhabited L] (x y : A) :
    Relation.ReflTransGen R x y ↔
      ∃ ex : FiniteTrace A L, TraceSteps (fun x _ y => R x y) ex ∧ ex.StartsIn x ∧ ex.EndsIn y := by
  rw [← rtc_iff]
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hst IH => exact IH.tail ⟨default, hst⟩
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hst IH => exact IH.tail hst.choose_spec

@[rocq_alias trillium.trace_steps_rtc_1_bin]
theorem exists_of_rtc_bin [Inhabited L] {x y : A} (h : Relation.ReflTransGen R x y) :
    ∃ ex : FiniteTrace A L, TraceSteps (fun x _ y => R x y) ex ∧ ex.StartsIn x ∧ ex.EndsIn y :=
  (rtc_iff_bin x y).mp h

@[rocq_alias trillium.trace_steps_rtc_2_bin]
theorem rtc_bin [Inhabited L] {ex : FiniteTrace A L} (h : TraceSteps (fun x _ y => R x y) ex) :
    Relation.ReflTransGen R ex.first ex.last :=
  (rtc_iff_bin _ _).mpr ⟨ex, h, rfl, rfl⟩

@[rocq_alias trillium.trace_append_list_steps_rtc_bin]
theorem appendList_rtc_bin {x y : A} {ex : FiniteTrace A L} {l : List (L × A)} :
    ex.EndsIn x → (ex +trl+ l).EndsIn y → TraceSteps (fun x _ y => R x y) (ex +trl+ l) →
      Relation.ReflTransGen R x y := by
  induction l using List.reverseRecOn generalizing y with
  | nil => intro hx hy _; rw [EndsIn.inj hx hy]
  | append_singleton l p IH =>
    rw [show p = (p.1, p.2) from rfl, appendList_concat]
    intro hx hy hts
    obtain ⟨hts1, z, hts2, hz⟩ := hts.step_inv
    cases hy
    exact .tail (IH hx hts2 hts1) hz

end binary

/-! ### Step relations without labels (`L = unit`) -/

section noLabels

variable {R : A → A → Prop}

@[rocq_alias trillium.trace_steps_step_inv_nl]
theorem step_inv_nl {ex : FiniteTrace A Unit} {ℓ : Unit} {x : A} :
    TraceSteps (fun x _ y => R x y) (ex :tr[ℓ]: x) →
      TraceSteps (fun x _ y => R x y) ex ∧ ∃ y, ex.EndsIn y ∧ R y x :=
  step_inv

@[rocq_alias trillium.trace_steps_impl_nl]
theorem impl_nl {R' : A → A → Prop} (HR : ∀ x y, R x y → R' x y) :
    ∀ ex : FiniteTrace A Unit,
      TraceSteps (fun x _ y => R x y) ex → TraceSteps (fun x _ y => R' x y) ex :=
  impl fun x _ y => HR x y

@[rocq_alias trillium.trace_steps_rtc_nl]
theorem rtc_iff_nl (x y : A) :
    Relation.ReflTransGen R x y ↔
      ∃ ex : FiniteTrace A Unit,
        TraceSteps (fun x _ y => R x y) ex ∧ ex.StartsIn x ∧ ex.EndsIn y :=
  rtc_iff_bin x y

@[rocq_alias trillium.trace_steps_rtc_1_nl]
theorem exists_of_rtc_nl {x y : A} (h : Relation.ReflTransGen R x y) :
    ∃ ex : FiniteTrace A Unit, TraceSteps (fun x _ y => R x y) ex ∧ ex.StartsIn x ∧ ex.EndsIn y :=
  (rtc_iff_nl x y).mp h

@[rocq_alias trillium.trace_steps_rtc_2_nl]
theorem rtc_nl {ex : FiniteTrace A Unit} (h : TraceSteps (fun x _ y => R x y) ex) :
    Relation.ReflTransGen R ex.first ex.last :=
  (rtc_iff_nl _ _).mpr ⟨ex, h, rfl, rfl⟩

@[rocq_alias trillium.trace_append_list_steps_rtc_nl]
theorem appendList_rtc_nl {x y : A} {ex : FiniteTrace A Unit} {l : List (Unit × A)} :
    ex.EndsIn x → (ex +trl+ l).EndsIn y → TraceSteps (fun x _ y => R x y) (ex +trl+ l) →
      Relation.ReflTransGen R x y :=
  appendList_rtc_bin

end noLabels

@[rocq_alias trillium.trace_steps_lookup]
theorem lookup_rtc {R : A → A → Prop} {ft : FiniteTrace A L}
    (Hft : TraceSteps (fun x _ y => R x y) ft) :
    ∀ i j a b, i ≤ j → ft.lookup i = some a → ft.lookup j = some b → Relation.ReflTransGen R a b := by
  intro i j a b hij ha hb
  obtain ⟨ft', l, rfl, hj⟩ := exists_appendList_of_lookup hb
  rw [lookup_appendList _ (by omega)] at hb ha
  have Hft' := Hft.of_appendList
  obtain ⟨ft'', l', rfl, hi⟩ := exists_appendList_of_lookup ha
  rw [lookup_appendList _ (by omega)] at ha
  rw [lookup_eq_last hi] at ha
  rw [lookup_eq_last hj] at hb
  cases ha; cases hb
  exact appendList_rtc_bin (endsIn_last _) (endsIn_last _) Hft'

end TraceSteps

namespace TraceSteps2

variable {A B L1 L2 : Type _} {R : A → B → L1 → L2 → A → B → Prop}

@[rocq_alias trillium.trace_steps2_step_inv]
theorem step_inv {ex1 : FiniteTrace A L1} {x : A} {ex2 : FiniteTrace B L2} {y : B} {ℓ1 : L1}
    {ℓ2 : L2} :
    TraceSteps2 R (ex1 :tr[ℓ1]: x) (ex2 :tr[ℓ2]: y) →
      TraceSteps2 R ex1 ex2 ∧ ∃ x' y', ex1.EndsIn x' ∧ ex2.EndsIn y' ∧ R x' y' ℓ1 ℓ2 x y := by
  rintro (_ | ⟨_, _, x', y', _, _, _, _, h1, h2, h3, h4⟩)
  exact ⟨h4, x', y', h1, h2, h3⟩

@[rocq_alias trillium.trace_steps2_impl]
theorem impl {R' : A → B → L1 → L2 → A → B → Prop}
    (HR : ∀ x1 y1 ℓ1 ℓ2 x2 y2, R x1 y1 ℓ1 ℓ2 x2 y2 → R' x1 y1 ℓ1 ℓ2 x2 y2) :
    ∀ ex ex', TraceSteps2 R ex ex' → TraceSteps2 R' ex ex' := by
  intro ex ex' Hex
  induction Hex with
  | singleton x y => exact .singleton x y
  | step _ _ _ _ _ _ _ _ h1 h2 h3 _ IH => exact .step _ _ _ _ _ _ _ _ h1 h2 (HR _ _ _ _ _ _ h3) IH

@[rocq_alias trillium.trace.trace_steps2_trace_steps]
theorem traceSteps {R1 : A → L1 → A → Prop} {R2 : B → L2 → B → Prop}
    (HR : ∀ x1 y1 ℓ1 ℓ2 x2 y2, R x1 y1 ℓ1 ℓ2 x2 y2 → R1 x1 ℓ1 x2 ∧ R2 y1 ℓ2 y2) :
    ∀ ex ex', TraceSteps2 R ex ex' → TraceSteps R1 ex ∧ TraceSteps R2 ex' := by
  intro ex ex' Hexs
  induction Hexs with
  | singleton x y => exact ⟨.singleton x, .singleton y⟩
  | step _ _ _ _ _ _ _ _ h1 h2 h3 _ IH =>
    obtain ⟨r1, r2⟩ := HR _ _ _ _ _ _ h3
    exact ⟨.step _ _ _ _ h1 r1 IH.1, .step _ _ _ _ h2 r2 IH.2⟩

end TraceSteps2

/-! ## Pointwise predicates on traces -/

/-- Every state of the trace satisfies `P` (Rocq `trace_forall`). -/
@[rocq_alias trillium.trace_forall]
inductive TraceForall {A L : Type _} (P : A → Prop) : FiniteTrace A L → Prop
  | singleton a : P a → TraceForall P {tr[a]}
  | extend tr a ℓ : TraceForall P tr → P a → TraceForall P (tr :tr[ℓ]: a)

namespace TraceForall

variable {A L : Type _} {P : A → Prop}

@[rocq_alias trillium.trace_forall_last]
theorem last {tr : FiniteTrace A L} : TraceForall P tr → P tr.last := by
  rintro (⟨_, h⟩ | ⟨_, _, _, _, h⟩) <;> exact h

@[rocq_alias trillium.trace_forall_first]
theorem first {tr : FiniteTrace A L} : TraceForall P tr → P tr.first := by
  intro h
  induction h with
  | singleton _ h => exact h
  | extend _ _ _ _ _ IH => exact IH

@[rocq_alias trillium.trace_forall_extend_inv]
theorem extend_inv {tr : FiniteTrace A L} {a : A} {ℓ : L} :
    TraceForall P (tr :tr[ℓ]: a) → TraceForall P tr ∧ P a := by
  rintro (_ | ⟨_, _, _, h1, h2⟩)
  exact ⟨h1, h2⟩

end TraceForall

/-- The states of the two traces are pointwise related by `P` (Rocq `trace_forall2`). -/
@[rocq_alias trillium.trace_forall2]
inductive TraceForall2 {A B L1 L2 : Type _} (P : A → B → Prop) :
    FiniteTrace A L1 → FiniteTrace B L2 → Prop
  | singleton a b : P a b → TraceForall2 P {tr[a]} {tr[b]}
  | extend tr tr' a b ℓ1 ℓ2 :
    TraceForall2 P tr tr' → P a b → TraceForall2 P (tr :tr[ℓ1]: a) (tr' :tr[ℓ2]: b)

namespace TraceForall2

variable {A B L1 L2 : Type _} {P : A → B → Prop}

@[rocq_alias trillium.trace_forall2_impl]
theorem impl {Q : A → B → Prop} {tr : FiniteTrace A L1} {tr' : FiniteTrace B L2}
    (HPQ : ∀ x y, P x y → Q x y) : TraceForall2 P tr tr' → TraceForall2 Q tr tr' := by
  intro h
  induction h with
  | singleton a b h => exact .singleton a b (HPQ _ _ h)
  | extend _ _ _ _ _ _ _ h IH => exact .extend _ _ _ _ _ _ IH (HPQ _ _ h)

@[rocq_alias trillium.trace_forall2_last]
theorem last {tr : FiniteTrace A L1} {tr' : FiniteTrace B L2} :
    TraceForall2 P tr tr' → P tr.last tr'.last := by
  rintro (⟨_, _, h⟩ | ⟨_, _, _, _, _, _, _, h⟩) <;> exact h

@[rocq_alias trillium.trace_forall2_first]
theorem first {tr : FiniteTrace A L1} {tr' : FiniteTrace B L2} :
    TraceForall2 P tr tr' → P tr.first tr'.first := by
  intro h
  induction h with
  | singleton _ _ h => exact h
  | extend _ _ _ _ _ _ _ _ IH => exact IH

@[rocq_alias trillium.trace_forall2_singleton_inv]
theorem singleton_inv {a : A} {b : B} :
    TraceForall2 (L1 := L1) (L2 := L2) P {tr[a]} {tr[b]} → P a b := by
  rintro ⟨_, _, h⟩; exact h

@[rocq_alias trillium.trace_forall2_singleton_inv_l]
theorem singleton_inv_l {tr' : FiniteTrace B L2} {a : A} :
    TraceForall2 (L1 := L1) P {tr[a]} tr' → ∃ b, tr' = {tr[b]} ∧ P a b := by
  rintro ⟨_, b, h⟩; exact ⟨b, rfl, h⟩

@[rocq_alias trillium.trace_forall2_singleton_inv_r]
theorem singleton_inv_r {tr : FiniteTrace A L1} {b : B} :
    TraceForall2 (L2 := L2) P tr {tr[b]} → ∃ a, tr = {tr[a]} ∧ P a b := by
  rintro ⟨a, _, h⟩; exact ⟨a, rfl, h⟩

@[rocq_alias trillium.trace_forall2_extend_inv]
theorem extend_inv {tr : FiniteTrace A L1} {tr' : FiniteTrace B L2} {a : A} {b : B} {ℓ1 : L1}
    {ℓ2 : L2} : TraceForall2 P (tr :tr[ℓ1]: a) (tr' :tr[ℓ2]: b) → TraceForall2 P tr tr' ∧ P a b := by
  rintro (_ | ⟨_, _, _, _, _, _, h1, h2⟩); exact ⟨h1, h2⟩

@[rocq_alias trillium.trace_forall2_extend_inv_l]
theorem extend_inv_l {tr : FiniteTrace A L1} {tr' : FiniteTrace B L2} {a : A} {ℓ1 : L1} :
    TraceForall2 P (tr :tr[ℓ1]: a) tr' →
      ∃ b tr'' ℓ2, tr' = (tr'' :tr[ℓ2]: b) ∧ TraceForall2 P tr tr'' ∧ P a b := by
  rintro (_ | ⟨_, tr'', _, b, _, ℓ2, h1, h2⟩); exact ⟨b, tr'', ℓ2, rfl, h1, h2⟩

@[rocq_alias trillium.trace_forall2_extend_inv_r]
theorem extend_inv_r {tr : FiniteTrace A L1} {tr' : FiniteTrace B L2} {b : B} {ℓ2 : L2} :
    TraceForall2 P tr (tr' :tr[ℓ2]: b) →
      ∃ a tr'' ℓ1, tr = (tr'' :tr[ℓ1]: a) ∧ TraceForall2 P tr'' tr' ∧ P a b := by
  rintro (_ | ⟨tr'', _, a, _, ℓ1, _, h1, h2⟩); exact ⟨a, tr'', ℓ1, rfl, h1, h2⟩

end TraceForall2

/-- The states of the three traces are pointwise related by `P` (Rocq `trace_forall3`). -/
@[rocq_alias trillium.trace_forall3]
inductive TraceForall3 {A B C L1 L2 L3 : Type _} (P : A → B → C → Prop) :
    FiniteTrace A L1 → FiniteTrace B L2 → FiniteTrace C L3 → Prop
  | singleton a b c : P a b c → TraceForall3 P {tr[a]} {tr[b]} {tr[c]}
  | extend tr tr' tr'' a b c ℓ1 ℓ2 ℓ3 :
    TraceForall3 P tr tr' tr'' → P a b c →
    TraceForall3 P (tr :tr[ℓ1]: a) (tr' :tr[ℓ2]: b) (tr'' :tr[ℓ3]: c)

namespace TraceForall3

variable {A B C L1 L2 L3 : Type _} {P : A → B → C → Prop}

@[rocq_alias trillium.trace_forall3_impl]
theorem impl {Q : A → B → C → Prop} {tr : FiniteTrace A L1} {tr' : FiniteTrace B L2}
    {tr'' : FiniteTrace C L3} (HPQ : ∀ x y z, P x y z → Q x y z) :
    TraceForall3 P tr tr' tr'' → TraceForall3 Q tr tr' tr'' := by
  intro h
  induction h with
  | singleton a b c h => exact .singleton a b c (HPQ _ _ _ h)
  | extend _ _ _ _ _ _ _ _ _ _ h IH => exact .extend _ _ _ _ _ _ _ _ _ IH (HPQ _ _ _ h)

@[rocq_alias trillium.trace_forall3_last]
theorem last {tr : FiniteTrace A L1} {tr' : FiniteTrace B L2} {tr'' : FiniteTrace C L3} :
    TraceForall3 P tr tr' tr'' → P tr.last tr'.last tr''.last := by
  rintro (⟨_, _, _, h⟩ | ⟨_, _, _, _, _, _, _, _, _, _, h⟩) <;> exact h

@[rocq_alias trillium.trace_forall3_first]
theorem first {tr : FiniteTrace A L1} {tr' : FiniteTrace B L2} {tr'' : FiniteTrace C L3} :
    TraceForall3 P tr tr' tr'' → P tr.first tr'.first tr''.first := by
  intro h
  induction h with
  | singleton _ _ _ h => exact h
  | extend _ _ _ _ _ _ _ _ _ _ _ IH => exact IH

@[rocq_alias trillium.trace_forall3_singleton_inv]
theorem singleton_inv {a : A} {b : B} {c : C} :
    TraceForall3 (L1 := L1) (L2 := L2) (L3 := L3) P {tr[a]} {tr[b]} {tr[c]} → P a b c := by
  rintro ⟨_, _, _, h⟩; exact h

@[rocq_alias trillium.trace_forall3_singleton_inv_l]
theorem singleton_inv_l {a : A} {tr' : FiniteTrace B L2} {tr'' : FiniteTrace C L3} :
    TraceForall3 (L1 := L1) P {tr[a]} tr' tr'' →
      ∃ b c, tr' = {tr[b]} ∧ tr'' = {tr[c]} ∧ P a b c := by
  rintro ⟨_, b, c, h⟩; exact ⟨b, c, rfl, rfl, h⟩

@[rocq_alias trillium.trace_forall2_singleton_inv_m]
theorem singleton_inv_m {tr : FiniteTrace A L1} {b : B} {tr'' : FiniteTrace C L3} :
    TraceForall3 (L2 := L2) P tr {tr[b]} tr'' →
      ∃ a c, tr = {tr[a]} ∧ tr'' = {tr[c]} ∧ P a b c := by
  rintro ⟨a, _, c, h⟩; exact ⟨a, c, rfl, rfl, h⟩

@[rocq_alias trillium.trace_forall3_singleton_inv_r]
theorem singleton_inv_r {tr : FiniteTrace A L1} {tr' : FiniteTrace B L2} {c : C} :
    TraceForall3 (L3 := L3) P tr tr' {tr[c]} →
      ∃ a b, tr = {tr[a]} ∧ tr' = {tr[b]} ∧ P a b c := by
  rintro ⟨a, b, _, h⟩; exact ⟨a, b, rfl, rfl, h⟩

@[rocq_alias trillium.trace_forall3_extend_inv]
theorem extend_inv {tr : FiniteTrace A L1} {tr' : FiniteTrace B L2} {tr'' : FiniteTrace C L3}
    {a : A} {b : B} {c : C} {ℓ1 : L1} {ℓ2 : L2} {ℓ3 : L3} :
    TraceForall3 P (tr :tr[ℓ1]: a) (tr' :tr[ℓ2]: b) (tr'' :tr[ℓ3]: c) →
      TraceForall3 P tr tr' tr'' ∧ P a b c := by
  rintro (_ | ⟨_, _, _, _, _, _, _, _, _, h1, h2⟩); exact ⟨h1, h2⟩

@[rocq_alias trillium.trace_forall3_extend_inv_l]
theorem extend_inv_l {tr1 : FiniteTrace A L1} {a : A} {tr2 : FiniteTrace B L2}
    {tr3 : FiniteTrace C L3} {ℓ1 : L1} :
    TraceForall3 P (tr1 :tr[ℓ1]: a) tr2 tr3 →
      ∃ b tr2' c tr3' ℓ2 ℓ3, tr2 = (tr2' :tr[ℓ2]: b) ∧ tr3 = (tr3' :tr[ℓ3]: c) ∧
        TraceForall3 P tr1 tr2' tr3' ∧ P a b c := by
  rintro (_ | ⟨_, tr2', tr3', _, b, c, _, ℓ2, ℓ3, h1, h2⟩)
  exact ⟨b, tr2', c, tr3', ℓ2, ℓ3, rfl, rfl, h1, h2⟩

@[rocq_alias trillium.trace_forall3_extend_inv_m]
theorem extend_inv_m {tr1 : FiniteTrace A L1} {tr2 : FiniteTrace B L2} {b : B}
    {tr3 : FiniteTrace C L3} {ℓ2 : L2} :
    TraceForall3 P tr1 (tr2 :tr[ℓ2]: b) tr3 →
      ∃ a tr1' c tr3' ℓ1 ℓ3, tr1 = (tr1' :tr[ℓ1]: a) ∧ tr3 = (tr3' :tr[ℓ3]: c) ∧
        TraceForall3 P tr1' tr2 tr3' ∧ P a b c := by
  rintro (_ | ⟨tr1', _, tr3', a, _, c, ℓ1, _, ℓ3, h1, h2⟩)
  exact ⟨a, tr1', c, tr3', ℓ1, ℓ3, rfl, rfl, h1, h2⟩

@[rocq_alias trillium.trace_forall3_extend_inv_r]
theorem extend_inv_r {tr1 : FiniteTrace A L1} {tr2 : FiniteTrace B L2} {tr3 : FiniteTrace C L3}
    {c : C} {ℓ3 : L3} :
    TraceForall3 P tr1 tr2 (tr3 :tr[ℓ3]: c) →
      ∃ a tr1' b tr2' ℓ1 ℓ2, tr1 = (tr1' :tr[ℓ1]: a) ∧ tr2 = (tr2' :tr[ℓ2]: b) ∧
        TraceForall3 P tr1' tr2' tr3 ∧ P a b c := by
  rintro (_ | ⟨tr1', tr2', _, a, b, _, ℓ1, ℓ2, _, h1, h2⟩)
  exact ⟨a, tr1', b, tr2', ℓ1, ℓ2, rfl, rfl, h1, h2⟩

end TraceForall3

end Trillium
