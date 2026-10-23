/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.Fairness.Inftraces
import Trillium.Fairness.TraceLookup
import Trillium.Fairness.TraceLen

/-!
# Destuttering of traces
Port of `fairis/destuttering.v`.

Given a projection of states `Us : St → S'` and a partial projection of labels
`Ul : L → Option L'`, a trace `btr : Trace St L` is *up to stutter* a trace `str : Trace S' L'`
when `str` is obtained from `btr` by mapping states with `Us`, labels with `Ul`, and dropping
(finitely many consecutive) steps whose label is mapped to `none` and which do not change the
projected state.

Representation decisions:
* Rocq's `dec_unless` is stated with a `match` on `after n tr`; here it quantifies over the
  `cons` suffixes of `tr` (`decUnless`), which is equivalent and avoids matching on the
  coinductive trace type.
* Rocq's `upto_stutter` is a paco greatest fixpoint of the functor `upto_stutter_ind` (an
  inductive type parametrised by the coinductive hypothesis). Lean's `coinductive` command does
  not support such mixed inductive-coinductive definitions, so `UptoStutterInd R` is an ordinary
  inductive predicate and `UptoStutter` is defined impredicatively as the union of all
  post-fixpoints of `UptoStutterInd`. `UptoStutter.unfold` (Rocq `punfold`),
  `UptoStutter.fold` (Rocq `pfold`) and `UptoStutter.coind` (Rocq `pcofix`, with paco-style
  accumulation of the coinductive hypothesis) are its API.
* Rocq's `Program Fixpoint destutter_once_step` is defined by structural recursion on the fuel
  `N`; Rocq's `CoFixpoint destutter_gen` is defined with `Trace.corec`.
-/

namespace Trillium.Fairis

open Trillium.Fairness Trace

section DecUnless

variable {St S' L L' : Type _} (Us : St → S') (Ul : L → Option L')

/-- Every step of `tr` either has a visible label (`Ul ℓ = some _`) or decreases `Ψ` while
keeping the projected state unchanged. -/
@[rocq_alias trillium.fairis.dec_unless]
def decUnless (Ψ : St → Nat) (tr : Trace St L) : Prop :=
  ∀ n s ℓ tr', after n tr = some (s -[ℓ]-> tr') →
    (∃ ℓ', Ul ℓ = some ℓ') ∨ (Ψ tr'.first < Ψ s ∧ Us s = Us tr'.first)

variable {Us Ul}

@[rocq_alias trillium.fairis.dec_unless_next]
theorem dec_unless_next (Ψ : St → Nat) (s : St) (ℓ : L) (tr : Trace St L)
    (Hdec : decUnless Us Ul Ψ (s -[ℓ]-> tr)) : decUnless Us Ul Ψ tr := by
  intro n s' ℓ' tr' h
  exact Hdec (n + 1) s' ℓ' tr' (by rw [after_succ_cons]; exact h)

end DecUnless

section Destuttering

variable {St S' L L' : Type _} (Us : St → S') (Ul : L → Option L')

/-- The generating functor of `UptoStutter` (Rocq `upto_stutter_ind`): an inductive predicate
parametrised by the coinductive hypothesis `R`. -/
@[rocq_alias trillium.fairis.upto_stutter_ind]
inductive UptoStutterInd (R : Trace St L → Trace S' L' → Prop) :
    Trace St L → Trace S' L' → Prop where
  | singleton (s : St) : UptoStutterInd R (singl s) (singl (Us s))
  | stutter (btr : Trace St L) (str : Trace S' L') (s : St) (ℓ : L) :
      Ul ℓ = none → Us s = Us btr.first → Us s = str.first →
      UptoStutterInd R btr str → UptoStutterInd R (s -[ℓ]-> btr) str
  | step (btr : Trace St L) (str : Trace S' L') (s : St) (ℓ : L) (s' : S') (ℓ' : L') :
      Us s = s' → Ul ℓ = some ℓ' → R btr str → UptoStutterInd R (s -[ℓ]-> btr) (s' -[ℓ']-> str)

/-- `btr` is, up to stuttering steps, the trace `str` (Rocq `upto_stutter`, the paco greatest
fixpoint of `upto_stutter_ind`). -/
@[rocq_alias trillium.fairis.upto_stutter]
def UptoStutter (btr : Trace St L) (str : Trace S' L') : Prop :=
  ∃ R : Trace St L → Trace S' L' → Prop, R btr str ∧ ∀ b s, R b s → UptoStutterInd Us Ul R b s

variable {Us Ul}

@[rocq_alias trillium.fairis.upto_stutter_mono]
theorem upto_stutter_mono {R R' : Trace St L → Trace S' L' → Prop} (LE : ∀ b s, R b s → R' b s)
    {btr : Trace St L} {str : Trace S' L'} (IN : UptoStutterInd Us Ul R btr str) :
    UptoStutterInd Us Ul R' btr str := by
  induction IN with
  | singleton s => exact .singleton s
  | stutter btr str s ℓ h1 h2 h3 _ IH => exact .stutter btr str s ℓ h1 h2 h3 IH
  | step btr str s ℓ s' ℓ' h1 h2 h3 => exact .step btr str s ℓ s' ℓ' h1 h2 (LE _ _ h3)

namespace UptoStutter

/-- Unfolding (Rocq `punfold`). -/
theorem unfold {btr : Trace St L} {str : Trace S' L'} (h : UptoStutter Us Ul btr str) :
    UptoStutterInd Us Ul (UptoStutter Us Ul) btr str := by
  obtain ⟨R, HR, Hpost⟩ := h
  exact upto_stutter_mono (fun b s Hbs => ⟨R, Hbs, Hpost⟩) (Hpost _ _ HR)

/-- Folding (Rocq `pfold`). -/
theorem fold {btr : Trace St L} {str : Trace S' L'}
    (h : UptoStutterInd Us Ul (UptoStutter Us Ul) btr str) : UptoStutter Us Ul btr str :=
  ⟨fun b s => UptoStutterInd Us Ul (UptoStutter Us Ul) b s, h,
    fun _ _ H => upto_stutter_mono (fun _ _ H' => H'.unfold) H⟩

/-- Coinduction with accumulation (Rocq `pcofix`): to prove `UptoStutter` for all pairs in `R`,
unfold one layer, where the coinductive hypothesis may be used for `R` or for `UptoStutter`. -/
theorem coind (R : Trace St L → Trace S' L' → Prop)
    (H : ∀ b s, R b s → UptoStutterInd Us Ul (fun b s => R b s ∨ UptoStutter Us Ul b s) b s)
    {btr : Trace St L} {str : Trace S' L'} (h : R btr str) : UptoStutter Us Ul btr str := by
  refine ⟨fun b s => R b s ∨ UptoStutter Us Ul b s, .inl h, ?_⟩
  rintro b s (Hbs | Hbs)
  · exact H b s Hbs
  · exact upto_stutter_mono (fun _ _ H' => .inr H') Hbs.unfold

end UptoStutter

/-- Inversion of `UptoStutterInd` on a `cons` on the left. -/
theorem UptoStutterInd.cons_inv {R : Trace St L → Trace S' L' → Prop} {s : St} {ℓ : L}
    {btr : Trace St L} {str : Trace S' L'} (h : UptoStutterInd Us Ul R (s -[ℓ]-> btr) str) :
    (Ul ℓ = none ∧ Us s = Us btr.first ∧ Us s = str.first ∧ UptoStutterInd Us Ul R btr str) ∨
      ∃ ℓ' str', str = (Us s -[ℓ']-> str') ∧ Ul ℓ = some ℓ' ∧ R btr str' := by
  generalize hb : (s -[ℓ]-> btr) = b at h
  cases h with
  | singleton s0 => exact absurd hb cons_ne_singl
  | stutter btr0 str0 s0 ℓ0 h1 h2 h3 h4 =>
    obtain ⟨rfl, rfl, rfl⟩ := cons_inj.1 hb
    exact .inl ⟨h1, h2, h3, h4⟩
  | step btr0 str0 s0 ℓ0 s' ℓ' h1 h2 h3 =>
    obtain ⟨rfl, rfl, rfl⟩ := cons_inj.1 hb
    subst h1
    exact .inr ⟨ℓ', str0, rfl, h2, h3⟩

/-- Inversion of `UptoStutterInd` on a `singl` on the left. -/
theorem UptoStutterInd.singl_inv {R : Trace St L → Trace S' L' → Prop} {s : St}
    {str : Trace S' L'} (h : UptoStutterInd Us Ul R (singl s) str) : str = singl (Us s) := by
  generalize hb : (singl s : Trace St L) = b at h
  cases h with
  | singleton s0 => rw [singl_inj.1 hb]
  | stutter => exact absurd hb.symm cons_ne_singl
  | step => exact absurd hb.symm cons_ne_singl

/-- The first state of `str` is the projection of the first state of `btr`. -/
theorem UptoStutterInd.first {R : Trace St L → Trace S' L' → Prop} {btr : Trace St L}
    {str : Trace S' L'} (h : UptoStutterInd Us Ul R btr str) : str.first = Us btr.first := by
  cases h with
  | singleton s => rfl
  | stutter _ _ _ _ _ _ h3 _ => exact h3.symm
  | step _ _ _ _ _ _ h1 _ _ => exact h1.symm

@[rocq_alias trillium.fairis.upto_stutter_after]
theorem upto_stutter_after {btr : Trace St L} {str : Trace S' L'} (n : Nat) {str' : Trace S' L'} :
    UptoStutter Us Ul btr str → after n str = some str' →
      ∃ n' btr', after n' btr = some btr' ∧ UptoStutter Us Ul btr' str' := by
  induction n generalizing btr str str' with
  | zero =>
    intro Hupto Hafter
    simp only [after_0_id, Option.some.injEq] at Hafter
    exact ⟨0, btr, rfl, Hafter ▸ Hupto⟩
  | succ n IH =>
    intro Hupto Hafter
    have Hind := Hupto.unfold
    clear Hupto
    induction Hind with
    | singleton s => simp at Hafter
    | stutter btr str s ℓ _ _ _ _ IHH =>
      obtain ⟨n', btr', h1, h2⟩ := IHH Hafter
      exact ⟨n' + 1, btr', by rw [after_succ_cons]; exact h1, h2⟩
    | step btr str s ℓ s' ℓ' _ _ Hrest =>
      rw [after_succ_cons] at Hafter
      obtain ⟨n', btr', h1, h2⟩ := IH Hrest Hafter
      exact ⟨n' + 1, btr', by rw [after_succ_cons]; exact h1, h2⟩

@[rocq_alias trillium.fairis.upto_stutter_after']
theorem upto_stutter_after' {btr : Trace St L} {str : Trace S' L'} (n : Nat) {btr' : Trace St L} :
    UptoStutter Us Ul btr str → after n btr = some btr' →
      ∃ n' str', after n' str = some str' ∧ UptoStutter Us Ul btr' str' := by
  induction n generalizing btr str btr' with
  | zero =>
    intro Hupto Hafter
    simp only [after_0_id, Option.some.injEq] at Hafter
    exact ⟨0, str, rfl, Hafter ▸ Hupto⟩
  | succ n IH =>
    intro Hupto Hafter
    cases btr with
    | singl s => simp at Hafter
    | cons s ℓ btr =>
      rw [after_succ_cons] at Hafter
      rcases Hupto.unfold.cons_inv with ⟨_, _, _, Hind⟩ | ⟨ℓ', str', rfl, _, Hrest⟩
      · exact IH (UptoStutter.fold Hind) Hafter
      · obtain ⟨n', str'', h1, h2⟩ := IH Hrest Hafter
        exact ⟨n' + 1, str'', by rw [after_succ_cons]; exact h1, h2⟩

@[rocq_alias trillium.fairis.upto_stutter_after_None]
theorem upto_stutter_after_None {btr : Trace St L} {str : Trace S' L'} (n : Nat) :
    UptoStutter Us Ul btr str → after n str = none → ∃ n', after n' btr = none := by
  induction n generalizing btr str with
  | zero => intro _ Hafter; simp at Hafter
  | succ n IH =>
    intro Hupto Hafter
    have Hind := Hupto.unfold
    clear Hupto
    induction Hind with
    | singleton s => exact ⟨1, by simp⟩
    | stutter btr str s ℓ _ _ _ _ IHH =>
      obtain ⟨n', h⟩ := IHH Hafter
      exact ⟨n' + 1, by rw [after_succ_cons]; exact h⟩
    | step btr str s ℓ s' ℓ' _ _ Hrest =>
      rw [after_succ_cons] at Hafter
      obtain ⟨n', h⟩ := IH Hrest Hafter
      exact ⟨n' + 1, by rw [after_succ_cons]; exact h⟩

@[rocq_alias trillium.fairis.upto_stutter_infinite_trace]
theorem upto_stutter_infinite_trace (tr1 : Trace St L) (tr2 : Trace S' L') :
    UptoStutter Us Ul tr1 tr2 → infiniteTrace tr1 → infiniteTrace tr2 := by
  intro Hstutter Hinf n
  induction n generalizing tr1 tr2 with
  | zero => rfl
  | succ n IHn =>
    have Hind := Hstutter.unfold
    clear Hstutter
    induction Hind with
    | singleton s => simpa using Hinf 1
    | stutter btr str s ℓ _ _ _ _ IHH =>
      exact IHH (fun m => by simpa using Hinf (m + 1))
    | step btr str s ℓ s' ℓ' _ _ Hrest =>
      rw [after_succ_cons]
      exact IHn btr str Hrest (fun m => by simpa using Hinf (m + 1))

@[rocq_alias trillium.fairis.upto_stutter_trfirst]
theorem upto_stutter_trfirst (btr : Trace St L) (str : Trace S' L')
    (CORR : UptoStutter Us Ul btr str) : str.first = Us btr.first :=
  CORR.unfold.first

variable (Us Ul)

/-- One destuttering step (Rocq `Program Fixpoint destutter_once_step`): skip the invisible
steps at the beginning of `btr` (at most `N` of them, as `Ψ` decreases along them) and return
either the projection of the final state or the first visible step with the remaining trace. -/
@[rocq_alias trillium.fairis.destutter_once_step]
def destutterOnceStep (Ψ : St → Nat) :
    (N : Nat) → (btr : Trace St L) → Ψ btr.first < N → decUnless Us Ul Ψ btr →
      S' ⊕ (S' × L' × { btr' : Trace St L // decUnless Us Ul Ψ btr' })
  | 0, _, Hlt, _ => absurd Hlt (Nat.not_lt_zero _)
  | N + 1, btr, Hlt, Hdec =>
    match Hd : btr.dest with
    | .inl s => .inl (Us s)
    | .inr (s, l, btr') =>
      have Hbtr : btr = s -[l]-> btr' := by rw [← ofDest_dest btr, Hd]; rfl
      match HUl : Ul l with
      | some l' => .inr (Us s, l', ⟨btr', dec_unless_next Ψ s l btr' (Hbtr ▸ Hdec)⟩)
      | none =>
        destutterOnceStep Ψ N btr'
          (by
            rcases Hdec 0 s l btr' (by rw [Hbtr]; rfl) with ⟨_, h⟩ | ⟨h, _⟩
            · rw [HUl] at h; cases h
            · subst Hbtr; simp only [first_cons] at Hlt; omega)
          (dec_unless_next Ψ s l btr' (Hbtr ▸ Hdec))

theorem destutterOnceStep_singl (Ψ : St → Nat) (N : Nat) (s : St) (Hlt) (Hdec) :
    destutterOnceStep Us Ul Ψ (N + 1) (singl s) Hlt Hdec = .inl (Us s) := by
  simp only [destutterOnceStep]
  split
  · rename_i s' Hd; simp only [dest_singl, Sum.inl.injEq] at Hd; rw [Hd]
  · rename_i Hd; simp at Hd

theorem destutterOnceStep_cons_some (Ψ : St → Nat) (N : Nat) (s : St) (l : L) (btr : Trace St L)
    (l' : L') (HUl : Ul l = some l') (Hlt) (Hdec) :
    destutterOnceStep Us Ul Ψ (N + 1) (s -[l]-> btr) Hlt Hdec =
      .inr (Us s, l', ⟨btr, dec_unless_next Ψ s l btr Hdec⟩) := by
  simp only [destutterOnceStep]
  split
  · rename_i Hd; simp at Hd
  · rename_i s0 l0 btr0 Hd
    simp only [dest_cons, Sum.inr.injEq, Prod.mk.injEq] at Hd
    obtain ⟨rfl, rfl, rfl⟩ := Hd
    split
    · rename_i l1 HUl'; rw [HUl] at HUl'; cases HUl'; rfl
    · rename_i HUl'; rw [HUl] at HUl'; cases HUl'

theorem destutterOnceStep_cons_none (Ψ : St → Nat) (N : Nat) (s : St) (l : L) (btr : Trace St L)
    (HUl : Ul l = none) (Hlt) (Hdec) (Hlt' : Ψ btr.first < N) :
    destutterOnceStep Us Ul Ψ (N + 1) (s -[l]-> btr) Hlt Hdec =
      destutterOnceStep Us Ul Ψ N btr Hlt' (dec_unless_next Ψ s l btr Hdec) := by
  simp only [destutterOnceStep]
  split
  · rename_i Hd; simp at Hd
  · rename_i s0 l0 btr0 Hd
    simp only [dest_cons, Sum.inr.injEq, Prod.mk.injEq] at Hd
    obtain ⟨rfl, rfl, rfl⟩ := Hd
    split
    · rename_i l1 HUl'; rw [HUl] at HUl'; cases HUl'
    · rfl

/-- The state of the corecursion of `destutterGen`: fuel, trace, and the invariants. -/
private abbrev DestutterState (Ψ : St → Nat) :=
  Σ' (N : Nat) (btr : Trace St L), Ψ btr.first < N ∧ decUnless Us Ul Ψ btr

/-- One step of the corecursion of `destutterGen`. -/
private def destutterStep (Ψ : St → Nat) (x : DestutterState Us Ul Ψ) :
    S' ⊕ (S' × L' × DestutterState Us Ul Ψ) :=
  match destutterOnceStep Us Ul Ψ x.1 x.2.1 x.2.2.1 x.2.2.2 with
  | .inl s' => .inl s'
  | .inr (s', l', z) => .inr (s', l', ⟨Ψ z.1.first + 1, z.1, Nat.lt_succ_self _, z.2⟩)

/-- The destuttered trace (Rocq `CoFixpoint destutter_gen`). -/
@[rocq_alias trillium.fairis.destutter_gen]
def destutterGen (Ψ : St → Nat) (N : Nat) (btr : Trace St L) (Hlt : Ψ btr.first < N)
    (Hdec : decUnless Us Ul Ψ btr) : Trace S' L' :=
  Trace.corec (destutterStep Us Ul Ψ) ⟨N, btr, Hlt, Hdec⟩

theorem destutterGen_eq (Ψ : St → Nat) (N : Nat) (btr : Trace St L) (Hlt : Ψ btr.first < N)
    (Hdec : decUnless Us Ul Ψ btr) :
    destutterGen Us Ul Ψ N btr Hlt Hdec =
      match destutterOnceStep Us Ul Ψ N btr Hlt Hdec with
      | .inl s' => singl s'
      | .inr (s', l', z) =>
        s' -[l']-> destutterGen Us Ul Ψ (Ψ z.1.first + 1) z.1 (Nat.lt_succ_self _) z.2 := by
  rw [destutterGen, Trace.corec_eq]
  dsimp only [destutterStep]
  generalize destutterOnceStep Us Ul Ψ N btr Hlt Hdec = r
  rcases r with s' | ⟨s', l', z⟩ <;> rfl

/-- The destuttered trace (Rocq `destutter`). -/
@[rocq_alias trillium.fairis.destutter]
def destutter (Ψ : St → Nat) (btr : Trace St L) (Hdec : decUnless Us Ul Ψ btr) : Trace S' L' :=
  destutterGen Us Ul Ψ (Ψ btr.first + 1) btr (Nat.lt_succ_self _) Hdec

@[rocq_alias trillium.fairis.destutter_same_Us]
theorem destutter_same_Us (N : Nat) (Ψ : St → Nat) (btr : Trace St L) (Hlt : Ψ btr.first < N)
    (Hdec : decUnless Us Ul Ψ btr) :
    match destutterOnceStep Us Ul Ψ N btr Hlt Hdec with
    | .inl s' => Us btr.first = s'
    | .inr (s', _, _) => Us btr.first = s' := by
  induction N generalizing btr with
  | zero => exact absurd Hlt (Nat.not_lt_zero _)
  | succ N IHN =>
    cases btr with
    | singl s => rw [destutterOnceStep_singl]; rfl
    | cons s ℓ btr' =>
      cases HUl : Ul ℓ with
      | some ℓ' => rw [destutterOnceStep_cons_some Us Ul Ψ N s ℓ btr' ℓ' HUl]; rfl
      | none =>
        rcases Hdec 0 s ℓ btr' rfl with ⟨_, h⟩ | ⟨Hlt', Hsame⟩
        · rw [HUl] at h; cases h
        · have Hlt'' : Ψ btr'.first < N := by simp only [first_cons] at Hlt; omega
          rw [destutterOnceStep_cons_none Us Ul Ψ N s ℓ btr' HUl Hlt Hdec Hlt'']
          have := IHN btr' Hlt'' (dec_unless_next Ψ s ℓ btr' Hdec)
          simp only [first_cons, Hsame]
          exact this

@[rocq_alias trillium.fairis.destutter_spec_ind]
theorem destutter_spec_ind (N : Nat) (Ψ : St → Nat) (btr : Trace St L)
    (Hdec : decUnless Us Ul Ψ btr) (Hlt : Ψ btr.first < N) :
    UptoStutter Us Ul btr (destutterGen Us Ul Ψ N btr Hlt Hdec) := by
  refine UptoStutter.coind
    (fun b s => ∃ N Hlt Hdec, s = destutterGen Us Ul Ψ N b Hlt Hdec) ?_ ⟨N, Hlt, Hdec, rfl⟩
  rintro b _ ⟨N, Hlt, Hdec, rfl⟩
  induction N generalizing b with
  | zero => exact absurd Hlt (Nat.not_lt_zero _)
  | succ N IHN =>
    rw [destutterGen_eq]
    cases b with
    | singl s =>
      rw [destutterOnceStep_singl]
      exact .singleton s
    | cons s ℓ btr' =>
      cases HUl : Ul ℓ with
      | some ℓ' =>
        rw [destutterOnceStep_cons_some Us Ul Ψ N s ℓ btr' ℓ' HUl]
        exact .step _ _ s ℓ _ ℓ' rfl HUl (.inl ⟨_, _, _, rfl⟩)
      | none =>
        rcases Hdec 0 s ℓ btr' rfl with ⟨_, h⟩ | ⟨Hlt', Hsame⟩
        · rw [HUl] at h; cases h
        · have Hlt'' : Ψ btr'.first < N := by simp only [first_cons] at Hlt; omega
          rw [destutterOnceStep_cons_none Us Ul Ψ N s ℓ btr' HUl Hlt Hdec Hlt'']
          have IH := IHN btr' Hlt'' (dec_unless_next Ψ s ℓ btr' Hdec)
          rw [destutterGen_eq] at IH
          refine .stutter _ _ s ℓ HUl Hsame ?_ IH
          have HH := destutter_same_Us Us Ul N Ψ btr' Hlt'' (dec_unless_next Ψ s ℓ btr' Hdec)
          revert HH
          split <;> simp_all

@[rocq_alias trillium.fairis.destutter_spec]
theorem destutter_spec (Ψ : St → Nat) (btr : Trace St L) (Hdec : decUnless Us Ul Ψ btr) :
    UptoStutter Us Ul btr (destutter Us Ul Ψ btr Hdec) :=
  destutter_spec_ind Us Ul _ Ψ btr Hdec _

@[rocq_alias trillium.fairis.can_destutter]
theorem can_destutter (Ψ : St → Nat) (btr : Trace St L) (Hdec : decUnless Us Ul Ψ btr) :
    ∃ str, UptoStutter Us Ul btr str :=
  ⟨_, destutter_spec Us Ul Ψ btr Hdec⟩

end Destuttering

section Lookup

variable {St S' L L' : Type _} {Us : St → S'} (Ul : L → Option L')

attribute [local simp] traceLookup_eq stateLookup_eq labelLookup_eq

@[rocq_alias trillium.fairis.upto_stutter_trace_label_lookup]
theorem upto_stutter_trace_label_lookup {btr : Trace St L} {str : Trace S' L'} (n : Nat)
    (st : St) (ℓ : L) (st' : St) (l : L') :
    UptoStutter Us Ul btr str → btr !! n = some (st, some (ℓ, st')) → Ul ℓ = some l →
      ∃ n', str L!! n' = some l := by
  intro UPTO NTH MATCH
  obtain ⟨atr', AFTER, -⟩ := (trace_lookup_after_strong btr st ℓ st' n).2 NTH
  obtain ⟨n', str', AFTER', UPTOn⟩ := upto_stutter_after' n UPTO AFTER
  refine ⟨n', ?_⟩
  rcases UPTOn.unfold.cons_inv with ⟨h, -⟩ | ⟨ℓ', str'', rfl, h, -⟩
  · rw [MATCH] at h; cases h
  · rw [MATCH] at h; cases h
    simp [AFTER']

@[rocq_alias trillium.fairis.upto_stutter_state_lookup]
theorem upto_stutter_state_lookup {btr : Trace St L} {str : Trace S' L'} (n' : Nat) (st' : S') :
    UptoStutter Us Ul btr str → str S!! n' = some st' →
      ∃ n st, btr S!! n = some st ∧ Us st = st' := by
  intro UPTO NTH
  simp only [stateLookup_eq, Option.map_eq_some_iff] at NTH
  obtain ⟨str_n, AFTER, rfl⟩ := NTH
  obtain ⟨n, btr', AFTER', UPTOn⟩ := upto_stutter_after n' UPTO AFTER
  exact ⟨n, btr'.first, by simp [AFTER'], (upto_stutter_trfirst _ _ UPTOn).symm⟩

@[rocq_alias trillium.fairis.upto_stutter_state_lookup']
theorem upto_stutter_state_lookup' {btr : Trace St L} {str : Trace S' L'} (n : Nat) (bst : St) :
    UptoStutter Us Ul btr str → btr S!! n = some bst → ∃ n', str S!! n' = some (Us bst) := by
  intro UPTO NTH
  simp only [stateLookup_eq, Option.map_eq_some_iff] at NTH
  obtain ⟨btr_n, AFTER, rfl⟩ := NTH
  obtain ⟨n', str', AFTER', UPTOn⟩ := upto_stutter_after' n UPTO AFTER
  exact ⟨n', by simp [AFTER', upto_stutter_trfirst _ _ UPTOn]⟩

end Lookup

end Trillium.Fairis
