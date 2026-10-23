/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.Fairis.ProofMode
import Trillium.HeapLang.Notation
import Trillium.Fairness.Utils
import Iris.Algebra.Lib.ExclAuth
import Iris.Instances.Lib.Invariants

/-!
# The even/odd example
Port of `fairis/examples/even_odd/even_odd.v`.

Two threads increment a shared counter: the "even" thread only increments it when it is even,
the "odd" thread only when it is odd. The fair model has the natural numbers as states and two
roles `EO.ρEven`, `EO.ρOdd`, which are always live.

## Representation

* Rocq's boolean `Nat.even n` (used as a proposition through `Is_true`) is Mathlib's `Even n`, and
  `Nat.odd n` is `Odd n` (both decidable).
* `excl_authR natO` is iris-lean's `ExclAuthR (A := DiscreteO Nat)`; `own γ (◯E n)` is
  `iOwn γ (◯E ⟨n⟩)`.
* `evenoddΣ`/`subG_evenoddΣ` are subsumed by `ElemG` typeclass synthesis on `BundledGFunctors`.
* The Rocq `Countable EO` instance is an `Encodable EO` instance; the order on roles needed for
  `GSet EO` is derived from it (`ordOfEncodable`).
-/

set_option linter.unusedSectionVars false

namespace Trillium.Fairis.EvenOdd

open Iris Iris.BI Iris.Std Iris.ProofMode OFE COFE ExclAuth
open Trillium Trillium.HeapLang Trillium.Fairness Trillium.Language Trillium.Fairis
open Iris.HeapLang (Loc HeapF)

/-! ## The program -/

/-- Rocq `incr_loop`. -/
@[rocq_alias trillium.fairis.incr_loop]
def incrLoop : Val := tl_val(
  rec incr_loop l n :=
    if cas(l, n, n + #1)
    then incr_loop l (n + #2)
    else incr_loop l n)

/-- Rocq `start`. -/
@[rocq_alias trillium.fairis.even_odd.start]
def start : Val := tl_val(
  λ l,
    let x := !l;
    fork(v(&incrLoop) l x);
    fork(v(&incrLoop) l (x + #1)))

/-! ## The model -/

/-- The roles of the model (Rocq `EO`). -/
@[rocq_alias trillium.fairis.EO]
inductive EO where
  | ρEven
  | ρOdd
  deriving Inhabited

@[rocq_alias trillium.fairis.EO_eqdec]
instance EO.instDecidableEq : DecidableEq EO := fun a b => by
  cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by simp)

@[rocq_alias trillium.fairis.EO_countable]
instance EO.instEncodable : Encodable EO where
  encode | .ρEven => 1 | .ρOdd => 2
  decode | 1 => some .ρEven | 2 => some .ρOdd | _ => none
  encodek eo := by cases eo <;> rfl

#rocq_ignore trillium.fairis.EO_inhabited "Derived `Inhabited EO` instance (`deriving Inhabited`)"

instance : Ord EO := ordOfEncodable
instance : Std.TransOrd EO := transOrd_ordOfEncodable
instance : Std.LawfulEqOrd EO := lawfulEqOrd_ordOfEncodable

/-- The transitions of the model (Rocq `eotrans`). -/
@[rocq_alias trillium.fairis.eotrans]
inductive EOTrans : Nat → Option EO → Nat → Prop where
  | even_trans (n : Nat) : Even n → EOTrans n (some .ρEven) (n + 1)
  | even_fail (n : Nat) : Odd n → EOTrans n (some .ρEven) n
  | odd_trans (n : Nat) : Odd n → EOTrans n (some .ρOdd) (n + 1)
  | odd_fail (n : Nat) : Even n → EOTrans n (some .ρOdd) n

/-- Both roles are always live (Rocq `eo_live_roles`). -/
@[rocq_alias trillium.fairis.eo_live_roles]
def eoLiveRoles : GSet EO := (((∅ : GSet EO).insert .ρEven).insert .ρOdd)

theorem mem_eoLiveRoles (ρ : EO) : ρ ∈ eoLiveRoles := by
  cases ρ <;> simp [eoLiveRoles]

@[rocq_alias trillium.fairis.even_odd.live_spec_holds]
theorem live_spec_holds : ∀ s ρ s', EOTrans s (some ρ) s' → ρ ∈ eoLiveRoles :=
  fun _ ρ _ _ => mem_eoLiveRoles ρ

/-- The fair model of the example (Rocq `the_fair_model`). -/
@[rocq_alias trillium.fairis.even_odd.the_fair_model]
abbrev theFairModel : FairModel where
  fmstate := Nat
  fmrole := EO
  fmtrans := EOTrans
  liveRoles _ := eoLiveRoles
  fm_live_spec := live_spec_holds

/-- The live model of the example, with fuel limit `61` (Rocq `the_model`). -/
@[rocq_alias trillium.fairis.even_odd.the_model]
def theModel : LiveModel BaseLocale theFairModel where
  lmFl _ := 61

@[simp] theorem theModel_lmFl (s : theFairModel.fmstate) : theModel.lmFl s = 61 := rfl

/-! ## Ghost state -/

/-- The camera of the counters of the two threads (Rocq `excl_authR natO`). -/
abbrev EOAuthR : Type := ExclAuthR (A := DiscreteO Nat)

/-- The ghost state of the example (Rocq `evenoddG`). -/
@[rocq_alias trillium.fairis.evenoddG]
class EvenoddG (GF : BundledGFunctors) where
  even_name : GName
  odd_name : GName
  evenodd_n_G : ElemG GF (constOF EOAuthR)

attribute [reducible, instance] EvenoddG.evenodd_n_G

/-- The ghost state of the example, before allocation (Rocq `evenoddPreG`). -/
@[rocq_alias trillium.fairis.evenoddPreG]
class EvenoddPreG (GF : BundledGFunctors) where
  evenodd_PreG : ElemG GF (constOF EOAuthR)

attribute [reducible, instance] EvenoddPreG.evenodd_PreG

#rocq_ignore trillium.fairis.«evenoddΣ»
  "Superseded by the `EvenoddPreG`/`HeapGpreS` typeclasses on `BundledGFunctors`"
#rocq_ignore trillium.fairis.«subG_evenoddΣ» "Superseded by Lean's direct `ElemG` typeclass synthesis"

section proof

variable {GF : BundledGFunctors} [HeapGS theModel GF] [EvenoddG GF]

/-- Rocq's `Let Ns := nroot .@ "even_odd"`. -/
abbrev Ns : Namespace := nroot .@ "even_odd"

/-- Rocq `even_at`. -/
@[rocq_alias trillium.fairis.even_at]
def evenAt (n : Nat) : IProp GF :=
  iOwn (F := constOF EOAuthR) (EvenoddG.even_name GF) (◯E (⟨n⟩ : DiscreteO Nat))

/-- Rocq `odd_at`. -/
@[rocq_alias trillium.fairis.odd_at]
def oddAt (n : Nat) : IProp GF :=
  iOwn (F := constOF EOAuthR) (EvenoddG.odd_name GF) (◯E (⟨n⟩ : DiscreteO Nat))

/-- Rocq `auth_even_at`. -/
@[rocq_alias trillium.fairis.auth_even_at]
def authEvenAt (n : Nat) : IProp GF :=
  iOwn (F := constOF EOAuthR) (EvenoddG.even_name GF) (●E (⟨n⟩ : DiscreteO Nat))

/-- Rocq `auth_odd_at`. -/
@[rocq_alias trillium.fairis.auth_odd_at]
def authOddAt (n : Nat) : IProp GF :=
  iOwn (F := constOF EOAuthR) (EvenoddG.odd_name GF) (●E (⟨n⟩ : DiscreteO Nat))

instance evenAt_timeless (n : Nat) : Timeless (evenAt (GF := GF) n) := by
  unfold evenAt; infer_instance
instance oddAt_timeless (n : Nat) : Timeless (oddAt (GF := GF) n) := by
  unfold oddAt; infer_instance
instance authEvenAt_timeless (n : Nat) : Timeless (authEvenAt (GF := GF) n) := by
  unfold authEvenAt; infer_instance
instance authOddAt_timeless (n : Nat) : Timeless (authOddAt (GF := GF) n) := by
  unfold authOddAt; infer_instance

@[rocq_alias trillium.fairis.even_odd.they_agree]
theorem they_agree (γ : GName) (N M : Nat) :
    ⊢ iOwn (GF := GF) (F := constOF EOAuthR) γ (◯E (⟨N⟩ : DiscreteO Nat)) -∗
      iOwn (F := constOF EOAuthR) γ (●E (⟨M⟩ : DiscreteO Nat)) -∗ ⌜M = N⌝ := by
  iintro HA HB
  icombine HB HA gives %Hval
  ipureintro
  exact DiscreteO.eqv_inj (Iris.ExclAuth.agree Hval)

@[rocq_alias trillium.fairis.even_agree]
theorem even_agree (N M : Nat) : ⊢ evenAt (GF := GF) N -∗ authEvenAt M -∗ ⌜M = N⌝ :=
  they_agree _ N M

@[rocq_alias trillium.fairis.odd_agree]
theorem odd_agree (N M : Nat) : ⊢ oddAt (GF := GF) N -∗ authOddAt M -∗ ⌜M = N⌝ :=
  they_agree _ N M

@[rocq_alias trillium.fairis.even_odd.they_update]
theorem they_update (γ : GName) (N M P : Nat) :
    iOwn (GF := GF) (F := constOF EOAuthR) γ (●E (⟨N⟩ : DiscreteO Nat)) ∗
      iOwn (F := constOF EOAuthR) γ (◯E (⟨M⟩ : DiscreteO Nat)) ==∗
    iOwn (F := constOF EOAuthR) γ (●E (⟨P⟩ : DiscreteO Nat)) ∗
      iOwn (F := constOF EOAuthR) γ (◯E (⟨P⟩ : DiscreteO Nat)) := by
  rw [← iOwn_op.to_eq, ← iOwn_op.to_eq]
  exact entails_wand (iOwn_update ExclAuth.update)

@[rocq_alias trillium.fairis.even_update]
theorem even_update (P N M : Nat) :
    authEvenAt (GF := GF) M ∗ evenAt N ==∗ authEvenAt P ∗ evenAt P :=
  they_update _ M N P

@[rocq_alias trillium.fairis.odd_update]
theorem odd_update (P N M : Nat) :
    authOddAt (GF := GF) M ∗ oddAt N ==∗ authOddAt P ∗ oddAt P :=
  they_update _ M N P

/-- The invariant of the example (Rocq `evenodd_inv_inner`). -/
@[rocq_alias trillium.fairis.evenodd_inv_inner]
def evenoddInvInner (n : Loc) : IProp GF :=
  iprop(∃ N : Nat,
    fragFreeRolesAre (GF := GF) ∅ ∗
    fragModelIs (GF := GF) (N : theFairModel.fmstate) ∗ n ↦ .lit (.int N) ∗
    if Even N then authEvenAt N ∗ authOddAt (N + 1)
    else authEvenAt (N + 1) ∗ authOddAt N)

/-- Rocq `evenodd_inv`. -/
@[rocq_alias trillium.fairis.evenodd_inv]
def evenoddInv (n : Loc) : IProp GF := inv Ns (evenoddInvInner n)

instance evenoddInv_persistent (n : Loc) : Persistent (evenoddInv (GF := GF) n) := by
  unfold evenoddInv; infer_instance

@[rocq_alias trillium.fairis.even_go_spec]
theorem even_go_spec (tid : BaseLocale) (n : Loc) (N : Nat) (f : Nat) (Hf : f > 40) :
    {{ evenoddInv (GF := GF) n ∗ (tid ↦M GMap.singleton (K := theFairModel.fmrole) EO.ρEven f) ∗ evenAt N }}
      tl(v(&incrLoop) #(.loc n) #(.int N)) @[tid]
    {{ RET (Val.lit .unit); tid ↦M ∅ }} := by
  iloeb as Hg generalizing %N %f %Hf
  iintro %Φ ⟨#Hinv, Hf, Heven⟩ Hk
  wp_lam
  wp_pures
  wp_bind (cmpXchg(_, _, _))
  iapply wp_atomic (E₂ := ⊤ \ ↑Ns)
  iunfold evenoddInv at Hinv
  imod inv_acc CoPset.subseteq_top $$ Hinv with ⟨HI, Hclose⟩
  iunfold evenoddInvInner at HI
  icases HI with ⟨%M, >HFR, >Hmod, >Hn, Hauths⟩
  by_cases Heqn : Even M
  · isimp only [Heqn, ite_true] at Hauths
    icases Hauths with ⟨>Hay, >Han⟩
    ihave %Heq := even_agree N M $$ Heven Hay
    subst Heq
    imodintro
    iapply wp_step_model_singlerole _ tid EO.ρEven _ ∅ M (M + 1) _ _ _ rfl
      (EOTrans.even_trans M Heqn) (fun _ h => h) $$ Hmod Hf HFR
    iapply wp_cmpxchg_suc _ _ n _ _ _ _ rfl rfl $$ Hn
    inext
    iintro Hb Hmod Hf HFR
    imod even_update (M + 2) M M $$ [Hay Heven] with ⟨Hay, Heven⟩
    · iframe
    iapply wp_value (h := into_val_val _)
    imod Hclose $$ [Hmod Hay Han Hb HFR] with -
    · inext
      iunfold evenoddInvInner
      iexists M + 1
      have Hodd : ¬ Even (M + 1) := by simpa [Nat.even_add_one] using Heqn
      isimp only [Hodd, ite_false]
      push_cast
      iframe
    imodintro
    isimp only [theModel_lmFl] at Hf
    wp_pures
    rw [show ((M : Int) + 2) = ((M + 2 : Nat) : Int) by push_cast; rfl]
    iapply Hg $$ %(M + 2) %58 [] %Φ [Heven Hf] [Hk]
    · ipureintro; omega
    · iframe
      iunfold evenoddInv
      iexact Hinv
    · inext
      iexact Hk
  · isimp only [Heqn, ite_false] at Hauths
    icases Hauths with ⟨>Hay, >Han⟩
    ihave %Heq := even_agree N (M + 1) $$ Heven Hay
    subst Heq
    imodintro
    have Hodd : Odd M := Nat.not_even_iff_odd.1 Heqn
    iapply wp_step_model_singlerole _ tid EO.ρEven _ ∅ M M _ _ _ rfl
      (EOTrans.even_fail M Hodd) (fun _ h => h) $$ Hmod Hf HFR
    iapply wp_cmpxchg_fail _ _ n _ _ _ _ _ (by simp) rfl $$ Hn
    inext
    iintro Hb Hmod Hf HFR
    iapply wp_value (h := into_val_val _)
    imod Hclose $$ [Hmod Hay Han Hb HFR] with -
    · inext
      iunfold evenoddInvInner
      iexists M
      isimp only [Heqn, ite_false]
      iframe
    imodintro
    isimp only [theModel_lmFl] at Hf
    wp_pures
    iapply Hg $$ %(M + 1) %59 [] %Φ [Heven Hf] [Hk]
    · ipureintro; omega
    · iframe
      iunfold evenoddInv
      iexact Hinv
    · inext
      iexact Hk

@[rocq_alias trillium.fairis.odd_go_spec]
theorem odd_go_spec (tid : BaseLocale) (n : Loc) (N : Nat) (f : Nat) (Hf : f > 40) :
    {{ evenoddInv (GF := GF) n ∗ (tid ↦M GMap.singleton (K := theFairModel.fmrole) EO.ρOdd f) ∗ oddAt N }}
      tl(v(&incrLoop) #(.loc n) #(.int N)) @[tid]
    {{ RET (Val.lit .unit); tid ↦M ∅ }} := by
  iloeb as Hg generalizing %N %f %Hf
  iintro %Φ ⟨#Hinv, Hf, Hodd⟩ Hk
  wp_lam
  wp_pures
  wp_bind (cmpXchg(_, _, _))
  iapply wp_atomic (E₂ := ⊤ \ ↑Ns)
  iunfold evenoddInv at Hinv
  imod inv_acc CoPset.subseteq_top $$ Hinv with ⟨HI, Hclose⟩
  iunfold evenoddInvInner at HI
  icases HI with ⟨%M, >HFR, >Hmod, >Hn, Hauths⟩
  by_cases Heqn : Even M
  · isimp only [Heqn, ite_true] at Hauths
    icases Hauths with ⟨>Hay, >Han⟩
    ihave %Heq := odd_agree N (M + 1) $$ Hodd Han
    subst Heq
    imodintro
    iapply wp_step_model_singlerole _ tid EO.ρOdd _ ∅ M M _ _ _ rfl
      (EOTrans.odd_fail M Heqn) (fun _ h => h) $$ Hmod Hf HFR
    iapply wp_cmpxchg_fail _ _ n _ _ _ _ _ (by simp) rfl $$ Hn
    inext
    iintro Hb Hmod Hf HFR
    iapply wp_value (h := into_val_val _)
    imod Hclose $$ [Hmod Hay Han Hb HFR] with -
    · inext
      iunfold evenoddInvInner
      iexists M
      isimp only [Heqn, ite_true]
      iframe
    imodintro
    isimp only [theModel_lmFl] at Hf
    wp_pures
    iapply Hg $$ %(M + 1) %59 [] %Φ [Hodd Hf] [Hk]
    · ipureintro; omega
    · iframe
      iunfold evenoddInv
      iexact Hinv
    · inext
      iexact Hk
  · isimp only [Heqn, ite_false] at Hauths
    icases Hauths with ⟨>Hay, >Han⟩
    ihave %Heq := odd_agree N M $$ Hodd Han
    subst Heq
    imodintro
    have Hodd' : Odd M := Nat.not_even_iff_odd.1 Heqn
    iapply wp_step_model_singlerole _ tid EO.ρOdd _ ∅ M (M + 1) _ _ _ rfl
      (EOTrans.odd_trans M Hodd') (fun _ h => h) $$ Hmod Hf HFR
    iapply wp_cmpxchg_suc _ _ n _ _ _ _ rfl rfl $$ Hn
    inext
    iintro Hb Hmod Hf HFR
    imod odd_update (M + 2) M M $$ [Han Hodd] with ⟨Han, Hodd⟩
    · iframe
    iapply wp_value (h := into_val_val _)
    imod Hclose $$ [Hmod Hay Han Hb HFR] with -
    · inext
      iunfold evenoddInvInner
      iexists M + 1
      have Heven : Even (M + 1) := by simpa [Nat.even_add_one] using Heqn
      isimp only [Heven, ite_true]
      push_cast
      iframe
    imodintro
    isimp only [theModel_lmFl] at Hf
    wp_pures
    rw [show ((M : Int) + 2) = ((M + 2 : Nat) : Int) by push_cast; rfl]
    iapply Hg $$ %(M + 2) %58 [] %Φ [Hodd Hf] [Hk]
    · ipureintro; omega
    · iframe
      iunfold evenoddInv
      iexact Hinv
    · inext
      iexact Hk

/-- The fragment of the counter of the thread playing role `eo` (Rocq `role_frag`). -/
@[rocq_alias trillium.fairis.role_frag]
def roleFrag : EO → Nat → IProp GF
  | .ρEven => evenAt
  | .ρOdd => oddAt

@[rocq_alias trillium.fairis.incr_loop_spec]
theorem incr_loop_spec (tid : BaseLocale) (n : Loc) (N : Nat) (f : Nat) (Hf : f > 40) (eo : EO) :
    {{ evenoddInv (GF := GF) n ∗ (tid ↦M GMap.singleton (K := theFairModel.fmrole) eo f) ∗
        roleFrag eo N }}
      tl(v(&incrLoop) #(.loc n) #(.int N)) @[tid]
    {{ RET (Val.lit .unit); tid ↦M ∅ }} := by
  iintro %Φ ⟨#Hinv, Hf, Heo⟩ Hk
  cases eo with
  | ρEven =>
    iunfold roleFrag at Heo
    iapply even_go_spec tid n N f Hf $$ %Φ [Hf Heo] Hk
    iframe
    iexact Hinv
  | ρOdd =>
    iunfold roleFrag at Heo
    iapply odd_go_spec tid n N f Hf $$ %Φ [Hf Heo] Hk
    iframe
    iexact Hinv

end proof

section proof_start

variable {GF : BundledGFunctors} [HeapGS theModel GF] [EvenoddG GF]

theorem eo_insert_eq_union (f g : Nat) :
    (GMap.singleton (K := theFairModel.fmrole) EO.ρOdd f).insert EO.ρEven g =
      GMap.singleton EO.ρOdd f ∪ GMap.singleton EO.ρEven g := by
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  rw [Std.ExtTreeMap.getElem?_union]
  cases k <;> simp [GMap.getElem?_insert_ite, GMap.getElem?_singleton]

theorem eo_disj (ρ1 ρ2 : EO) (h : ρ1 ≠ ρ2) (f g : Nat) :
    GMap.Disjoint (GMap.singleton (K := theFairModel.fmrole) ρ1 f) (GMap.singleton ρ2 g) := by
  intro k
  by_cases h1 : ρ1 = k
  · subst h1; right; simp [GMap.getElem?_singleton, Ne.symm h]
  · left; simp [GMap.getElem?_singleton, h1]

theorem eo_union_ne (m : GMap theFairModel.fmrole Nat) (ρ : EO) (g : Nat) :
    m ∪ GMap.singleton (K := theFairModel.fmrole) ρ g ≠ ∅ := by
  intro h
  have := congrArg (fun m : GMap theFairModel.fmrole Nat => m[ρ]?) h
  simp [Std.ExtTreeMap.getElem?_union, GMap.getElem?_singleton] at this

theorem hasFuelsS_eo_union (tid : BaseLocale) (a b : Nat) :
    hasFuelsS (GF := GF) tid ((GMap.singleton (K := theFairModel.fmrole) EO.ρOdd a).insert EO.ρEven b)
      ⊢ hasFuelsS tid (GMap.singleton EO.ρOdd a ∪ GMap.singleton EO.ρEven b) := by
  rw [eo_insert_eq_union]

theorem hasFuelsS_empty_union (tid : BaseLocale) (m : GMap theFairModel.fmrole Nat) :
    hasFuelsS (GF := GF) tid m ⊢ hasFuelsS tid (∅ ∪ m) := by
  have : (∅ ∪ m : GMap theFairModel.fmrole Nat) = m := by
    apply Std.ExtTreeMap.ext_getElem?
    intro k
    simp [Std.ExtTreeMap.getElem?_union]
  rw [this]

theorem eo_disj_empty (m : GMap theFairModel.fmrole Nat) : GMap.Disjoint ∅ m :=
  fun _ => .inl (by simp)

theorem hasFuelsS_eo_union' (tid : BaseLocale) (a b : Nat) :
    hasFuelsS (GF := GF) tid ((GMap.singleton (K := theFairModel.fmrole) EO.ρOdd a).insert EO.ρEven b)
      ⊢ hasFuelsS tid (GMap.singleton EO.ρEven b ∪ GMap.singleton EO.ρOdd a) := by
  have : (GMap.singleton (K := theFairModel.fmrole) EO.ρOdd a).insert EO.ρEven b =
      GMap.singleton EO.ρEven b ∪ GMap.singleton EO.ρOdd a := by
    apply Std.ExtTreeMap.ext_getElem?
    intro k
    rw [Std.ExtTreeMap.getElem?_union]
    cases k <;> simp [GMap.getElem?_insert_ite, GMap.getElem?_singleton]
  rw [this]

@[rocq_alias trillium.fairis.even_odd.start_spec]
theorem start_spec (tid : BaseLocale) (n : Loc) (N1 N2 : Nat) (f : Nat) (Hf : f > 60) :
    {{ evenoddInv (GF := GF) n ∗
        (tid ↦M (GMap.singleton (K := theFairModel.fmrole) EO.ρOdd f).insert EO.ρEven f) ∗
        evenAt N1 ∗ oddAt N2 }}
      tl(v(&start) #(.loc n)) @[tid]
    {{ RET (Val.lit .unit); tid ↦M ∅ }} := by
  iintro %Φ ⟨#Hinv, Hf, Heven_at, Hodd_at⟩ HΦ
  unfold start
  wp_pures
  wp_bind (!_)
  iapply wp_atomic (E₂ := ⊤ \ ↑Ns)
  iunfold evenoddInv at Hinv
  imod inv_acc CoPset.subseteq_top $$ Hinv with ⟨HI, Hclose⟩
  iunfold evenoddInvInner at HI
  icases HI with ⟨%M, >HFR, >Hmod, >Hn, Hauths⟩
  imodintro
  icases (has_fuels_gt_1 _ _ (by solve_fuel_positive)).1 $$ Hf with Hf
  simpl_has_fuels
  iapply wp_step_fuel _ _ _ _ _ _ (GMap.insert_ne_empty _ _ _) $$ [Hf]
  · inext; iexact Hf
  iapply Trillium.HeapLang.wp_load _ _ n _ _ _ $$ Hn
  inext
  iintro Hn Hf
  iapply wp_value (h := into_val_val _)
  by_cases Heven : Even M
  · isimp only [Heven, ite_true] at Hauths
    icases Hauths with ⟨Hay, Han⟩
    ihave %HN1 := even_agree N1 M $$ Heven_at Hay
    ihave %HN2 := odd_agree N2 (M + 1) $$ Hodd_at Han
    subst HN1 HN2
    imod Hclose $$ [Hmod Hay Han Hn HFR] with -
    · inext
      iunfold evenoddInvInner
      iexists M
      isimp only [Heven, ite_true]
      iframe
    imodintro
    wp_pures
    wp_bind (fork(_))
    icases (has_fuels_gt_1 _ _ (by solve_fuel_positive)).1 $$ Hf with Hf
    simpl_has_fuels
    icases hasFuelsS_eo_union tid _ _ $$ Hf with Hf
    iapply wp_role_fork _ tid _ _ _ (GMap.singleton EO.ρOdd _) (GMap.singleton EO.ρEven _)
      (eo_disj _ _ (by decide) _ _) (eo_union_ne _ _ _) $$ Hf [Heven_at] [HΦ Hodd_at]
    · iintro %tid' !> Hf
      iapply incr_loop_spec tid' n M (f - (4 + 1)) (by omega) EO.ρEven $$ %(fun _ => iprop(tid' ↦M ∅))
        [Hf Heven_at] []
      · iunfold roleFrag, evenoddInv
        iframe
        iexact Hinv
      · inext
        iintro H
        iexact H
    · inext
      iintro Hf
      imodintro
      wp_pures
      icases (has_fuels_gt_1 _ _ (by solve_fuel_positive)).1 $$ Hf with Hf
      simpl_has_fuels
      icases hasFuelsS_empty_union tid _ $$ Hf with Hf
      iapply wp_role_fork _ tid _ _ _ ∅ (GMap.singleton EO.ρOdd _)
        (eo_disj_empty _) (eo_union_ne _ _ _) $$ Hf [Hodd_at] [HΦ]
      · iintro %tid' !> Hf
        wp_pures
        rw [show ((M : Int) + 1) = ((M + 1 : Nat) : Int) by push_cast; rfl]
        iapply incr_loop_spec tid' n (M + 1) (f - 9) (by omega) EO.ρOdd
          $$ %(fun _ => iprop(tid' ↦M ∅)) [Hf Hodd_at] []
        · iunfold roleFrag, evenoddInv
          iframe
          iexact Hinv
        · inext
          iintro H
          iexact H
      · inext
        iintro Hf
        imodintro
        iapply HΦ $$ Hf
  · isimp only [Heven, ite_false] at Hauths
    icases Hauths with ⟨Hay, Han⟩
    ihave %HN1 := even_agree N1 (M + 1) $$ Heven_at Hay
    ihave %HN2 := odd_agree N2 M $$ Hodd_at Han
    subst HN1 HN2
    imod Hclose $$ [Hmod Hay Han Hn HFR] with -
    · inext
      iunfold evenoddInvInner
      iexists M
      isimp only [Heven, ite_false]
      iframe
    imodintro
    wp_pures
    wp_bind (fork(_))
    icases (has_fuels_gt_1 _ _ (by solve_fuel_positive)).1 $$ Hf with Hf
    simpl_has_fuels
    icases hasFuelsS_eo_union' tid _ _ $$ Hf with Hf
    iapply wp_role_fork _ tid _ _ _ (GMap.singleton EO.ρEven _) (GMap.singleton EO.ρOdd _)
      (eo_disj _ _ (by decide) _ _) (eo_union_ne _ _ _) $$ Hf [Hodd_at] [HΦ Heven_at]
    · iintro %tid' !> Hf
      iapply incr_loop_spec tid' n M (f - (4 + 1)) (by omega) EO.ρOdd
        $$ %(fun _ => iprop(tid' ↦M ∅)) [Hf Hodd_at] []
      · iunfold roleFrag, evenoddInv
        iframe
        iexact Hinv
      · inext
        iintro H
        iexact H
    · inext
      iintro Hf
      imodintro
      wp_pures
      icases (has_fuels_gt_1 _ _ (by solve_fuel_positive)).1 $$ Hf with Hf
      simpl_has_fuels
      icases hasFuelsS_empty_union tid _ $$ Hf with Hf
      iapply wp_role_fork _ tid _ _ _ ∅ (GMap.singleton EO.ρEven _)
        (eo_disj_empty _) (eo_union_ne _ _ _) $$ Hf [Heven_at] [HΦ]
      · iintro %tid' !> Hf
        wp_pures
        rw [show ((M : Int) + 1) = ((M + 1 : Nat) : Int) by push_cast; rfl]
        iapply incr_loop_spec tid' n (M + 1) (f - 9) (by omega) EO.ρEven
          $$ %(fun _ => iprop(tid' ↦M ∅)) [Hf Heven_at] []
        · iunfold roleFrag, evenoddInv
          iframe
          iexact Hinv
        · inext
          iintro H
          iexact H
      · inext
        iintro Hf
        imodintro
        iapply HΦ $$ Hf

end proof_start

end Trillium.Fairis.EvenOdd
