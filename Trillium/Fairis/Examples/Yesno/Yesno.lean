/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.Fairis.ProofMode
import Trillium.HeapLang.Notation
import Trillium.Fairis.FairTermination
import Iris.Algebra.Lib.ExclAuth
import Iris.Instances.Lib.Invariants

/-!
# The yes/no example
Port of `fairis/examples/yesno/yesno.v`: two threads `yes` and `no` alternately flip a shared
boolean and each decrements its own counter, with the fair model `theFairModel` (states:
counter × whose turn; roles `Y`, `No`) and the live model `theModel` (61 units of fuel).

## Representation

* The HeapLang programs use Trillium's `tl(…)`/`tl_val(…)` notation; Rocq's `#N` for `N : nat`
  is `#(.int N)`, `#b` for a location is `#(.loc b)`.
* `theFairModel` is an `abbrev`, so that instances on `theFairModel.fmrole` (= `YN`) and
  `theFairModel.fmstate` (= `ℕ × Bool`) are found by reducible unfolding (needed by the fuel
  tactics and the `GMap` simp lemmas).
* stdpp's `Countable YN` is an `Encodable YN` instance; the `Ord` instance required by
  `GSet YN`/`GMap YN _` is `ordOfEncodable`.
* `excl_authR natO` is iris-lean's `ExclAuthR (A := DiscreteO Nat)` (functor `NatAuthF`);
  `yesnoG`/`yesnoPreG` are classes on `BundledGFunctors`.
* `{[ Y := f ]}` is `GMap.singleton Y f`, `{[ Y := f; No := f ]}` is
  `(GMap.singleton No f).insert Y f`; Texan triples `{{{ P }}} e @ tid {{{ RET v; Q }}}` are
  Trillium's `{{ P }} e @[tid] {{ RET v; Q }}`.
* `yesnoInvInner` is an `abbrev`, so that `iinv` can destruct the invariant body.
* Rocq's `yes_go_spec`/`no_go_spec` use `wp_atomic` + `iInv`; here `iinv` is applied directly
  to the (atomic) WP goal. The final step that deallocates the role is taken, as in Rocq, with
  `wp_step_fuel` + `sswp_pure_step` while the invariant is open.
-/

namespace Trillium.Fairis.Yesno

open Iris Iris.BI Iris.Std Iris.ProofMode ExclAuth
open Trillium Trillium.Fairness
open Trillium.HeapLang (Expr Val BaseLocale)
open Iris.HeapLang (Loc)
open Trillium.HeapLang (wp_cmpxchg_suc wp_cmpxchg_fail wp_alloc sswp_pure_step)

/-! ## The programs -/

@[rocq_alias trillium.fairis.yes_go]
def yesGo : Val := tl_val(
  rec yes_go n b :=
    (if cas(b, #true, #false) then n ← !n - #1 else #());
    if #0 < !n then yes_go n b else #())

@[rocq_alias trillium.fairis.yes]
def yes : Val := tl_val(λ N b, let n := alloc(N); v(&yesGo) n b)

@[rocq_alias trillium.fairis.no_go]
def noGo : Val := tl_val(
  rec no_go n b :=
    (if cas(b, #false, #true) then n ← !n - #1 else #());
    if #0 < !n then no_go n b else #())

@[rocq_alias trillium.fairis.no]
def no : Val := tl_val(λ N b, let n := alloc(N); v(&noGo) n b)

@[rocq_alias trillium.fairis.yesno.start]
def start : Val := tl_val(λ N, let b := alloc(#true); (fork(v(&yes) N b); fork(v(&no) N b)))

/-! ## The model -/

/-- The roles of the model. -/
@[rocq_alias trillium.fairis.YN]
inductive YN where
  | Y
  | No
  deriving Inhabited

@[rocq_alias trillium.fairis.YN_eqdec]
instance YN_eqdec : DecidableEq YN := fun a b => by
  cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)

/-- stdpp's `Countable YN` (encoding `Y ↦ 1`, `No ↦ 2`); it provides the order needed for
`GSet YN` and `GMap YN _`. -/
@[rocq_alias trillium.fairis.YN_countable]
instance YN_countable : Encodable YN where
  encode | .Y => 1 | .No => 2
  decode | 1 => some .Y | 2 => some .No | _ => none
  encodek a := by cases a <;> rfl

instance : Ord YN := ordOfEncodable
instance : Std.TransOrd YN := transOrd_ordOfEncodable
instance : Std.LawfulEqOrd YN := lawfulEqOrd_ordOfEncodable

attribute [rocq_alias trillium.fairis.YN_inhabited] instInhabitedYN

open YN

/-- The transitions of the model: the state is the counter and whose turn it is (`true`: yes). -/
@[rocq_alias trillium.fairis.yntrans]
inductive YnTrans : Nat × Bool → Option YN → Nat × Bool → Prop
  | yes_trans (n : Nat) : n > 0 → YnTrans (n, true) (some Y) (n, false)
  | yes_fail (n : Nat) : n > 1 → YnTrans (n, false) (some Y) (n, false)
  | no_trans (n : Nat) : YnTrans (n + 1, false) (some No) (n, true)
  | no_fail (n : Nat) : n > 0 → YnTrans (n, true) (some No) (n, true)

@[rocq_alias trillium.fairis.yn_live_roles]
def ynLiveRoles : Nat × Bool → GSet YN
  | (0, _) => ∅
  | (1, false) => {No}
  | _ => {No, Y}

@[rocq_alias trillium.fairis.yesno.live_spec_holds]
theorem live_spec_holds :
    ∀ s ρ s', YnTrans s (some ρ) s' → ρ ∈ ynLiveRoles s := by
  intro s ρ s' Htrans
  cases Htrans with
  | yes_trans n Hn =>
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp [ynLiveRoles]
  | yes_fail n Hn =>
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    simp [ynLiveRoles]
  | no_trans n =>
    cases n <;> simp [ynLiveRoles]
  | no_fail n Hn =>
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp [ynLiveRoles]

@[rocq_alias trillium.fairis.yesno.the_fair_model]
abbrev theFairModel : FairModel where
  fmstate := Nat × Bool
  fmrole := YN
  fmtrans := YnTrans
  liveRoles := ynLiveRoles
  fm_live_spec := live_spec_holds

@[rocq_alias trillium.fairis.yesno.the_model]
def theModel : LiveModel BaseLocale theFairModel where
  lmFl _ := 61

theorem GMap.erase_singleton {K V : Type _} [Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]
    (k : K) (v : V) : (GMap.singleton k v).erase k = ∅ := by
  apply Std.ExtTreeMap.ext_getElem?
  intro k'
  simp only [GMap.singleton, Std.ExtTreeMap.getElem?_erase, Std.ExtTreeMap.getElem?_insert,
    Std.ExtTreeMap.getElem?_empty]
  split <;> simp_all

theorem theModel_lmFl (s : theFairModel.fmstate) : theModel.lmFl s = 61 := rfl

/-! ## Ghost state -/

/-- Rocq `excl_authR natO`. -/
abbrev NatAuthF : COFE.OFunctorPre := constOF (ExclAuthR (A := DiscreteO Nat))
/-- Rocq `excl_authR boolO`. -/
abbrev BoolAuthF : COFE.OFunctorPre := constOF (ExclAuthR (A := DiscreteO Bool))

/-- The ghost state of the example, with the names of the two counters (Rocq `yesnoG`). -/
@[rocq_alias trillium.fairis.yesnoG]
class YesnoG (GF : BundledGFunctors) where
  yes_name : GName
  no_name : GName
  [yesno_n_G : ElemG GF NatAuthF]
  [yesno_f_G : ElemG GF BoolAuthF]

attribute [reducible, instance] YesnoG.yesno_n_G YesnoG.yesno_f_G

/-- The ghost state needed to allocate the ghost state of the example (Rocq `yesnoPreG`). -/
@[rocq_alias trillium.fairis.yesnoPreG]
class YesnoPreG (GF : BundledGFunctors) where
  yesno_PreG : ElemG GF NatAuthF
  yesno_f_PreG : ElemG GF BoolAuthF

attribute [reducible, instance] YesnoPreG.yesno_PreG YesnoPreG.yesno_f_PreG

#rocq_ignore trillium.fairis.«yesnoΣ»
  "Superseded by the `YesnoPreG`/`HeapGpreS` typeclasses on `BundledGFunctors` (no concrete `gFunctors` lists in iris-lean)."
#rocq_ignore trillium.fairis.«subG_yesnoΣ» "Superseded by Lean's direct `ElemG` typeclass synthesis."

section ghost

variable {GF : BundledGFunctors}

@[rocq_alias trillium.fairis.yesno.they_agree]
theorem they_agree [ElemG GF NatAuthF] (γ : GName) (N M : Nat) :
    ⊢ iOwn (GF := GF) (F := NatAuthF) γ (◯E (⟨N⟩ : DiscreteO Nat)) -∗
      iOwn (F := NatAuthF) γ (●E (⟨M⟩ : DiscreteO Nat)) -∗ ⌜M = N⌝ := by
  iintro HA HB
  icombine HB HA as H
  icases (iOwn_cmraValid.trans internalCmraValid_discrete.1) $$ H with %Hval
  ipureintro
  exact DiscreteO.eqv_inj (ExclAuth.agree Hval)

@[rocq_alias trillium.fairis.yesno.they_update]
theorem they_update [ElemG GF NatAuthF] (γ : GName) (N M P : Nat) :
    iOwn (GF := GF) (F := NatAuthF) γ (●E (⟨N⟩ : DiscreteO Nat)) ∗
      iOwn (F := NatAuthF) γ (◯E (⟨M⟩ : DiscreteO Nat)) ==∗
    iOwn (F := NatAuthF) γ (●E (⟨P⟩ : DiscreteO Nat)) ∗
      iOwn (F := NatAuthF) γ (◯E (⟨P⟩ : DiscreteO Nat)) := by
  simp only [← iOwn_op.to_eq]
  iapply iOwn_update ExclAuth.update

@[rocq_alias trillium.fairis.they_finished_update]
theorem they_finished_update [ElemG GF BoolAuthF] (γ : GName) (N M P : Bool) :
    iOwn (GF := GF) (F := BoolAuthF) γ (●E (⟨N⟩ : DiscreteO Bool)) ∗
      iOwn (F := BoolAuthF) γ (◯E (⟨M⟩ : DiscreteO Bool)) ==∗
    iOwn (F := BoolAuthF) γ (●E (⟨P⟩ : DiscreteO Bool)) ∗
      iOwn (F := BoolAuthF) γ (◯E (⟨P⟩ : DiscreteO Bool)) := by
  simp only [← iOwn_op.to_eq]
  iapply iOwn_update ExclAuth.update

end ghost

section proof

variable {GF : BundledGFunctors} [HeapGS theModel GF] [YesnoG GF]

/-- Rocq `Ns := nroot .@ "yes_no"`. -/
def Ns : Namespace := ndot nroot "yes_no"

@[rocq_alias trillium.fairis.yes_at]
def yesAt (n : Nat) : IProp GF :=
  iOwn (F := NatAuthF) (YesnoG.yes_name GF) (◯E (⟨n⟩ : DiscreteO Nat))
@[rocq_alias trillium.fairis.no_at]
def noAt (n : Nat) : IProp GF :=
  iOwn (F := NatAuthF) (YesnoG.no_name GF) (◯E (⟨n⟩ : DiscreteO Nat))

@[rocq_alias trillium.fairis.auth_yes_at]
def authYesAt (n : Nat) : IProp GF :=
  iOwn (F := NatAuthF) (YesnoG.yes_name GF) (●E (⟨n⟩ : DiscreteO Nat))
@[rocq_alias trillium.fairis.auth_no_at]
def authNoAt (n : Nat) : IProp GF :=
  iOwn (F := NatAuthF) (YesnoG.no_name GF) (●E (⟨n⟩ : DiscreteO Nat))

omit [HeapGS theModel GF] in
instance yesAt_timeless (n : Nat) : Timeless (yesAt (GF := GF) n) := by
  unfold yesAt; infer_instance
omit [HeapGS theModel GF] in
instance noAt_timeless (n : Nat) : Timeless (noAt (GF := GF) n) := by
  unfold noAt; infer_instance
omit [HeapGS theModel GF] in
instance authYesAt_timeless (n : Nat) : Timeless (authYesAt (GF := GF) n) := by
  unfold authYesAt; infer_instance
omit [HeapGS theModel GF] in
instance authNoAt_timeless (n : Nat) : Timeless (authNoAt (GF := GF) n) := by
  unfold authNoAt; infer_instance

omit [HeapGS theModel GF] in
@[rocq_alias trillium.fairis.yes_agree]
theorem yes_agree (N M : Nat) : ⊢ yesAt (GF := GF) N -∗ authYesAt M -∗ ⌜M = N⌝ :=
  they_agree _ N M

omit [HeapGS theModel GF] in
@[rocq_alias trillium.fairis.no_agree]
theorem no_agree (N M : Nat) : ⊢ noAt (GF := GF) N -∗ authNoAt M -∗ ⌜M = N⌝ :=
  they_agree _ N M

omit [HeapGS theModel GF] in
@[rocq_alias trillium.fairis.yes_update]
theorem yes_update (P N M : Nat) :
    authYesAt (GF := GF) M ∗ yesAt N ==∗ authYesAt P ∗ yesAt P :=
  they_update _ M N P

omit [HeapGS theModel GF] in
@[rocq_alias trillium.fairis.no_update]
theorem no_update (P N M : Nat) :
    authNoAt (GF := GF) M ∗ noAt N ==∗ authNoAt P ∗ noAt P :=
  they_update _ M N P

@[rocq_alias trillium.fairis.yesno_inv_inner]
abbrev yesnoInvInner (b : Loc) : IProp GF :=
  iprop(∃ (N : Nat) (B : Bool),
    ⌜(N, B) ≠ (0, false)⌝ ∗
    fragFreeRolesAre (GF := GF) (∅ : GSet theFairModel.fmrole) ∗
    fragModelIs (GF := GF) ((N, B) : theFairModel.fmstate) ∗ b ↦ .lit (.bool B) ∗
    if B then authYesAt N ∗ authNoAt N
    else authYesAt (N - 1) ∗ authNoAt N)

@[rocq_alias trillium.fairis.yesno_inv]
def yesnoInv (b : Loc) : IProp GF := inv Ns (yesnoInvInner b)

instance yesnoInv_persistent (b : Loc) : Persistent (yesnoInv (GF := GF) b) := by
  unfold yesnoInv; infer_instance

@[rocq_alias trillium.fairis.yes_go_spec]
theorem yes_go_spec (tid : BaseLocale) (n b : Loc) (N : Nat) (f : Nat) (Hf : f > 40) :
    {{ iprop(yesnoInv (GF := GF) b ∗ (tid ↦M GMap.singleton Y f) ∗ n ↦ .lit (.int N) ∗
        ⌜N > 0⌝ ∗ yesAt N) }}
      tl(v(&yesGo) #(.loc n) #(.loc b)) @[tid]
    {{ RET .lit .unit; tid ↦M ∅ }} := by
  iintro %Φ ⟨#Hinv, Hf, HnN, %HN, Hyes⟩ Hk
  iloeb as Hg generalizing %N %f %Hf %HN
  unfold yesGo
  wp_pures
  wp_bind (cmpXchg(_, _, _))
  unfold yesnoInv
  iinv Hinv with ⟨%M, %B, >%Hnever, >HFR, >Hmod, >Bb, Hauths⟩ Hclose
  cases B with
  | true =>
    simp only [↓reduceIte]
    icases Hauths with ⟨>Hay, >Han⟩
    ihave %Heq := yes_agree N M $$ Hyes Hay
    subst Heq
    obtain rfl | rfl | HM : M = 0 ∨ M = 1 ∨ M ≥ 2 := by omega
    · omega
    · iapply wp_step_model_singlerole _ tid Y (f - 3) ∅ ((1, true) : theFairModel.fmstate) (1, false)
        _ _ _ rfl (YnTrans.yes_trans 1 (by omega)) (by intro x hx; simp_all [ynLiveRoles])
        $$ Hmod Hf HFR
      iapply wp_cmpxchg_suc _ _ b (.lit (.bool true)) _ _ _ rfl (by decide) $$ Bb
      inext
      iintro Hb Hmod Hf HFR
      imod yes_update 0 1 1 $$ [Hay Hyes] with ⟨Hay, Hyes⟩
      · iframe
      wp_pures
      imod Hclose $$ [Hmod Hb Hay Han HFR] with -
      · inext
        iexists 1, false
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.sub_self]
        iframe
        ipureintro
        decide
      imodintro
      simp only [theModel_lmFl]
      wp_load
      wp_store
      wp_load
      wp_pures
      simp only [decide_false]
      iinv Hinv with ⟨%M, %B, >%Hnever', >HFR, >Hmod, >Hb, Hauths⟩ Hclose
      cases B with
      | true =>
        simp only [↓reduceIte]
        icases Hauths with ⟨>Hay, >Han⟩
        ihave %Heq := yes_agree 0 M $$ Hyes Hay
        subst Heq
        icases (has_fuels_gt_1 _ _ (by solve_fuel_positive)).1 $$ Hf with Hf
        simpl_has_fuels
        iapply wp_step_fuel _ _ _ _ _ _ (GMap.singleton_ne_empty _ _) $$ [Hf]
        · inext; iexact Hf
        iapply sswp_pure_step _ _ _ _ _ _ inferInstance trivial
        inext
        iintro Hf
        imod has_fuels_dealloc _ tid _ Y ((0, true)) (by simp [ynLiveRoles]) $$ Hmod Hf
          with ⟨Hmod, Hf⟩
        wp_pures
        imod Hclose $$ [Hmod Hb Hay Han HFR] with -
        · inext
          iexists 0, true
          simp only [↓reduceIte]
          iframe
          ipureintro
          decide
        imodintro
        rw [GMap.erase_singleton]
        iapply Hk $$ Hf
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        icases Hauths with ⟨>Hay, >Han⟩
        ihave %Heq := yes_agree 0 (M - 1) $$ Hyes Hay
        obtain rfl : M = 1 := by
          rcases M with _ | _ | M
          · exact absurd rfl Hnever'
          · rfl
          · simp at Heq
        icases (has_fuels_gt_1 _ _ (by solve_fuel_positive)).1 $$ Hf with Hf
        simpl_has_fuels
        iapply wp_step_fuel _ _ _ _ _ _ (GMap.singleton_ne_empty _ _) $$ [Hf]
        · inext; iexact Hf
        iapply sswp_pure_step _ _ _ _ _ _ inferInstance trivial
        inext
        iintro Hf
        imod has_fuels_dealloc _ tid _ Y ((1, false)) (by simp [ynLiveRoles]) $$ Hmod Hf
          with ⟨Hmod, Hf⟩
        wp_pures
        imod Hclose $$ [Hmod Hb Hay Han HFR] with -
        · inext
          iexists 1, false
          simp only [Bool.false_eq_true, ↓reduceIte]
          iframe
          ipureintro
          decide
        imodintro
        rw [GMap.erase_singleton]
        iapply Hk $$ Hf
    · iapply wp_step_model_singlerole _ tid Y (f - 3) ∅ ((M, true) : theFairModel.fmstate)
        (M, false) _ _ _ rfl (YnTrans.yes_trans M (by omega))
        (by obtain ⟨M, rfl⟩ : ∃ k, M = k + 2 := ⟨M - 2, by omega⟩
            intro x hx; simp_all [ynLiveRoles])
        $$ Hmod Hf HFR
      iapply wp_cmpxchg_suc _ _ b (.lit (.bool true)) _ _ _ rfl (by decide) $$ Bb
      inext
      iintro Hb Hmod Hf HFR
      imod yes_update (M - 1) M M $$ [Hay Hyes] with ⟨Hay, Hyes⟩
      · iframe
      wp_pures
      imod Hclose $$ [Hmod Hb Hay Han HFR] with -
      · inext
        iexists M, false
        simp only [Bool.false_eq_true, ↓reduceIte]
        iframe
        ipureintro
        intro h; cases h; omega
      imodintro
      simp only [theModel_lmFl]
      wp_load
      wp_store
      wp_load
      wp_pures
      have hM : ((M : Int) - 1) = ((M - 1 : Nat) : Int) := by omega
      have hd : decide ((0 : Int) < ((M - 1 : Nat) : Int)) = true := by
        simp only [decide_eq_true_eq]; omega
      simp only [hM]
      simp only [hd]
      wp_if
      iapply Hg $$ %(M - 1) %_ [] [] Hf HnN Hyes [Hk]
      · ipureintro; omega
      · ipureintro; omega
      · inext; iexact Hk
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hauths with ⟨>Hay, >Han⟩
    ihave %Heq := yes_agree N (M - 1) $$ Hyes Hay
    obtain rfl : M = N + 1 := by omega
    iapply wp_step_model_singlerole _ tid Y (f - 3) ∅ ((N + 1, false) : theFairModel.fmstate)
      (N + 1, false) _ _ _ rfl (YnTrans.yes_fail (N + 1) (by omega)) (fun _ hx => hx)
      $$ Hmod Hf HFR
    iapply wp_cmpxchg_fail _ _ b 1 (.lit (.bool false)) _ _ _ (by decide) (by decide) $$ Bb
    inext
    iintro Hb Hmod Hf HFR
    wp_pures
    imod Hclose $$ [Hmod Hb Hay Han HFR] with -
    · inext
      iexists N + 1, false
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe
      ipureintro
      intro h; cases h
    imodintro
    simp only [theModel_lmFl]
    wp_load
    wp_pures
    have hd : decide ((0 : Int) < (N : Int)) = true := by
      simp only [decide_eq_true_eq]; omega
    simp only [hd]
    wp_if
    iapply Hg $$ %N %_ [] [] Hf HnN Hyes [Hk]
    · ipureintro; omega
    · ipureintro; omega
    · inext; iexact Hk

@[rocq_alias trillium.fairis.yes_spec]
theorem yes_spec (tid : BaseLocale) (b : Loc) (N : Nat) (f : Nat) (Hf : f > 50) :
    {{ iprop(yesnoInv (GF := GF) b ∗ (tid ↦M GMap.singleton Y f) ∗ ⌜N > 0⌝ ∗ yesAt N) }}
      tl(v(&yes) #(.int N) #(.loc b)) @[tid]
    {{ RET .lit .unit; tid ↦M ∅ }} := by
  iintro %Φ ⟨#Hinv, Hf, %HN, Hyes⟩ Hk
  unfold yes
  wp_pures
  wp_bind (allocn(_, _))
  icases (has_fuels_gt_1 _ _ (by solve_fuel_positive)).1 $$ Hf with Hf
  simpl_has_fuels
  iapply wp_step_fuel _ _ _ _ _ _ (GMap.singleton_ne_empty _ _) $$ [Hf]
  · inext; iexact Hf
  iapply Trillium.HeapLang.wp_alloc
  inext
  iintro %n HnN - Hf
  simpl_has_fuels
  wp_pures
  wp_pures
  iapply yes_go_spec tid n b N (f - 6) (by omega) $$ [Hf HnN Hyes] [Hk]
  · iframe
    isplit
    · iexact Hinv
    · ipureintro; exact HN
  · inext
    iexact Hk

@[rocq_alias trillium.fairis.no_go_spec]
theorem no_go_spec (tid : BaseLocale) (n b : Loc) (N : Nat) (f : Nat) (Hf : f > 40) :
    {{ iprop(yesnoInv (GF := GF) b ∗ (tid ↦M GMap.singleton No f) ∗ n ↦ .lit (.int N) ∗
        ⌜N > 0⌝ ∗ noAt N) }}
      tl(v(&noGo) #(.loc n) #(.loc b)) @[tid]
    {{ RET .lit .unit; tid ↦M ∅ }} := by
  iintro %Φ ⟨#Hinv, Hf, HnN, %HN, Hno⟩ Hk
  iloeb as Hg generalizing %N %f %Hf %HN
  unfold noGo
  wp_pures
  wp_bind (cmpXchg(_, _, _))
  unfold yesnoInv
  iinv Hinv with ⟨%M, %B, >%Hnever, >HFR, >Hmod, >Bb, Hauths⟩ Hclose
  cases B with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hauths with ⟨>Hay, >Han⟩
    ihave %Heq := no_agree N M $$ Hno Han
    subst Heq
    obtain rfl | rfl | HM : M = 0 ∨ M = 1 ∨ M ≥ 2 := by omega
    · omega
    · iapply wp_step_model_singlerole _ tid No (f - 3) ∅ ((1, false) : theFairModel.fmstate)
        (0, true) _ _ _ rfl (YnTrans.no_trans 0) (by intro x hx; simp_all [ynLiveRoles])
        $$ Hmod Hf HFR
      iapply wp_cmpxchg_suc _ _ b (.lit (.bool false)) _ _ _ rfl (by decide) $$ Bb
      inext
      iintro Hb Hmod Hf HFR
      imod no_update 0 1 1 $$ [Han Hno] with ⟨Han, Hno⟩
      · iframe
      wp_pures
      imod Hclose $$ [Hmod Hb Hay Han HFR] with -
      · inext
        iexists 0, true
        simp only [↓reduceIte, Nat.sub_self]
        iframe
        ipureintro
        decide
      imodintro
      simp only [theModel_lmFl]
      wp_load
      wp_store
      wp_load
      wp_pures
      simp only [decide_false]
      iinv Hinv with ⟨%M, %B, >%Hnever', >HFR, >Hmod, >Hb, Hauths⟩ Hclose
      cases B with
      | true =>
        simp only [↓reduceIte]
        icases Hauths with ⟨>Hay, >Han⟩
        ihave %Heq := no_agree 0 M $$ Hno Han
        subst Heq
        icases (has_fuels_gt_1 _ _ (by solve_fuel_positive)).1 $$ Hf with Hf
        simpl_has_fuels
        iapply wp_step_fuel _ _ _ _ _ _ (GMap.singleton_ne_empty _ _) $$ [Hf]
        · inext; iexact Hf
        iapply sswp_pure_step _ _ _ _ _ _ inferInstance trivial
        inext
        iintro Hf
        imod has_fuels_dealloc _ tid _ No ((0, true)) (by simp [ynLiveRoles]) $$ Hmod Hf
          with ⟨Hmod, Hf⟩
        wp_pures
        imod Hclose $$ [Hmod Hb Hay Han HFR] with -
        · inext
          iexists 0, true
          simp only [↓reduceIte]
          iframe
          ipureintro
          decide
        imodintro
        rw [GMap.erase_singleton]
        iapply Hk $$ Hf
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        icases Hauths with ⟨>Hay, >Han⟩
        ihave %Heq := no_agree 0 M $$ Hno Han
        subst Heq
        exact absurd rfl Hnever'
    · obtain ⟨K, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
      iapply wp_step_model_singlerole _ tid No (f - 3) ∅ ((K + 1, false) : theFairModel.fmstate)
        (K, true) _ _ _ rfl (YnTrans.no_trans K)
        (by obtain ⟨K, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
            intro x hx; simp_all [ynLiveRoles])
        $$ Hmod Hf HFR
      iapply wp_cmpxchg_suc _ _ b (.lit (.bool false)) _ _ _ rfl (by decide) $$ Bb
      inext
      iintro Hb Hmod Hf HFR
      imod no_update K (K + 1) (K + 1) $$ [Han Hno] with ⟨Han, Hno⟩
      · iframe
      wp_pures
      imod Hclose $$ [Hmod Hb Hay Han HFR] with -
      · inext
        iexists K, true
        simp only [↓reduceIte, Nat.add_sub_cancel]
        iframe
        ipureintro
        intro h; cases h
      imodintro
      simp only [theModel_lmFl]
      wp_load
      wp_store
      wp_load
      wp_pures
      have hM : (((K + 1 : Nat) : Int) - 1) = (K : Int) := by omega
      have hd : decide ((0 : Int) < (K : Int)) = true := by
        simp only [decide_eq_true_eq]; omega
      simp only [hM]
      simp only [hd]
      wp_if
      iapply Hg $$ %K %_ [] [] Hf HnN Hno [Hk]
      · ipureintro; omega
      · ipureintro; omega
      · inext; iexact Hk
  | true =>
    simp only [↓reduceIte]
    icases Hauths with ⟨>Hay, >Han⟩
    ihave %Heq := no_agree N M $$ Hno Han
    subst Heq
    iapply wp_step_model_singlerole _ tid No (f - 3) ∅ ((M, true) : theFairModel.fmstate)
      (M, true) _ _ _ rfl (YnTrans.no_fail M (by omega)) (fun _ hx => hx)
      $$ Hmod Hf HFR
    iapply wp_cmpxchg_fail _ _ b 1 (.lit (.bool true)) _ _ _ (by decide) (by decide) $$ Bb
    inext
    iintro Hb Hmod Hf HFR
    wp_pures
    imod Hclose $$ [Hmod Hb Hay Han HFR] with -
    · inext
      iexists M, true
      simp only [↓reduceIte]
      iframe
      ipureintro
      intro h; cases h
    imodintro
    simp only [theModel_lmFl]
    wp_load
    wp_pures
    have hd : decide ((0 : Int) < (M : Int)) = true := by
      simp only [decide_eq_true_eq]; omega
    simp only [hd]
    wp_if
    iapply Hg $$ %M %_ [] [] Hf HnN Hno [Hk]
    · ipureintro; omega
    · ipureintro; omega
    · inext; iexact Hk

@[rocq_alias trillium.fairis.no_spec]
theorem no_spec (tid : BaseLocale) (b : Loc) (N : Nat) (f : Nat) (Hf : f > 50) :
    {{ iprop(yesnoInv (GF := GF) b ∗ (tid ↦M GMap.singleton No f) ∗ ⌜N > 0⌝ ∗ noAt N) }}
      tl(v(&no) #(.int N) #(.loc b)) @[tid]
    {{ RET .lit .unit; tid ↦M ∅ }} := by
  iintro %Φ ⟨#Hinv, Hf, %HN, Hno⟩ Hk
  unfold no
  wp_pures
  wp_bind (allocn(_, _))
  icases (has_fuels_gt_1 _ _ (by solve_fuel_positive)).1 $$ Hf with Hf
  simpl_has_fuels
  iapply wp_step_fuel _ _ _ _ _ _ (GMap.singleton_ne_empty _ _) $$ [Hf]
  · inext; iexact Hf
  iapply Trillium.HeapLang.wp_alloc
  inext
  iintro %n HnN - Hf
  simpl_has_fuels
  wp_pures
  wp_pures
  iapply no_go_spec tid n b N (f - 6) (by omega) $$ [Hf HnN Hno] [Hk]
  · iframe
    isplit
    · iexact Hinv
    · ipureintro; exact HN
  · inext
    iexact Hk

end proof

section proof_start

theorem fuels_split (x : Nat) :
    ((GMap.singleton No x).insert Y x : GMap YN Nat) = GMap.singleton No x ∪ GMap.singleton Y x := by
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  cases k <;> simp [GMap.singleton] <;> rfl

theorem fuels_disj (x y : Nat) : GMap.Disjoint (GMap.singleton No x : GMap YN Nat) (GMap.singleton Y y) := by
  rw [GMap.disjoint_iff_mem]
  intro k hk hk'
  simp [GMap.singleton] at hk hk'
  subst hk; cases hk'

theorem empty_union_singleton (x : Nat) :
    (∅ : GMap YN Nat) ∪ GMap.singleton No x = GMap.singleton No x := by
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  simp [Std.ExtTreeMap.getElem?_union]

variable {GF : BundledGFunctors} [HeapGS theModel GF] [YesnoPreG GF]

@[rocq_alias trillium.fairis.yesno.start_spec]
theorem start_spec (tid : BaseLocale) (N : Nat) (f : Nat) (Hf : f > 60) :
    {{ iprop(fragModelIs (GF := GF) ((N, true) : theFairModel.fmstate) ∗
        fragFreeRolesAre (GF := GF) (∅ : GSet theFairModel.fmrole) ∗
        (tid ↦M (GMap.singleton No f).insert Y f) ∗ ⌜N > 0⌝) }}
      tl(v(&start) #(.int N)) @[tid]
    {{ RET .lit .unit; tid ↦M ∅ }} := by
  iintro %Φ ⟨Hst, HFR, Hf, %HN⟩ Hk
  unfold start
  wp_pures
  wp_bind (allocn(_, _))
  icases (has_fuels_gt_1 _ _ (by solve_fuel_positive)).1 $$ Hf with Hf
  simpl_has_fuels
  iapply wp_step_fuel _ _ _ _ _ _ (GMap.insert_ne_empty _ _ _) $$ [Hf]
  · inext; iexact Hf
  iapply Trillium.HeapLang.wp_alloc
  inext
  iintro %l Hl - Hf
  simpl_has_fuels
  wp_pures
  imod iOwn_alloc (F := NatAuthF) ((●E (⟨N⟩ : DiscreteO Nat)) • ◯E (⟨N⟩ : DiscreteO Nat)) ExclAuth.valid
    with ⟨%γy, Hya⟩
  icases iOwn_op.1 $$ Hya with ⟨Hyauth, Hyfrag⟩
  imod iOwn_alloc (F := NatAuthF) ((●E (⟨N⟩ : DiscreteO Nat)) • ◯E (⟨N⟩ : DiscreteO Nat)) ExclAuth.valid
    with ⟨%γn, Hna⟩
  icases iOwn_op.1 $$ Hna with ⟨Hnauth, Hnfrag⟩
  let _ : YesnoG GF := { yes_name := γy, no_name := γn }
  imod inv_alloc Ns ⊤ (yesnoInvInner (GF := GF) l) $$ [Hst Hl HFR Hyauth Hnauth] with #Hinv
  · inext
    iexists N, true
    simp only [↓reduceIte]
    unfold authYesAt authNoAt
    iframe
    ipureintro
    intro h; cases h
  wp_pures
  wp_bind (fork(_))
  icases (has_fuels_gt_1 _ _ (by solve_fuel_positive)).1 $$ Hf with Hf
  simpl_has_fuels
  rw [fuels_split]
  iapply wp_role_fork _ tid _ _ _ (GMap.singleton No (f - 5)) (GMap.singleton Y (f - 5))
    (fuels_disj _ _) (by rw [← fuels_split]; exact GMap.insert_ne_empty _ _ _)
    $$ Hf [Hyfrag] [Hnfrag Hk]
  · iintro %tid' !> Hf
    iapply yes_spec tid' l N (f - 5) (by omega) $$ [Hf Hyfrag] []
    · unfold yesnoInv yesAt
      iframe
      isplit
      · iexact Hinv
      · ipureintro; exact HN
    · inext
      iintro H
      iexact H
  inext
  iintro Hf
  imodintro
  wp_pures
  icases (has_fuels_gt_1 _ _ (by solve_fuel_positive)).1 $$ Hf with Hf
  simpl_has_fuels
  rw [← empty_union_singleton]
  iapply wp_role_fork _ tid _ _ _ ∅ (GMap.singleton No (f - 8))
    (by rw [GMap.disjoint_iff_mem]; intro k hk; simp at hk)
    (by rw [empty_union_singleton]; exact GMap.singleton_ne_empty _ _)
    $$ Hf [Hnfrag] [Hk]
  · iintro %tid' !> Hf
    iapply no_spec tid' l N (f - 8) (by omega) $$ [Hf Hnfrag] []
    · unfold yesnoInv noAt
      iframe
      isplit
      · iexact Hinv
      · ipureintro; exact HN
    · inext
      iintro H
      iexact H
  inext
  iintro Hf
  imodintro
  iapply Hk $$ Hf

end proof_start

end Trillium.Fairis.Yesno
