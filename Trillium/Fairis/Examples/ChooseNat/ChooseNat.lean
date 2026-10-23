/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.Fairis.FairTermination
import Trillium.Fairis.ProofMode
import Trillium.HeapLang.Notation
import Iris.Algebra.Lib.ExclAuth
import Iris.Instances.Lib.Invariants

/-!
# The `choose_nat` example
Port of `fairis/examples/choose_nat/choose_nat.v`.

The program `choose_nat_prog l` stores a non-deterministically chosen positive natural number
into `l` and then decrements it down to `0`. We define a fair model `cnFairModel` (states
`CN.start` and `CN.n n`) of which it is a refinement, show that the model is fairly terminating
(`cn_model_terminates`), and verify the program against the live model `cnModel`
(`choose_nat_spec`).

## Representation

* Rocq's `unit` role type is Lean's `Unit`; the `GSet Unit` needs `Std.LawfulEqOrd Unit`, provided
  below (core only provides `Ord Unit`/`Std.TransOrd Unit`).
* Rocq's `ZO` (Leibniz OFE on `Z`) is `DiscreteO Int`, `excl_authR ZO` is `ExclAuthR (A := IntO)`.
* `choose_natΣ`/`subG_choosenatΣ` are subsumed by `ElemG` typeclass synthesis (as for
  `heapΣ` in `Trillium/Fairis/HeapLangLM.lean`).
* stdpp's `h !!! l` (total lookup with default `#()`) is `h.getD l default`.
-/

set_option linter.unusedSectionVars false

namespace Trillium.Fairis.ChooseNat

open Iris Iris.BI Iris.Std Iris.ProofMode Iris.OFE
open Trillium Trillium.HeapLang Trillium.Fairness
open Iris.HeapLang (Loc HeapF)

/-! ## The program -/

/-- Recursion is "off by one" to allow immediate termination after storing `0`. -/
@[rocq_alias trillium.fairis.decr_loop_prog]
def decrLoopProg (l : Loc) : Val := tl_val(
  rec go _ :=
    let x := !#l;
    if #0 < x then ((#l ← x - #1); go #()) else #())

@[rocq_alias trillium.fairis.choose_nat_prog]
def chooseNatProg (l : Loc) : Val := tl_val(
  λ _,
    (#l ← chooseNat() + #1);
    v(&(decrLoopProg l)) #())

/-! ## The model -/

/-- The model state. -/
@[rocq_alias trillium.fairis.CN]
inductive CN where
  | start
  | n (n : Nat)
  deriving DecidableEq

/-- A mapping of model state to "program state". -/
@[rocq_alias trillium.fairis.CN_Z]
def cnZ : CN → Int
  | .start => -1
  | .n n => n

attribute [rocq_alias trillium.fairis.CN_eqdec] instDecidableEqCN

@[rocq_alias trillium.fairis.CN_inhabited]
instance cnInhabited : Inhabited CN := ⟨.start⟩

/-- `Unit` keys for `GSet Unit` (the comparison on `Unit` is trivially lawful). -/
instance unitLawfulEqOrd : Std.LawfulEqOrd Unit where
  compare_self := rfl
  eq_of_compare _ := rfl

@[rocq_alias trillium.fairis.cntrans]
inductive CnTrans : CN → Option Unit → CN → Prop
  | start_trans (n : Nat) : CnTrans .start (some ()) (.n n)
  | decr_trans (n : Nat) : CnTrans (.n (n + 1)) (some ()) (.n n)

/-- Free construction of the active labels on each state by `CnTrans`. -/
@[rocq_alias trillium.fairis.cn_live_roles]
def cnLiveRoles : CN → GSet Unit
  | .n 0 => ∅
  | _ => {()}

@[rocq_alias trillium.fairis.cn_live_spec_holds]
theorem cn_live_spec_holds (s : CN) (ρ : Unit) (s' : CN) :
    CnTrans s (some ρ) s' → ρ ∈ cnLiveRoles s := by
  intro h
  cases h <;> simp [cnLiveRoles]

@[rocq_alias trillium.fairis.cn_fair_model]
abbrev cnFairModel : FairModel where
  fmstate := CN
  fmrole := Unit
  fmtrans := CnTrans
  liveRoles := cnLiveRoles
  fm_live_spec := cn_live_spec_holds

/-! ## The model is fairly terminating -/

@[rocq_alias trillium.fairis.cn_order]
inductive CnOrder : CN → CN → Prop
  | start (cn : CN) : CnOrder cn .start
  | n (n1 n2 : Nat) : n1 ≤ n2 → CnOrder (.n n1) (.n n2)

@[rocq_alias trillium.fairis.choose_nat.the_order_po]
instance the_order_po : IsPartialOrder CN CnOrder where
  refl := by
    intro a
    cases a
    · exact .start _
    · exact .n _ _ (Nat.le_refl _)
  trans := by
    intro a b c h1 h2
    cases h2 with
    | start => exact .start _
    | n n2 n3 h23 =>
      cases h1 with
      | n n1 _ h12 => exact .n _ _ (Nat.le_trans h12 h23)
  antisymm := by
    intro a b h1 h2
    cases h1 with
    | start => cases h2; rfl
    | n n1 n2 h12 =>
      cases h2 with
      | n _ _ h21 => rw [Nat.le_antisymm h12 h21]

@[rocq_alias trillium.fairis.cn_decreasing_role]
def cnDecreasingRole (_s : cnFairModel.fmstate) : Unit := ()

@[rocq_alias trillium.fairis.cn_model_terminates]
instance cn_model_terminates : FairTerminatingModel cnFairModel where
  ftmLeq := CnOrder
  ftm_order := (inferInstance : IsPreorder CN CnOrder)
  ftm_wf := by
    have HN : ∀ n, Acc (fun a b => CnOrder a b ∧ ¬ CnOrder b a) (CN.n n) := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n IHn =>
        constructor
        rintro cn ⟨Hcn1, Hcn2⟩
        cases Hcn1 with
        | n n1 _ h =>
          have : n1 < n := by
            rcases Nat.lt_or_eq_of_le h with h | rfl
            · exact h
            · exact absurd (.n _ _ (Nat.le_refl _)) Hcn2
          exact IHn n1 this
    constructor
    intro cn
    cases cn with
    | start =>
      constructor
      rintro cn ⟨Hc1, Hc2⟩
      cases cn with
      | start => exact absurd (.start _) Hc2
      | n n => exact HN n
    | n n => exact HN n
  ftmDecreasingRole := cnDecreasingRole
  ftm_decr := by
    rintro cn ⟨ρ', cn', Htrans⟩
    refine ⟨?_, ?_⟩
    · change () ∈ cnLiveRoles cn
      cases Htrans <;> simp [cnLiveRoles]
    · intro cn'' Htrans'
      change CnTrans cn (some ()) cn'' at Htrans'
      cases Htrans' with
      | start_trans n =>
        refine ⟨.start _, fun h => ?_⟩
        cases h
      | decr_trans n =>
        refine ⟨.n _ _ (Nat.le_succ n), fun h => ?_⟩
        cases h with
        | n _ _ h => omega
  ftm_decreasing_role_preserved := by
    intro _ _ _ _ _
    rfl
  ftm_notinc := by
    intro cn1 ρ cn2 Htrans
    change CnTrans cn1 ρ cn2 at Htrans
    cases Htrans with
    | start_trans n => exact .start _
    | decr_trans n => exact .n _ _ (Nat.le_succ n)

@[rocq_alias trillium.fairis.cn_model]
def cnModel : LiveModel BaseLocale cnFairModel where
  lmFl _ := 40

/-- Additional restriction on the simulation relation, to obtain finite branching. -/
@[rocq_alias trillium.fairis.«ξ_cn»]
def ξCn (l : Loc) (extr : ExecutionTrace Expr)
    (auxtr : FiniteTrace cnFairModel.fmstate (Option cnFairModel.fmrole)) : Prop :=
  ∃ cn : CN, extr.last.2.heap.getD l default = .lit (.int (cnZ cn)) ∧ auxtr.last = cn

/-! ## Verification of the program -/

/-- Rocq `ZO`: the discrete OFE on `Int`. -/
abbrev IntO := DiscreteO Int

/-- The ghost state of the example (Rocq `choose_natG`). -/
@[rocq_alias trillium.fairis.choose_natG]
class ChooseNatG (GF : BundledGFunctors) where
  choose_nat_G : ElemG GF (constOF (ExclAuth.ExclAuthR (A := IntO)))

attribute [reducible, instance] ChooseNatG.choose_nat_G

#rocq_ignore trillium.fairis.«choose_natΣ»
  "Superseded by the `ChooseNatG`/`HeapGpreS` typeclasses on `BundledGFunctors` (iris-lean has no concrete `invΣ`)."
#rocq_ignore trillium.fairis.«subG_choosenatΣ» "Superseded by Lean's direct `ElemG` typeclass synthesis."

@[rocq_alias trillium.fairis.Ns]
def Ns : Namespace := nroot .@ "choose_nat"

section proof

open ExclAuth

variable {GF : BundledGFunctors} [HeapGS cnModel GF] [ChooseNatG GF]

/-- Ownership of the `excl_auth` ghost variable (abbreviation used in this file). -/
abbrev ownE (γ : GName) (a : ExclAuthR (A := IntO)) : IProp GF :=
  iOwn (F := constOF (ExclAuthR (A := IntO))) γ a

/-- Rocq `own_valid_2 … excl_auth_agree_L`. -/
theorem ownE_agree (γ : GName) (a b : Int) :
    ⊢ ownE (GF := GF) γ (●E (⟨a⟩ : IntO)) -∗ ownE γ (◯E (⟨b⟩ : IntO)) -∗ ⌜a = b⌝ := by
  iintro H1 H2
  icases iOwn_cmraValid_op $$ [$H1 $H2] with %Hvalid
  ipureintro
  exact DiscreteO.eqv_inj (ExclAuth.agree Hvalid)

/-- Rocq `own_update_2 … excl_auth_update`. -/
theorem ownE_update (γ : GName) (a b c : Int) :
    ⊢ ownE (GF := GF) γ (●E (⟨a⟩ : IntO)) -∗ ownE γ (◯E (⟨b⟩ : IntO)) ==∗
      ownE γ (●E (⟨c⟩ : IntO)) ∗ ownE γ (◯E (⟨c⟩ : IntO)) := by
  iintro H1 H2
  ihave H : ownE (GF := GF) γ ((●E (⟨a⟩ : IntO)) • ◯E (⟨b⟩ : IntO)) $$ [H1 H2]
  · iapply iOwn_op.2
    iframe
  imod iOwn_update ExclAuth.update $$ H with H
  icases iOwn_op.1 $$ H with ⟨H1, H2⟩
  imodintro
  iframe

/-- The invariant, from which `ξCn` is eventually derived. -/
@[rocq_alias trillium.fairis.choose_nat_inv_inner]
def chooseNatInvInner (γ : GName) (l : Loc) : IProp GF :=
  iprop(∃ cn : CN, fragModelIs (GF := GF) (cn : cnFairModel.fmstate) ∗
    l ↦ .lit (.int (cnZ cn)) ∗
    ownE γ (●E (⟨cnZ cn⟩ : IntO)))

instance chooseNatInvInner_timeless (γ : GName) (l : Loc) :
    Timeless (chooseNatInvInner (GF := GF) γ l) := by
  unfold chooseNatInvInner
  have : ∀ cn : CN, Timeless (fragModelIs (GF := GF) (cn : cnFairModel.fmstate)) := by
    intro cn; infer_instance
  have : ∀ cn : CN, Timeless iprop(l ↦ Val.lit (.int (cnZ cn))) := by
    intro cn; infer_instance
  have : ∀ cn : CN, Timeless (ownE (GF := GF) γ (●E (⟨cnZ cn⟩ : IntO))) := by
    intro cn; infer_instance
  infer_instance

@[rocq_alias trillium.fairis.choose_nat_inv]
def chooseNatInv (γ : GName) (l : Loc) : IProp GF :=
  inv Ns (chooseNatInvInner γ l)

/-- Opening the invariant (Rocq `iInv Ns as ">HI" "Hclose"`). -/
theorem chooseNatInv_acc (γ : GName) (l : Loc) :
    ⊢ chooseNatInv (GF := GF) γ l ={⊤, ⊤ \ ↑Ns}=∗
      chooseNatInvInner γ l ∗ (chooseNatInvInner γ l ={⊤ \ ↑Ns, ⊤}=∗ True) :=
  inv_acc_timeless CoPset.subseteq_top

instance chooseNatInv_persistent (γ : GName) (l : Loc) :
    Persistent (chooseNatInv (GF := GF) γ l) := by
  unfold chooseNatInv
  infer_instance

@[rocq_alias trillium.fairis.decr_loop_spec]
theorem decr_loop_spec (γ : GName) (tid : BaseLocale) (l : Loc) (n f : Nat) :
    7 ≤ f → f ≤ 38 →
    ⊢ chooseNatInv (GF := GF) γ l -∗
      iprop({{ (tid ↦M GMap.singleton () f) ∗ fragFreeRolesAre (GF := GF) ∅ ∗
          ownE γ (◯E (⟨(n : Int)⟩ : IntO)) }}
        tl(v(&(decrLoopProg l)) #()) @[tid] ⊤
        {{ RET .lit .unit; tid ↦M ∅ }}) := by
  intro Hle1 Hle2
  induction n generalizing f with
  | zero =>
    iintro #HI !> %Φ ⟨Hf, Hr, Hm⟩ HΦ
    wp_lam
    -- Load - with invariant
    wp_bind (!_)
    iapply wp_atomic (E₂ := ⊤ \ ↑Ns)
    imod chooseNatInv_acc γ l $$ HI with ⟨HInv, Hclose⟩
    iunfold chooseNatInvInner at HInv
    icases HInv with ⟨%cn, Hs, Hl, Hcn⟩
    ihave %Hvalid := ownE_agree γ _ _ $$ Hcn Hm
    imodintro
    wp_load
    imod Hclose $$ [Hs Hl Hcn] with -
    · iunfold chooseNatInvInner
      iexists cn
      iframe
    imodintro
    rw [Hvalid]
    iapply wp_preStep
    wp_pures
    isimp only [decide_false]
    wp_pures
    imodintro
    unfold preStep
    iintro %extr %atr Hsi
    imod chooseNatInv_acc γ l $$ HI with ⟨HInv, Hclose⟩
    iunfold chooseNatInvInner at HInv
    icases HInv with ⟨%cn', Hs, Hl, Hcn⟩
    ihave %Hvalid' := ownE_agree γ _ _ $$ Hcn Hm
    obtain rfl : cn' = .n 0 := by
      cases cn' with
      | start => simp [cnZ] at Hvalid'
      | n k => simp only [cnZ] at Hvalid'; congr 1; omega
    imod preStep_elim (E := ⊤ \ ↑Ns)
      (P := iprop(fragModelIs (GF := GF) (CN.n 0 : cnFairModel.fmstate) ∗
        (tid ↦M (GMap.singleton () (f - 6)).erase ()))) extr atr $$ Hsi [Hs Hf] with ⟨Hsi, Hs, Hf⟩
    · iapply has_fuels_dealloc (⊤ \ ↑Ns) tid _ () (CN.n 0 : cnFairModel.fmstate)
        (by simp [cnLiveRoles]) $$ Hs Hf
    imod Hclose $$ [Hs Hl Hcn] with -
    · iunfold chooseNatInvInner
      iexists CN.n 0
      iframe
    imodintro
    iframe Hsi
    iapply HΦ
    have Herase : (GMap.singleton () (f - 6)).erase () = (∅ : GMap Unit Nat) := by
      apply Std.ExtTreeMap.ext_getElem?
      intro k
      simp [GMap.singleton]
    have Hempty : hasFuels (GF := GF) tid ((GMap.singleton () (f - 6)).erase ()) ⊢
        hasFuels (GF := GF) tid (∅ : GMap Unit Nat) := by
      rw [Herase]
    iapply Hempty $$ Hf
  | succ n IHn =>
    iintro #HI !> %Φ ⟨Hf, Hr, Hm⟩ HΦ
    wp_lam
    -- Load - with invariant
    wp_bind (!_)
    iapply wp_atomic (E₂ := ⊤ \ ↑Ns)
    imod chooseNatInv_acc γ l $$ HI with ⟨HInv, Hclose⟩
    iunfold chooseNatInvInner at HInv
    icases HInv with ⟨%cn, Hs, Hl, Hcn⟩
    imodintro
    wp_load
    ihave %Hvalid := ownE_agree γ _ _ $$ Hcn Hm
    imod Hclose $$ [Hs Hl Hcn] with -
    · iunfold chooseNatInvInner
      iexists cn
      iframe
    imodintro
    rw [Hvalid]
    have Hpos : (0 : Int) < ((n + 1 : Nat) : Int) := by omega
    wp_pures
    isimp only [Hpos, decide_true]
    wp_pures
    have Hsub : ((n + 1 : Nat) : Int) - 1 = (n : Int) := by omega
    isimp only [Hsub]
    -- Store - with invariant
    wp_bind (_ ← _)
    iapply wp_atomic (E₂ := ⊤ \ ↑Ns)
    imod chooseNatInv_acc γ l $$ HI with ⟨HInv, Hclose⟩
    iunfold chooseNatInvInner at HInv
    icases HInv with ⟨%cn, Hs, Hl, Hcn⟩
    ihave %Hvalid := ownE_agree γ _ _ $$ Hcn Hm
    obtain rfl : cn = .n (n + 1) := by
      cases cn with
      | start => simp only [cnZ] at Hvalid; omega
      | n k => simp only [cnZ] at Hvalid; congr 1; omega
    imodintro
    have Hlive : cnFairModel.liveRoles (CN.n n) ⊆ cnFairModel.liveRoles (CN.n (n + 1)) := by
      intro x _
      exact mem_singleton_extTreeSet.mpr rfl
    -- Update the model state to maintain program correspondence
    iapply wp_step_model_singlerole .NotStuck tid () (f - 7) ∅ (CN.n (n + 1) : cnFairModel.fmstate)
      (CN.n n : cnFairModel.fmstate) (⊤ \ ↑Ns) _ _ rfl (CnTrans.decr_trans n) Hlive $$ Hs Hf Hr
    iapply wp_store .NotStuck (⊤ \ ↑Ns) l _ _ $$ Hl
    inext
    iintro Hl Hs Hf Hr
    iapply wp_value'
    imod ownE_update γ _ _ (n : Int) $$ Hcn Hm with ⟨Hcn, Hm⟩
    imod Hclose $$ [Hs Hl Hcn] with -
    · iunfold chooseNatInvInner
      iexists CN.n n
      isimp only [cnZ]
      iframe
    imodintro
    have H40 : cnModel.lmFl (CN.n n) = 40 := rfl
    isimp only [H40] at Hf
    wp_pures
    ihave #IH := IHn 38 (by omega) (by omega) $$ HI
    iapply IH $$ %Φ [Hf Hr Hm] [HΦ]
    · iframe
    · inext
      iexact HΦ

@[rocq_alias trillium.fairis.choose_nat_spec]
theorem choose_nat_spec (γ : GName) (l : Loc) (tid : BaseLocale) (f : Nat) :
    12 ≤ f → f ≤ 40 →
    ⊢ chooseNatInv (GF := GF) γ l -∗
      iprop({{ (tid ↦M GMap.singleton () f) ∗ fragFreeRolesAre (GF := GF) ∅ ∗
          ownE γ (◯E (⟨-1⟩ : IntO)) }}
        tl(v(&(chooseNatProg l)) #()) @[tid] ⊤
        {{ RET .lit .unit; tid ↦M ∅ }}) := by
  intro Hle1 Hle2
  iintro #HI !> %Φ ⟨Hf, Hr, Hm⟩ HΦ
  wp_lam
  wp_bind chooseNat()
  have Hfs := has_fuels_gt_1 (GF := GF) (GMap.singleton () (f - 1)) tid (by solve_fuel_positive)
  ihave Hf := Hfs.1 $$ Hf
  isimp only [GMap.map_singleton, Nat.sub_sub] at Hf
  iapply wp_step_fuel .NotStuck tid ⊤ _ _ _ (GMap.singleton_ne_empty _ _) $$ [Hf]
  · inext
    iexact Hf
  iapply wp_choose_nat
  inext
  iintro %k Hf
  have H2 : f - (1 + 1) = f - 2 := rfl
  isimp only [H2] at Hf
  wp_value_head
  wp_pures
  -- Store - with invariant
  wp_bind (_ ← _)
  iapply wp_atomic (E₂ := ⊤ \ ↑Ns)
  imod chooseNatInv_acc γ l $$ HI with ⟨HInv, Hclose⟩
  iunfold chooseNatInvInner at HInv
  icases HInv with ⟨%cn, Hs, Hl, Hcn⟩
  ihave %Hvalid := ownE_agree γ _ _ $$ Hcn Hm
  obtain rfl : cn = .start := by
    cases cn with
    | start => rfl
    | n k => simp only [cnZ] at Hvalid; omega
  imodintro
  have Hlive : cnFairModel.liveRoles (CN.n (k + 1)) ⊆ cnFairModel.liveRoles CN.start := by
    intro x _
    exact mem_singleton_extTreeSet.mpr rfl
  -- Update the model state to maintain program correspondence
  iapply wp_step_model_singlerole .NotStuck tid () (f - 3) ∅ (CN.start : cnFairModel.fmstate)
    (CN.n (k + 1) : cnFairModel.fmstate) (⊤ \ ↑Ns) _ _ rfl (CnTrans.start_trans (k + 1)) Hlive
    $$ Hs Hf Hr
  iapply wp_store .NotStuck (⊤ \ ↑Ns) l _ _ $$ Hl
  inext
  iintro Hl Hs Hf Hr
  iapply wp_value'
  imod ownE_update γ _ _ ((k + 1 : Nat) : Int) $$ Hcn Hm with ⟨Hcn, Hm⟩
  imod Hclose $$ [Hs Hl Hcn] with -
  · iunfold chooseNatInvInner
    iexists CN.n (k + 1)
    have Hk : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
    isimp only [← Hk] at Hl
    isimp only [cnZ]
    iframe
  imodintro
  have H40 : cnModel.lmFl (CN.n (k + 1)) = 40 := rfl
  isimp only [H40] at Hf
  wp_pures
  ihave #Hspec := decr_loop_spec γ tid l (k + 1) 38 (by omega) (by omega) $$ HI
  iapply Hspec $$ %Φ [Hf Hr Hm] [HΦ]
  · iframe
  · inext
    iexact HΦ

end proof

end Trillium.Fairis.ChooseNat
