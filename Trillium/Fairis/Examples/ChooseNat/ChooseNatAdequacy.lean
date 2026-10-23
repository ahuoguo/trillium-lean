/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.Fairis.Adequacy
import Trillium.Fairis.Examples.ChooseNat.ChooseNat

/-!
# Adequacy of the `choose_nat` example
Port of `fairis/examples/choose_nat/choose_nat_adequacy.v`.

Using the Fairis adequacy theorem, the program `chooseNatProg l` (started with `l ↦ #-1`) is
related to the live model `cnModel` by `simRelWithUser cnModel (ξCn l)` (`choose_nat_sim`), hence
all its fair executions terminate (`choose_nat_terminates`).

## Representation

* Rocq instantiates the ghost state with the concrete `choose_natΣ`. iris-lean has no concrete
  `invΣ`/`heapΣ`, so (as for iris-lean's `heap_adequacy`) the theorems are instead stated for any
  `GF` with `[HeapGpreS cnModel GF] [ChooseNatG GF]`.
* The initial heap `{[l := #-1]}` is `GMap.singleton l (.lit (.int (-1)))`.
-/

namespace Trillium.Fairis.ChooseNat

open Iris Iris.BI Iris.Std Iris.ProofMode Iris.OFE
open Trillium Trillium.HeapLang Trillium.Fairness
open Iris.HeapLang (Loc HeapF)

/-- Inverse mapping of program state to model state, to compute a finite relation. -/
@[rocq_alias trillium.fairis.Z_CN]
def zCn : Val → CN
  | .lit (.int (.ofNat n)) => .n n
  -- Error case when `z < -1`, and when `v` is not an integer.
  | _ => .start

@[rocq_alias trillium.fairis.Z_CN_CN_Z]
theorem Z_CN_CN_Z (cn : CN) : zCn (.lit (.int (cnZ cn))) = cn := by
  cases cn <;> rfl

/-- The initial configuration of the example. -/
abbrev initCfg (l : Loc) : List Expr × State :=
  ([tl(v(&(chooseNatProg l)) #())], ⟨GMap.singleton l (.lit (.int (-1))), ∅⟩)

/-- Derive that the program is related to the model by `simRelWithUser cnModel (ξCn l)`, using
Trillium's adequacy. -/
@[rocq_alias trillium.fairis.choose_nat_sim]
theorem choose_nat_sim (GF : BundledGFunctors) [HeapGpreS cnModel GF] [ChooseNatG GF] (l : Loc) :
    ContinuedSimulation (simRelWithUser cnModel (ξCn l)) {tr[initCfg l]}
      {tr[initialLs cnModel CN.start 0]} := by
  refine strong_simulation_adequacy GF cnModel .NotStuck _ _ CN.start ∅ (ξCn l) ?_ ?_ ?_
  · apply rel_finitary_sim_rel_with_user_ξ
    intro extr atr c' oζ
    apply finite_smaller_card_nat
    apply in_list_finite [(zCn (c'.2.heap.getD l default), none),
      (zCn (c'.2.heap.getD l default), some ())]
    rintro ⟨cn, o⟩ ⟨cn', Hextr, Hatr⟩
    simp only [FiniteTrace.last] at Hextr Hatr
    rw [Hextr, Z_CN_CN_Z, ← Hatr]
    cases o <;> simp
  · intro h
    have : () ∈ cnFairModel.liveRoles CN.start := by
      simp only [cnFairModel, cnLiveRoles]
      exact mem_singleton_extTreeSet.mpr rfl
    rw [h] at this
    exact LawfulSet.mem_empty this
  · intro _
    iintro !> Hσ Hs Hr Hf
    imod iOwn_alloc (F := constOF (ExclAuth.ExclAuthR (A := IntO)))
      ((ExclAuth.auth (⟨-1⟩ : IntO)) • ExclAuth.frag (⟨-1⟩ : IntO)) ExclAuth.valid with ⟨%γ, He⟩
    icases iOwn_op.1 $$ He with ⟨Hea, Hef⟩
    imod inv_alloc Ns ⊤ (chooseNatInvInner (GF := GF) γ l) $$ [Hea Hσ Hs] with #HI
    · inext
      iunfold chooseNatInvInner
      iexists CN.start
      have Hsing := BigSepM.bigSepM_singleton (M := HeapF) (PROP := IProp GF)
        (Φ := fun l v => iprop(l ↦ v)) (i := l) (x := Val.lit (.int (-1)))
      have Heq : (PartialMap.singleton l (Val.lit (.int (-1))) : HeapF Val) =
          GMap.singleton l (Val.lit (.int (-1))) := rfl
      rw [Heq] at Hsing
      ihave Hl := Hsing.1 $$ Hσ
      isimp only [cnZ]
      iframe
    imodintro
    isplitl [Hr Hf Hef]
    · have Hfr : (∅ : GSet Unit) \ cnFairModel.liveRoles CN.start = ∅ := by
        apply LawfulSet.ext
        intro x
        simp only [LawfulSet.mem_diff]
        exact ⟨fun h => absurd h.1 LawfulSet.mem_empty, fun h => absurd h LawfulSet.mem_empty⟩
      have Hfuel : GSet.toGMap (cnModel.lmFl CN.start) (cnFairModel.liveRoles CN.start) =
          GMap.singleton () 40 := toGMap_singleton _ _
      have HrEq : fragFreeRolesAre (GF := GF) (∅ \ cnFairModel.liveRoles CN.start) ⊢
          fragFreeRolesAre (GF := GF) ∅ := by rw [Hfr]
      ihave Hr := HrEq $$ Hr
      ihave Hf : hasFuels (GF := GF) 0 (GMap.singleton () 40) $$ [Hf]
      · rw [← Hfuel]
        iexact Hf
      have Hspec := choose_nat_spec (GF := GF) γ l 0 40 (by omega) (by omega)
      unfold chooseNatInv at Hspec
      ihave Hspec := Hspec $$ HI
      isimp only [localeOf_eq, List.length_nil]
      iapply Hspec $$ [Hr Hf Hef]
      · iframe
      · inext
        iintro H
        iexact H
    · iunfold relAlwaysHolds
      iintro %ex %atr %c %Hvalid %Hex %Hatr %Hends %Hξ %Hstuck %Hequiv Hσ -
      imod inv_acc (E := ⊤) (N := Ns) (P := chooseNatInvInner (GF := GF) γ l)
        CoPset.subseteq_top $$ HI with ⟨>HInv, Hclose⟩
      iunfold chooseNatInvInner at HInv
      icases HInv with ⟨%cn, Hf, Hl, Ha⟩
      rw [heapG_stateInterp_eq]
      icases Hσ with ⟨%Hvse, Hh, Hm⟩
      ihave %Hlookup : ⌜ex.last.2.heap[l]? = some (Val.lit (.int (cnZ cn)))⌝ $$ [Hh Hl]
      · ihave >%H := genHeap_valid' ex.last.2 l _ _ $$ [$Hh $Hl]
        ipureintro
        exact H
      ihave %Hlast := model_agree' (GF := GF) atr.last (cn : cnFairModel.fmstate) ex.last.1 $$ Hm Hf
      imod Hclose $$ [Hf Hl Ha] with -
      · inext
        iunfold chooseNatInvInner
        iexists cn
        iframe
      iapply fupd_mask_intro_discard LawfulSet.empty_subset
      ipureintro
      refine ⟨cn, ?_, ?_⟩
      · rw [Std.ExtTreeMap.getD_eq_getD_getElem?, Hlookup]
        rfl
      · rw [← Hlast]
        cases atr <;> rfl

@[rocq_alias trillium.fairis.choose_nat_terminates]
theorem choose_nat_terminates (GF : BundledGFunctors) [HeapGpreS cnModel GF] [ChooseNatG GF]
    (l : Loc) (extr : Extrace Expr) :
    extr.first = initCfg l → ExtraceFairlyTerminating extr := by
  intro Hexfirst
  apply heap_lang_continued_simulation_fair_termination (LM := cnModel) (ξCn l) CN.start 0 extr
  rw [Hexfirst]
  exact choose_nat_sim GF l

end Trillium.Fairis.ChooseNat
