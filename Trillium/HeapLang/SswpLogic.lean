/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.HeapLang.HeapLangDefs

/-!
# Single-step weakest preconditions for HeapLang

Port of `heap_lang/sswp_logic.v`.

`sswp s E e Φ` is a single-step weakest precondition: if `e` is a value `v` it is `|={E}=> Φ v`,
otherwise `e` must take exactly one (fork-free) step, for which only the heap part of the state
(`genHeapInterp σ.heap`) is available. Unlike `wp`, the postcondition `Φ` is on the resulting
*expression*. The primitive heap laws (`wp_allocN_seq`, `wp_load`, …) are stated for `sswp`.

## Representation

* The context `heap1GS Σ`, `invGS_gen HasNoLc Σ` is `[Heap1GS GF] [InvGS_gen .hasNoLC GF]`.
* Rocq's `if s is NotStuck then reducible e1 σ1 else True` is `reducibleIfNotStuck s e1 σ1`.
* `l ↦{q} v` (fraction `q`) is `l ↦{DFrac.own q} v`; `seq 0 n` is `List.range n`; `#l`, `#n`
  are written with the constructors (`.val (.lit (.loc l))`, `.val (.lit (.int n))`).
* `vals_compare_safe v' v1` is the `Bool` `v'.compareSafe v1` (as a `Prop`, `= true`).
-/

set_option linter.dupNamespace false

namespace Trillium.HeapLang

open Iris Iris.BI Iris.Std Iris.ProofMode Iris.Algebra
open Iris.HeapLang (Loc Binder BaseLit UnOp BinOp HeapF)
open Trillium.Language Trillium.EctxLanguage

/-! ## Heap lemmas in terms of `Trillium.HeapLang.State` -/

section HeapLemmas

variable {GF : BundledGFunctors} [Heap1GS GF]

/-- `gen_heap_alloc_big` for the heap of `σ.initHeap l n v`. -/
theorem genHeap_alloc_initHeap (σ : State) (l : Loc) (n : Int) (v : Val)
    (hfresh : ∀ i : Int, 0 ≤ i → i < n → σ.heap[l + i]? = none) :
    genHeapInterp (H := HeapF) σ.heap ⊢@{IProp GF} |==>
      (genHeapInterp (H := HeapF) (σ.initHeap l n v).heap ∗
        bigSepM (M := HeapF) (fun l' v => iprop(l' ↦ v)) (heapArray l (List.replicate n.toNat v)) ∗
        bigSepM (M := HeapF) (fun l' _ => metaToken (V := Val) l' ⊤)
          (heapArray l (List.replicate n.toNat v))) := by
  have hdisj : PartialMap.disjoint (M := HeapF) (heapArray l (List.replicate n.toNat v)) σ.heap :=
    (PartialMap.disjoint_iff _ _).mpr <|
      heapArray_map_disjoint σ.heap l _ fun i hi hlt => hfresh i hi (by simp at hlt; omega)
  have heq := (partialMap_union_eq (heapArray l (List.replicate n.toNat v)) σ.heap).symm
  rw [show (σ.initHeap l n v).heap = σ.heap ∪ heapArray l (List.replicate n.toNat v) from rfl,
    heq]
  exact genHeap_alloc_big _ _ hdisj

/-- `gen_heap_update` with core's `Std.ExtTreeMap.insert`. -/
theorem genHeap_update' (σ : State) (l : Loc) (v₁ v₂ : Val) :
    genHeapInterp (H := HeapF) σ.heap ∗ l ↦ v₁ ==∗
      genHeapInterp (H := HeapF) (σ.heap.insert l v₂) ∗ l ↦ v₂ := by
  rw [← partialMap_insert_eq]
  exact genHeap_update

/-- `gen_heap_valid` with core's `getElem?`. -/
theorem genHeap_valid' (σ : State) (l : Loc) (dq : DFrac) (v : Val) :
    genHeapInterp (H := HeapF) σ.heap ∗ l ↦{dq} v ==∗ ⌜σ.heap[l]? = some v⌝ :=
  genHeap_valid

end HeapLemmas

section SSWP

variable {GF : BundledGFunctors} [Heap1GS GF] [InvGS_gen .hasNoLC GF]

/-- The single-step weakest precondition. -/
@[rocq_alias trillium.heap_lang.sswp]
def sswp (s : Stuckness) (E : CoPset) (e1 : Expr) (Φ : Expr → IProp GF) : IProp GF :=
  match e1.toVal with
  | some v => iprop(|={E}=> Φ (.val v))
  | none => iprop(∀ σ1 : State, genHeapInterp (H := HeapF) σ1.heap ={E,∅}=∗
      ⌜reducibleIfNotStuck s e1 σ1⌝ ∗
      ∀ (e2 : Expr) (σ2 : State) (efs : List Expr),
        ⌜primStep e1 σ1 e2 σ2 efs⌝ ={∅}▷=∗ |={∅,E}=>
          genHeapInterp (H := HeapF) σ2.heap ∗ Φ e2 ∗ ⌜efs = []⌝)

theorem sswp_eq_of_toVal_none {s : Stuckness} {E : CoPset} {e1 : Expr} {Φ : Expr → IProp GF}
    (h : e1.toVal = none) :
    sswp s E e1 Φ = iprop(∀ σ1 : State, genHeapInterp (H := HeapF) σ1.heap ={E,∅}=∗
      ⌜reducibleIfNotStuck s e1 σ1⌝ ∗
      ∀ (e2 : Expr) (σ2 : State) (efs : List Expr),
        ⌜primStep e1 σ1 e2 σ2 efs⌝ ={∅}▷=∗ |={∅,E}=>
          genHeapInterp (H := HeapF) σ2.heap ∗ Φ e2 ∗ ⌜efs = []⌝) := by
  simp only [sswp, h]

@[rocq_alias trillium.heap_lang.sswp_wand]
theorem sswp_wand (s : Stuckness) (e : Expr) (E : CoPset) (Φ Ψ : Expr → IProp GF) :
    (∀ e, Φ e -∗ Ψ e) -∗ sswp s E e Φ -∗ sswp s E e Ψ := by
  cases h : e.toVal with
  | some v =>
    simp only [sswp, h]
    iintro HΦΨ HΦ
    imod HΦ
    imodintro
    iapply HΦΨ $$ HΦ
  | none =>
    rw [sswp_eq_of_toVal_none h, sswp_eq_of_toVal_none h]
    iintro HΦΨ HΦ %σ H
    imod HΦ $$ %σ H with ⟨%Hs, HΦ⟩
    imodintro
    isplitr
    · ipureintro; exact Hs
    iintro %e2 %σ2 %efs %Hstep
    imod HΦ $$ %e2 %σ2 %efs %Hstep with HΦ
    iintro !> !>
    imod HΦ
    imodintro
    imod HΦ with ⟨Hσ, HΦ, Hefs⟩
    imodintro
    iframe Hσ Hefs
    iapply HΦΨ $$ HΦ

@[rocq_alias trillium.heap_lang.sswp_fupd]
theorem sswp_fupd (s : Stuckness) (E E' : CoPset) (e : Expr) (Φ : Expr → IProp GF)
    (NVAL : toVal e = none) :
    (|={E,E'}=> sswp s E' e (fun k => iprop(|={E',E}=> Φ k))) -∗ sswp s E e Φ := by
  simp only [toVal_eq] at NVAL
  rw [sswp_eq_of_toVal_none NVAL, sswp_eq_of_toVal_none NVAL]
  iintro Hwp %σ HEAP
  imod Hwp
  imod Hwp $$ %σ HEAP with ⟨%Hred, Hwp⟩
  imodintro
  isplitr
  · ipureintro; exact Hred
  iintro %e2 %σ2 %efs %Hstep
  imod Hwp $$ %e2 %σ2 %efs %Hstep with Hwp
  iintro !> !>
  imod Hwp
  imodintro
  imod Hwp with ⟨Hσ, HΦ, Hefs⟩
  imod HΦ
  imodintro
  iframe

theorem pureStep_of_iterate_one {e1 e2 : Expr} :
    Relation.Iterate (PureStep (Λ := heapLang)) 1 e1 e2 → PureStep (Λ := heapLang) e1 e2 := by
  intro h
  cases h with
  | tail y h0 hs => cases h0; exact hs

@[rocq_alias trillium.heap_lang.sswp_pure_step]
theorem sswp_pure_step (s : Stuckness) (E : CoPset) (e1 e2 : Expr) (φ : Prop)
    (Ψ : Expr → IProp GF) :
    PureExec φ 1 e1 e2 → φ → ▷ Ψ e2 -∗ sswp s E e1 Ψ := by
  intro Hpe Hφ
  have Hps : PureStep (Λ := heapLang) e1 e2 := pureStep_of_iterate_one (Hpe.pure_exec Hφ)
  have Hnv : e1.toVal = none := reducible_not_val (Hps.safe default)
  rw [sswp_eq_of_toVal_none Hnv]
  iintro HΨ %σ Hσ
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact Hps.safe σ
    · trivial
  iintro %e2' %σ2 %efs %Hstep !> !> !>
  imod Hclose
  imodintro
  obtain ⟨rfl, rfl, rfl⟩ := Hps.det Hstep
  iframe
  ipureintro; rfl

/-! ### Heap -/

@[rocq_alias trillium.heap_lang.wp_allocN_seq]
theorem wp_allocN_seq (s : Stuckness) (E : CoPset) (v : Val) (n : Int) (Φ : Expr → IProp GF) :
    0 < n →
    ▷ (∀ l : Loc, ([∗list] i ∈ List.range n.toNat,
          (l + ((i : Nat) : Int)) ↦ v ∗ metaToken (V := Val) (l + ((i : Nat) : Int)) ⊤) -∗
        Φ (.val (.lit (.loc l)))) -∗
      sswp s E (.allocN (.val (.lit (.int n))) (.val v)) Φ := by
  intro HnO
  rw [sswp_eq_of_toVal_none rfl]
  iintro HΦ %σ Hσ
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact head_prim_reducible ⟨_, _, _, alloc_fresh v n σ HnO⟩
    · trivial
  iintro %e2 %σ2 %efs %Hstep !> !> !>
  imod Hclose
  have Hhs := head_reducible_prim_step ⟨_, _, _, alloc_fresh v n σ HnO⟩ Hstep
  cases Hhs with
  | allocNS _ _ _ l _ hfresh =>
    imod genHeap_alloc_initHeap σ l n v hfresh $$ Hσ with ⟨Hσ, Hl, Hm⟩
    imodintro
    iframe Hσ
    isplitl
    · iapply HΦ
      iapply BigSepL.bigSepL_sep_eqv.2
      isplitl [Hl]
      · iapply heapArray_toSeq_pointsTo $$ Hl
      · iapply heapArray_toSeq_metaToken _ _ _ (List.length_replicate) $$ Hm
    · ipureintro; trivial

@[rocq_alias trillium.heap_lang.wp_alloc]
theorem wp_alloc (s : Stuckness) (E : CoPset) (v : Val) (Φ : Expr → IProp GF) :
    ▷ (∀ l : Loc, l ↦ v -∗ metaToken (V := Val) l ⊤ -∗ Φ (.val (.lit (.loc l)))) -∗
      sswp s E (.allocN (.val (.lit (.int 1))) (.val v)) Φ := by
  iintro HΦ
  iapply wp_allocN_seq _ _ _ _ _ (by omega)
  iintro !> %l H
  have h0 : l + ((0 : Nat) : Int) = l := Iris.HeapLang.loc_add_zero l
  ieval (simp only [Int.toNat_one, List.range_one, BigSepL.bigSepL_singleton.to_eq, h0]) at H
  icases H with ⟨Hl, Hm⟩
  iapply HΦ $$ Hl Hm

@[rocq_alias trillium.heap_lang.wp_choose_nat]
theorem wp_choose_nat (s : Stuckness) (E : CoPset) (Φ : Expr → IProp GF) :
    ▷ (∀ n : Nat, Φ (.val (.lit (.int n)))) -∗ sswp s E .chooseNat Φ := by
  rw [sswp_eq_of_toVal_none rfl]
  iintro HΦ %σ Hσ
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact head_prim_reducible ⟨_, _, _, BaseStep.chooseNatS 0 σ⟩
    · trivial
  iintro %e2 %σ2 %efs %Hstep !> !> !>
  imod Hclose
  have Hhs := head_reducible_prim_step ⟨_, _, _, BaseStep.chooseNatS 0 σ⟩ Hstep
  cases Hhs with
  | chooseNatS n _ =>
    imodintro
    iframe Hσ
    isplitl
    · iapply HΦ
    · ipureintro; trivial

@[rocq_alias trillium.heap_lang.wp_load]
theorem wp_load (s : Stuckness) (E : CoPset) (l : Loc) (q : Qp) (v : Val)
    (Φ : Expr → IProp GF) :
    ▷ l ↦{.own q} v -∗ ▷ (l ↦{.own q} v -∗ Φ (.val v)) -∗
      sswp s E (.load (.val (.lit (.loc l)))) Φ := by
  rw [sswp_eq_of_toVal_none rfl]
  iintro >Hl HΦ %σ Hσ
  ihave %Hheap : ⌜σ.heap[l]? = some v⌝ $$ [Hσ Hl]
  · ihave >%_ := genHeap_valid' σ l _ v $$ [$Hσ $Hl]
    itrivial
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact head_prim_reducible ⟨_, _, _, BaseStep.loadS l v σ Hheap⟩
    · trivial
  iintro %e2 %σ2 %efs %Hstep !> !> !>
  imod Hclose
  have Hhs := head_reducible_prim_step ⟨_, _, _, BaseStep.loadS l v σ Hheap⟩ Hstep
  cases Hhs with
  | loadS _ w _ hw =>
    rw [Hheap] at hw
    cases hw
    imodintro
    iframe Hσ
    isplitl
    · iapply HΦ $$ Hl
    · ipureintro; trivial

@[rocq_alias trillium.heap_lang.wp_store]
theorem wp_store (s : Stuckness) (E : CoPset) (l : Loc) (v' v : Val) (Φ : Expr → IProp GF) :
    ▷ l ↦ v' -∗ ▷ (l ↦ v -∗ Φ (.val (.lit .unit))) -∗
      sswp s E (.store (.val (.lit (.loc l))) (.val v)) Φ := by
  rw [sswp_eq_of_toVal_none rfl]
  iintro >Hl HΦ %σ Hσ
  ihave %Hheap : ⌜σ.heap[l]? = some v'⌝ $$ [Hσ Hl]
  · ihave >%_ := genHeap_valid' σ l _ v' $$ [$Hσ $Hl]
    itrivial
  have Hred : HeadReducible (Expr.store (.val (.lit (.loc l))) (.val v)) σ :=
    ⟨_, _, _, BaseStep.storeS l v σ (by simp [Hheap])⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact head_prim_reducible Hred
    · trivial
  iintro %e2 %σ2 %efs %Hstep !> !> !>
  imod Hclose
  imod genHeap_update' σ l v' v $$ [$Hσ $Hl] with ⟨Hσ, Hl⟩
  have Hhs := head_reducible_prim_step Hred Hstep
  cases Hhs with
  | storeS =>
    imodintro
    ieval (simp only [State.updHeap_heap])
    iframe Hσ
    isplitl
    · iapply HΦ $$ Hl
    · ipureintro; trivial

@[rocq_alias trillium.heap_lang.wp_cmpxchg_fail]
theorem wp_cmpxchg_fail (s : Stuckness) (E : CoPset) (l : Loc) (q : Qp) (v' v1 v2 : Val)
    (Φ : Expr → IProp GF) :
    v' ≠ v1 → v'.compareSafe v1 →
    ▷ l ↦{.own q} v' -∗ ▷ (l ↦{.own q} v' -∗ Φ (.val (.pair v' (.lit (.bool false))))) -∗
      sswp s E (.cmpXchg (.val (.lit (.loc l))) (.val v1) (.val v2)) Φ := by
  intro Hne Hsafe
  rw [sswp_eq_of_toVal_none rfl]
  iintro >Hl HΦ %σ Hσ
  ihave %Hheap : ⌜σ.heap[l]? = some v'⌝ $$ [Hσ Hl]
  · ihave >%_ := genHeap_valid' σ l _ v' $$ [$Hσ $Hl]
    itrivial
  have Hred : HeadReducible (Expr.cmpXchg (.val (.lit (.loc l))) (.val v1) (.val v2)) σ :=
    ⟨_, _, _, BaseStep.cmpXchgS l v1 v2 v' σ _ Hheap Hsafe rfl⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact head_prim_reducible Hred
    · trivial
  iintro %e2 %σ2 %efs %Hstep !> !> !>
  imod Hclose
  have Hhs := head_reducible_prim_step Hred Hstep
  cases Hhs with
  | cmpXchgS _ _ _ vl _ b hvl _ hb =>
    rw [Hheap] at hvl
    cases hvl
    have hb' : b = false := by simp [hb, Hne]
    subst hb'
    imodintro
    iframe Hσ
    isplitl
    · iapply HΦ $$ Hl
    · ipureintro; trivial

@[rocq_alias trillium.heap_lang.wp_cmpxchg_suc]
theorem wp_cmpxchg_suc (s : Stuckness) (E : CoPset) (l : Loc) (v' v1 v2 : Val)
    (Φ : Expr → IProp GF) :
    v' = v1 → v'.compareSafe v1 →
    ▷ l ↦ v' -∗ ▷ (l ↦ v2 -∗ Φ (.val (.pair v' (.lit (.bool true))))) -∗
      sswp s E (.cmpXchg (.val (.lit (.loc l))) (.val v1) (.val v2)) Φ := by
  intro Heq Hsafe
  rw [sswp_eq_of_toVal_none rfl]
  iintro >Hl HΦ %σ Hσ
  ihave %Hheap : ⌜σ.heap[l]? = some v'⌝ $$ [Hσ Hl]
  · ihave >%_ := genHeap_valid' σ l _ v' $$ [$Hσ $Hl]
    itrivial
  have Hred : HeadReducible (Expr.cmpXchg (.val (.lit (.loc l))) (.val v1) (.val v2)) σ :=
    ⟨_, _, _, BaseStep.cmpXchgS l v1 v2 v' σ _ Hheap Hsafe rfl⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact head_prim_reducible Hred
    · trivial
  iintro %e2 %σ2 %efs %Hstep !> !> !>
  imod genHeap_update' σ l v' v2 $$ [$Hσ $Hl] with ⟨Hσ, Hl⟩
  imod Hclose
  have Hhs := head_reducible_prim_step Hred Hstep
  cases Hhs with
  | cmpXchgS _ _ _ vl _ b hvl _ hb =>
    rw [Hheap] at hvl
    cases hvl
    have hb' : b = true := by simp [hb, Heq]
    subst hb'
    imodintro
    ieval (simp only [State.updHeap_heap, ↓reduceIte])
    iframe Hσ
    isplitl
    · iapply HΦ $$ Hl
    · ipureintro; trivial

@[rocq_alias trillium.heap_lang.wp_faa]
theorem wp_faa (s : Stuckness) (E : CoPset) (l : Loc) (i a : Int) (Φ : Expr → IProp GF) :
    ▷ l ↦ .lit (.int i) -∗ ▷ (l ↦ .lit (.int (i + a)) -∗ Φ (.val (.lit (.int i)))) -∗
      sswp s E (.faa (.val (.lit (.loc l))) (.val (.lit (.int a)))) Φ := by
  rw [sswp_eq_of_toVal_none rfl]
  iintro >Hl HΦ %σ Hσ
  ihave %Hheap : ⌜σ.heap[l]? = some (.lit (.int i))⌝ $$ [Hσ Hl]
  · ihave >%_ := genHeap_valid' σ l _ _ $$ [$Hσ $Hl]
    itrivial
  have Hred : HeadReducible (Expr.faa (.val (.lit (.loc l))) (.val (.lit (.int a)))) σ :=
    ⟨_, _, _, BaseStep.faaS l i a σ Hheap⟩
  iapply fupd_mask_intro LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact head_prim_reducible Hred
    · trivial
  iintro %e2 %σ2 %efs %Hstep !> !> !>
  imod genHeap_update' σ l _ (.lit (.int (i + a))) $$ [$Hσ $Hl] with ⟨Hσ, Hl⟩
  imod Hclose
  have Hhs := head_reducible_prim_step Hred Hstep
  cases Hhs with
  | faaS _ i' _ _ hi =>
    rw [Hheap] at hi
    cases hi
    imodintro
    ieval (simp only [State.updHeap_heap])
    iframe Hσ
    isplitl
    · iapply HΦ $$ Hl
    · ipureintro; trivial

end SSWP

end Trillium.HeapLang
