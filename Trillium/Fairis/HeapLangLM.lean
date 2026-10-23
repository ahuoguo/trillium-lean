/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.Fairis.Resources
import Trillium.HeapLang.SswpLogic

/-!
# HeapLang with a live model

Port of `fairis/heap_lang_lm.v`: the ghost state for Fairis proofs about HeapLang programs and the
state interpretation of Trillium's weakest preconditions for HeapLang with a live model `LM`.

## Representation

* `heapGpreS Σ LM` is the class `HeapGpreS LM GF` extending iris-lean's `InvGpreS GF` with the
  heap and fairness pre-ghost-state (as iris-lean's `HeapLangGpreS`).
* `heapGS Σ LM` is the class `HeapGS LM GF`. In Lean, `Heap1GS` already contains `Heap1GpreS`,
  `FairnessGS` contains `FairnessGpreS` and `InvGS_gen` contains `InvGpreS`, so storing the
  Rocq field `heap_inG : heapGpreS Σ LM` would create instance diamonds; it is instead the
  derived instance `HeapGS.heap_inG`. The invariant ghost state `heap_invGS` is (as in Rocq and
  as in iris-lean's `HeapLangGS`) *not* an instance: it is found through the `IrisG` instance
  `heapG_irisG`, which avoids a diamond.
* The live model `LM` (and its fair model `M`) are `outParam`s, so that `hasFuels`, `fragModelIs`
  etc. find their `FairnessGS LM GF` instance from `GF` alone.
* `heapΣ`/`subG_heapPreG` are subsumed by `ElemG` typeclass synthesis on `BundledGFunctors`
  (iris-lean provides no concrete `invΣ`).
-/

set_option linter.dupNamespace false

namespace Trillium.Fairis

open Iris Iris.BI Iris.Std
open Trillium Trillium.HeapLang Trillium.Fairness
open Iris.HeapLang (HeapF)

/-- The ghost state needed to allocate the resources of a Fairis HeapLang proof (Rocq
`heapGpreS`). -/
@[rocq_alias trillium.fairis.heapGpreS]
class HeapGpreS {M : outParam FairModel} (LM : outParam (LiveModel BaseLocale M))
    (GF : BundledGFunctors) extends InvGpreS GF where
  heapGpreS_gen_heap : Heap1GpreS GF
  heapGpreS_fairness : FairnessGpreS LM GF

attribute [reducible, instance] HeapGpreS.heapGpreS_gen_heap HeapGpreS.heapGpreS_fairness

/-- The ghost state of a Fairis HeapLang proof (Rocq `heapGS`). -/
@[rocq_alias trillium.fairis.heapGS]
class HeapGS {M : outParam FairModel} (LM : outParam (LiveModel BaseLocale M))
    (GF : BundledGFunctors) where
  /-- Not an instance on purpose: it is found through `heapG_irisG` (avoids diamonds). -/
  heap_invGS : InvGS_gen .hasNoLC GF
  heap_gen_heapGS : Heap1GS GF
  heap_fairnessGS : FairnessGS LM GF

attribute [reducible, instance] HeapGS.heap_gen_heapGS HeapGS.heap_fairnessGS

/-- Rocq field `heap_inG` of `heapGS`: derived from the other fields. -/
@[reducible]
instance HeapGS.heap_inG {M : FairModel} {LM : LiveModel BaseLocale M} {GF : BundledGFunctors}
    [H : HeapGS LM GF] : HeapGpreS LM GF where
  toInvGpreS := H.heap_invGS.toInvGpreS
  heapGpreS_gen_heap := inferInstance
  heapGpreS_fairness := inferInstance

#rocq_ignore trillium.fairis.«heapΣ»
  "Superseded by the `HeapGpreS` typeclass on `BundledGFunctors` (iris-lean has no concrete `invΣ`)."
#rocq_ignore trillium.fairis.subG_heapPreG "Superseded by Lean's direct `ElemG` typeclass synthesis."

/-- The state interpretation of Fairis HeapLang proofs (Rocq `heapG_irisG`): the last steps of
the execution and the auxiliary trace match, the heap of the last configuration is interpreted by
`gen_heap`, and the last live state by `modelStateInterp`. A forked thread must give back its
(empty) fuel map. -/
@[rocq_alias trillium.fairis.heapG_irisG, reducible]
instance heapG_irisG {M : FairModel} {LM : LiveModel BaseLocale M} {GF : BundledGFunctors}
    [H : HeapGS LM GF] : IrisG Expr LM.toModel GF where
  invGS := H.heap_invGS
  stateInterp extr auxtr :=
    iprop(⌜validStateEvolutionFairness LM extr auxtr⌝ ∗
      genHeapInterp (H := HeapF) extr.last.2.heap ∗
      modelStateInterp (GF := GF) extr.last.1 auxtr.last)
  forkPost tid _ := hasFuels (GF := GF) tid ∅

section

variable {M : FairModel} {LM : LiveModel BaseLocale M} {GF : BundledGFunctors} [HeapGS LM GF]

theorem heapG_stateInterp_eq (extr : ExecutionTrace Expr) (auxtr : AuxiliaryTrace LM.toModel) :
    stateInterp (GF := GF) extr auxtr =
      iprop(⌜validStateEvolutionFairness LM extr auxtr⌝ ∗
        genHeapInterp (H := HeapF) extr.last.2.heap ∗
        modelStateInterp (GF := GF) extr.last.1 auxtr.last) := rfl

theorem heapG_forkPost_eq (tid : BaseLocale) (v : Val) :
    forkPost (GF := GF) (Expr := Expr) (M := LM.toModel) tid v = hasFuels (GF := GF) tid ∅ := rfl

end

end Trillium.Fairis
