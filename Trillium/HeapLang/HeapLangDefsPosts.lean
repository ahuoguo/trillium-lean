/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.HeapLang.HeapLangDefs
import Trillium.ProgramLogic.Adequacy

/-!
# Postconditions of terminated HeapLang threads

Port of the `GeneralProperties` section of `heap_lang/heap_lang_defs.v` (the rest of that file is
in `Trillium/HeapLang/HeapLangDefs.lean`). It lives in a separate file because it depends on
`Trillium.postsOf`/`Trillium.curPosts` from the adequacy development.

Rocq's `seq 0 (length tp)` is `List.range tp.length`.
-/

namespace Trillium.HeapLang

open Iris Iris.BI

section GeneralProperties

variable {M : Model} {GF : BundledGFunctors} [IrisG Expr M GF]

/-- Auxiliary lemma: the postcondition of a terminated thread can be extracted from
`postsOf`. -/
theorem postsOf_getElem? {tp : List Expr} {Φs : List (Val → IProp GF)} {tid : Nat} {e : Expr}
    {v : Val} {Φ : Val → IProp GF} (Hsome : tp[tid]? = some e) (Hval : e.toVal = some v)
    (HΦ : Φs[tid]? = some Φ) :
    postsOf tp Φs ⊢ Φ v := by
  refine BigSepL.bigSepL_mem (Φ := fun vΦ : Val × (Val → IProp GF) => vΦ.2 vΦ.1)
    (x := (v, Φ)) ?_
  refine List.mem_filterMap.mpr ⟨(e, Φ), ?_, by simp [Hval]⟩
  exact List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨Hsome, HΦ⟩)

@[rocq_alias trillium.heap_lang.posts_of_empty_mapping_multiple]
theorem posts_of_empty_mapping_multiple (_es e : Expr) (v : Val) (tid : BaseLocale)
    (tp : List Expr) :
    tp[tid]? = some e → e.toVal = some v →
    postsOf tp ((List.range tp.length).map (forkPost (GF := GF))) ⊢ forkPost tid v := by
  intro Hsome Hval
  refine postsOf_getElem? Hsome Hval ?_
  have : tid < tp.length := (List.getElem?_eq_some_iff.mp Hsome).1
  simp [this]

@[rocq_alias trillium.heap_lang.posts_of_empty_mapping]
theorem posts_of_empty_mapping (e1 e : Expr) (v : Val) (tid : Nat) (tp : List Expr) :
    tp[tid]? = some e → e.toVal = some v →
    curPosts tp e1 (fun v => forkPost (GF := GF) 0 v) ⊢ forkPost tid v := by
  intro Hsome Hval
  refine postsOf_getElem? Hsome Hval ?_
  cases tid with
  | zero => rfl
  | succ tid =>
    have Hsome' : (tp.drop 1)[tid]? = some e := by simpa [Nat.add_comm] using Hsome
    have hlt : tid < (tp.drop 1).length := (List.getElem?_eq_some_iff.mp Hsome').1
    simp only [List.getElem?_cons_succ, List.getElem?_map,
      prefixesFrom_getElem? _ _ _ _ Hsome', Option.map_some, localeOf_eq]
    rw [List.length_append, List.length_singleton, List.length_take,
      Nat.min_eq_left hlt.le, Nat.add_comm]

end GeneralProperties

end Trillium.HeapLang
