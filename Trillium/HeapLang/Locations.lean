/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Iris.HeapLang.Syntax
import Trillium.Std.Maps

/-!
# Locations

Port of `heap_lang/locations.v`.

Trillium's locations are the same as Iris' HeapLang locations, so we reuse iris-lean's
`Iris.HeapLang.Loc` (a structure wrapping an `Int`, with `l + i` for Rocq's `l +ₗ i`) and its
instances and lemmas, recording the correspondence on the iris-lean constants.

The only addition is `freshLocs`, which (as in Rocq) takes a finite set of locations
(`Trillium.GSet Loc`) rather than the list taken by iris-lean's `Loc.fresh`.
-/

attribute [rocq_alias trillium.heap_lang.loc] Iris.HeapLang.Loc
attribute [rocq_alias trillium.heap_lang.loc_eq_decision] Iris.HeapLang.instDecidableEqLoc
attribute [rocq_alias trillium.heap_lang.loc_inhabited] Iris.HeapLang.instInhabitedLoc
attribute [rocq_alias trillium.heap_lang.loc_countable] Iris.HeapLang.instCountableLoc
attribute [rocq_alias trillium.heap_lang.loc_infinite] Iris.HeapLang.instInfiniteTypeLoc
attribute [rocq_alias trillium.heap_lang.loc_add] Iris.HeapLang.instHAddLocInt
attribute [rocq_alias trillium.heap_lang.loc_add_assoc] Iris.HeapLang.loc_add_assoc
attribute [rocq_alias trillium.heap_lang.loc_add_0] Iris.HeapLang.loc_add_zero
attribute [rocq_alias trillium.heap_lang.loc_add_inj] Iris.HeapLang.loc_add_inj

namespace Trillium.HeapLang

open Iris.HeapLang (Loc)

/-- A location `l` such that `l + i` is not in `ls` for every `0 ≤ i`. -/
@[rocq_alias trillium.heap_lang.fresh_locs]
def freshLocs (ls : GSet Loc) : Loc := Loc.fresh ls.toList

@[rocq_alias trillium.heap_lang.fresh_locs_fresh]
theorem freshLocs_fresh (ls : GSet Loc) {i : Int} (hi : 0 ≤ i) : freshLocs ls + i ∉ ls := by
  intro h
  exact Loc.fresh_fresh ls.toList hi (Std.ExtTreeSet.mem_toList.mpr h)

end Trillium.HeapLang
