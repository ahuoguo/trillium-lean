/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Iris.Std.HeapInstances
import Iris.Std.GenSetsInstances
import Iris.Std.RocqPorting
import Mathlib.Logic.Encodable.Basic

/-!
# Finite maps and sets used throughout the Trillium port

Trillium (Rocq) uses stdpp's `gmap K V` and `gset K` for keys with
`EqDecision K` and `Countable K`. Following iris-lean (see `Iris.HeapLang.Semantics`
and `Iris.Instances.Lib.WSat`), we represent them by Lean's extensional tree maps and
sets, ordered by `compare`. This makes iris-lean's `PartialMap`/`LawfulFiniteMap` and
`LawfulFiniteSet` instances (and hence its CMRA constructions, `GhostMap`, `GenHeap`,
...) directly applicable.

Keys must carry `[Ord K] [Std.TransOrd K] [Std.LawfulEqOrd K]`, which plays the role of
stdpp's `Countable K`. For a type with an `Encodable` instance, `Trillium.ordOfEncodable`
provides such an order (see the instances below).
-/

namespace Trillium

/-- stdpp's `gmap K V`. -/
abbrev GMap (K : Type _) (V : Type _) [Ord K] := Std.ExtTreeMap K V compare

/-- stdpp's `gset K`. -/
abbrev GSet (K : Type _) [Ord K] := Std.ExtTreeSet K compare

/-- The order on an `Encodable` type obtained by comparing codes. Use it to equip a
type with the `Ord` instance required by `GMap`/`GSet`:
```
instance : Ord T := ordOfEncodable
instance : Std.TransOrd T := transOrd_ordOfEncodable
instance : Std.LawfulEqOrd T := lawfulEqOrd_ordOfEncodable
```
-/
@[instance_reducible]
def ordOfEncodable {α : Type _} [Encodable α] : Ord α :=
  ⟨fun a b => compare (Encodable.encode a) (Encodable.encode b)⟩

theorem transOrd_ordOfEncodable {α : Type _} [Encodable α] :
    @Std.TransOrd α ordOfEncodable where
  eq_swap := Std.OrientedCmp.eq_swap (cmp := (compare : Nat → Nat → Ordering))
  isLE_trans := Std.TransCmp.isLE_trans (cmp := (compare : Nat → Nat → Ordering))

theorem lawfulEqOrd_ordOfEncodable {α : Type _} [Encodable α] :
    @Std.LawfulEqOrd α ordOfEncodable where
  compare_self := Std.ReflCmp.compare_self (cmp := (compare : Nat → Nat → Ordering))
  eq_of_compare h :=
    Encodable.encode_injective (Std.LawfulEqCmp.eq_of_compare (cmp := (compare : Nat → Nat → Ordering)) h)

end Trillium
