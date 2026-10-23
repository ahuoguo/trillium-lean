/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Iris.BI.WeakestPre
import Trillium.ProgramLogic.Language

/-!
# Weakest preconditions with thread identifiers

Port of `trillium/bi/weakestpre.v`.

Trillium's weakest preconditions carry, besides the stuckness bit and the mask, the *locale*
(thread identifier) `ζ` of the thread executing the expression.

## Stuckness

The stuckness bit, its order and `stuckness_to_atomicity` are literally those of Iris and are
reused from iris-lean (`Iris.Stuckness`, `Iris.Stuckness.instLE`,
`Iris.ProgramLogic.Language.Atomicity.ofStuckness`, also available as the coercion
`Stuckness → Atomicity`).

## Notation

iris-lean's `WP e @ s; E {{ Φ }}` (without a locale) stays available and denotes iris-lean's
`Iris.Wp.wp`. Trillium's weakest preconditions use syntactically distinct forms:

* `WP e @ s; ζ; E {{ v, Φ }}` / `WP e @ s; ζ; E {{ Φ }}`: full form, three `@`-components
  (stuckness, locale, mask), as in Rocq's `WP e @ s; tid; E {{ v, Φ }}`;
* `WP e @[ζ] E {{ v, Φ }}`: not stuck, locale `ζ`, mask `E` (Rocq `WP e @ tid; E {{ v, Φ }}`);
* `WP e @[ζ] E ? {{ v, Φ }}`: maybe stuck (Rocq `WP e @ tid; E ?{{ v, Φ }}`);
* `WP e @[ζ] {{ v, Φ }}`: not stuck, mask `⊤` (Rocq `WP e @ tid {{ v, Φ }}`);
* `WP e @[ζ] ? {{ v, Φ }}`: maybe stuck, mask `⊤` (Rocq `WP e @ tid ?{{ v, Φ }}`).

Texan triples use the same targets: `{{ P }} e @ s; ζ; E {{ x y, RET v; Q }}`,
`{{ P }} e @[ζ] E {{ RET v; Q }}`, … . As in iris-lean, a Texan triple inside `iprop(…)` is
`□ ∀ Φ, P -∗ ▷ (∀ x y, Q -∗ Φ v) -∗ WP …`, and as a Lean proposition it is
`⊢ ∀ Φ, P -∗ ▷ (∀ x y, Q -∗ Φ v) -∗ WP …` (the Rocq `stdpp_scope` variant).
-/

namespace Trillium

open Iris Lean

/-! ## Stuckness -/

attribute [rocq_alias trillium.stuckness] Iris.Stuckness
attribute [rocq_alias trillium.stuckness_le] Iris.Stuckness.instLE
attribute [rocq_alias trillium.stuckness_le_po] Iris.Stuckness.instIsPreorder
attribute [rocq_alias trillium.stuckness_to_atomicity]
  Iris.ProgramLogic.Language.Atomicity.ofStuckness

#rocq_ignore trillium.stuckness_leb
  "iris-lean defines the order on `Iris.Stuckness` directly as a `Prop`-valued `LE` instance"

/-! ## The `Wp` class -/

/-- Weakest preconditions `WP e @ s; ζ; E {{ Φ }}` with an additional argument `s : A` (the
stuckness bit) and the locale `ζ` of the executing thread. -/
@[rocq_alias trillium.Wp]
class Wp (PROP Expr : Type _) (Val Locale : outParam (Type _)) (A : Type _) where
  wp : A → CoPset → Locale → Expr → (Val → PROP) → PROP

/-! ## Notation -/

/-- `WP e @ s; ζ; E {{ v, Φ }}`: Trillium weakest precondition with stuckness `s`, locale `ζ`
and mask `E`. -/
syntax (name := trilliumWpFull)
  "WP " term:max " @ " term:max " ; " term:max " ; " term:max ppSpace wpPostcond : term
/-- `WP e @[ζ] E {{ v, Φ }}`: not-stuck Trillium weakest precondition with locale `ζ`. -/
syntax (name := trilliumWpTidMask) "WP " term:max " @[" term "] " term:max ppSpace wpPostcond : term
/-- `WP e @[ζ] E ? {{ v, Φ }}`: maybe-stuck Trillium weakest precondition with locale `ζ`. -/
syntax (name := trilliumWpTidMaskMaybe)
  "WP " term:max " @[" term "] " term:max " ? " wpPostcond : term
/-- `WP e @[ζ] {{ v, Φ }}`: not-stuck Trillium weakest precondition with locale `ζ`, mask `⊤`. -/
syntax (name := trilliumWpTid) "WP " term:max " @[" term "] " wpPostcond : term
/-- `WP e @[ζ] ? {{ v, Φ }}`: maybe-stuck Trillium weakest precondition with locale `ζ`, mask
`⊤`. -/
syntax (name := trilliumWpTidMaybe) "WP " term:max " @[" term "] " "? " wpPostcond : term

/-- Texan triple `{{ P }} e @ s; ζ; E {{ x, RET v; Q }}`. -/
syntax (name := trilliumTexanFull) texanPrecond ppSpace
  term:max " @ " term:max " ; " term:max " ; " term:max ppSpace texanPostcond : term
/-- Texan triple `{{ P }} e @[ζ] E {{ x, RET v; Q }}`. -/
syntax (name := trilliumTexanTidMask) texanPrecond ppSpace
  term:max " @[" term "] " term:max ppSpace texanPostcond : term
/-- Texan triple `{{ P }} e @[ζ] E ? {{ x, RET v; Q }}`. -/
syntax (name := trilliumTexanTidMaskMaybe) texanPrecond ppSpace
  term:max " @[" term "] " term:max " ? " texanPostcond : term
/-- Texan triple `{{ P }} e @[ζ] {{ x, RET v; Q }}`. -/
syntax (name := trilliumTexanTid) texanPrecond ppSpace
  term:max " @[" term "] " texanPostcond : term
/-- Texan triple `{{ P }} e @[ζ] ? {{ x, RET v; Q }}`. -/
syntax (name := trilliumTexanTidMaybe) texanPrecond ppSpace
  term:max " @[" term "] " "? " texanPostcond : term

/-- Build `Trillium.Wp.wp s E ζ e Φ` from a postcondition. -/
meta def mkTrilliumWp (tk : Syntax) (s ζ E e : Term) (post : TSyntax `wpPostcond) :
    MacroM Term := do
  let (Φ, useTotal?) ← parseWpPostcond post
  if useTotal? then
    Macro.throwErrorAt post "Trillium has no total weakest preconditions"
  `($(BI.wrapIpropSpan tk post ``Wp.wp) $s $E $ζ $e $Φ)

macro_rules
  | `(WP%$tk $e @ $s ; $ζ ; $E $post:wpPostcond) => mkTrilliumWp tk s ζ E e post
  | `(WP%$tk $e @[ $ζ ] $E:term $post:wpPostcond) =>
    do mkTrilliumWp tk (← `(Stuckness.NotStuck)) ζ E e post
  | `(WP%$tk $e @[ $ζ ] $E:term ? $post:wpPostcond) =>
    do mkTrilliumWp tk (← `(Stuckness.MaybeStuck)) ζ E e post
  | `(WP%$tk $e @[ $ζ ] $post:wpPostcond) =>
    do mkTrilliumWp tk (← `(Stuckness.NotStuck)) ζ (← `(⊤)) e post
  | `(WP%$tk $e @[ $ζ ] ? $post:wpPostcond) =>
    do mkTrilliumWp tk (← `(Stuckness.MaybeStuck)) ζ (← `(⊤)) e post

/-- The components `(e, s, ζ, E, P, xs, pat, Q)` of a Trillium Texan triple. -/
meta def parseTrilliumTexan : Syntax →
    MacroM (Term × Term × Term × Term × Term ×
      Option (Array (TSyntax [`Lean.binderIdent, `Lean.Parser.Term.bracketedBinder])) ×
      Term × Term)
  | `({{ $P:term }} $e @ $s ; $ζ ; $E {{ $[$[$xs]* ,]? RET $pat ; $Q:term }}) =>
    return (e, s, ζ, E, P, xs, pat, Q)
  | `({{ $P:term }} $e @[ $ζ ] $E:term {{ $[$[$xs]* ,]? RET $pat ; $Q:term }}) => do
    return (e, ← `(Stuckness.NotStuck), ζ, E, P, xs, pat, Q)
  | `({{ $P:term }} $e @[ $ζ ] $E:term ? {{ $[$[$xs]* ,]? RET $pat ; $Q:term }}) => do
    return (e, ← `(Stuckness.MaybeStuck), ζ, E, P, xs, pat, Q)
  | `({{ $P:term }} $e @[ $ζ ] {{ $[$[$xs]* ,]? RET $pat ; $Q:term }}) => do
    return (e, ← `(Stuckness.NotStuck), ζ, ← `(⊤), P, xs, pat, Q)
  | `({{ $P:term }} $e @[ $ζ ] ? {{ $[$[$xs]* ,]? RET $pat ; $Q:term }}) => do
    return (e, ← `(Stuckness.MaybeStuck), ζ, ← `(⊤), P, xs, pat, Q)
  | _ => Macro.throwUnsupported

/-- `∀ Φ, P -∗ ▷ (∀ xs, Q -∗ Φ pat) -∗ WP e @ s; ζ; E {{ Φ }}` for a Trillium Texan triple. -/
meta def expandTrilliumTexan (stx : Syntax) : MacroM Term := do
  let (e, s, ζ, E, P, xs, pat, Q) ← parseTrilliumTexan stx
  let k ← match xs with
    | some xs =>
      let xs : TSyntaxArray [`ident, `Lean.Parser.Term.hole, `Lean.Parser.Term.bracketedBinder] ←
        xs.mapM fun
          | `(binderIdent| _) => `(hole| _)
          | `(binderIdent| $i:ident) => `(ident| $i)
          | `(bracketedBinder| $x) => `(bracketedBinder| $x)
      `(iprop(∀ $xs*, $Q:term -∗ Φ $pat))
    | none => `(iprop($Q:term -∗ Φ $pat))
  `(∀ Φ, $P -∗ ▷ $k -∗ (WP $e @ $s ; $ζ ; $E {{ Φ }}))

@[macro Iris.BI.iprop]
meta def trilliumTexanIprop : Macro
  | `(iprop($P)) => do `(iprop(□ $(← expandTrilliumTexan P)))
  | _ => Macro.throwUnsupported

@[macro trilliumTexanFull, macro trilliumTexanTidMask, macro trilliumTexanTidMaskMaybe,
  macro trilliumTexanTid, macro trilliumTexanTidMaybe]
meta def trilliumTexanTerm : Macro
  | P => do `(⊢ $(← expandTrilliumTexan P))

/-- Pretty-print `Trillium.Wp.wp s E ζ e Φ` as `WP e @ s; ζ; E {{ Φ }}` (or a shorthand). -/
@[app_unexpander Wp.wp]
meta def unexpandTrilliumWp : PrettyPrinter.Unexpander
  | `($_wp $s $E $ζ $e $Φ) => do
    let inner ← unexpandWpPostcondInner Φ
    match s, E with
    | `(Stuckness.NotStuck), `(⊤) => `(WP $e @[ $ζ ] {{ $inner }})
    | `(Stuckness.NotStuck), E => `(WP $e @[ $ζ ] $E {{ $inner }})
    | `(Stuckness.MaybeStuck), `(⊤) => `(WP $e @[ $ζ ] ? {{ $inner }})
    | `(Stuckness.MaybeStuck), E => `(WP $e @[ $ζ ] $E ? {{ $inner }})
    | s, E => `(WP $e @ $s ; $ζ ; $E {{ $inner }})
  | _ => throw ()

/-! ## Notation tests

Both iris-lean's (locale-free) and Trillium's notations parse side by side. -/

section NotationTests

variable {PROP : Type} [BI PROP] {Expr Val Locale : Type}
variable [Wp PROP Expr Val Locale Stuckness] [Iris.Wp PROP Expr Val Stuckness]
variable (e : Expr) (ζ : Locale) (Φ : Val → PROP) (E : CoPset) (P Q : PROP) (s : Stuckness)
variable (v : Val)

example : PROP := iprop(WP e @ s; ζ; E {{ Φ }})
example : PROP := iprop(WP e @ s; ζ; E {{ w, Φ w ∗ P }})
example : PROP := iprop(WP e @[ζ] E {{ w, Φ w }})
example : PROP := iprop(WP e @[ζ] E ? {{ w, Φ w }})
example : PROP := iprop(WP e @[ζ] {{ w, Φ w }})
example : PROP := iprop(WP e @[ζ] ? {{ Φ }})
example : iprop(WP e @[ζ] E {{ Φ }}) = Wp.wp Stuckness.NotStuck E ζ e Φ := rfl
example : iprop(WP e @[ζ] ? {{ Φ }}) = Wp.wp Stuckness.MaybeStuck ⊤ ζ e Φ := rfl
-- iris-lean's notation is unaffected:
example : PROP := iprop(WP e @ s; E {{ Φ }})
example : PROP := iprop(WP e @ E {{ Φ }})
example : PROP := iprop(WP e {{ Φ }})
example : iprop(WP e @ E ? {{ Φ }}) = Iris.Wp.wp Stuckness.MaybeStuck E e Φ := rfl
-- Texan triples
example : Prop := {{ P }} e @ s; ζ; E {{ RET v; Q }}
example : Prop := {{ P }} e @[ζ] E {{ x, RET x; Q }}
example : Prop := {{ P }} e @[ζ] {{ x (_n : Nat), RET x; Q }}
example : Prop := {{ P }} e @[ζ] ? {{ RET v; Q }}
example : PROP := iprop({{ P }} e @[ζ] E ? {{ RET v; Q }})
example : Prop := {{ P }} e @ s; E {{ RET v; Q }}

end NotationTests

end Trillium
