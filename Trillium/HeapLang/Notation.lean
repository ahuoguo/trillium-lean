/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.HeapLang.Lang
import Lean.PrettyPrinter.Parenthesizer

/-!
# HeapLang notation

Port of `heap_lang/notation.v`.

A surface syntax for Trillium's HeapLang, adapted from iris-lean's `Iris.HeapLang.Notation`
(which is for iris-lean's own HeapLang expression type). `notation.v` has no named
declarations, only notations; the Rocq derived forms are the following `tl(…)` syntax:

| Rocq | Lean (`tl(…)` / `tl_val(…)`) |
|---|---|
| `#l` (literals) | `#l`, e.g. `#1`, `#true`, `#()`, `#l` for `l : Loc` |
| `"x"` (variables) | `x` (an identifier) |
| `rec: "f" "x" "y" := e` | `rec f x y := e` |
| `λ: "x" "y", e`, `λ: <>, e` | `λ x y, e`, `λ _, e` |
| `let: "x" := e1 in e2` | `let x := e1; e2` |
| `e1 ;; e2` | `e1; e2` |
| `if: e1 then e2 else e3` | `if e1 then e2 else e3` |
| `e1 e2` (application) | `e1 e2` |
| `!e`, `e1 <- e2` | `!e`, `e1 ← e2` |
| `ref e`, `Alloc e`, `AllocN e1 e2` | `ref(e)`, `alloc(e)`, `allocn(e1, e2)` |
| `CmpXchg e0 e1 e2`, `CAS e0 e1 e2`, `FAA e1 e2` | `cmpXchg(e0, e1, e2)`, `cas(e0, e1, e2)`, `faa(e1, e2)` |
| `Fork e` | `fork(e)` |
| `ChooseNat` | `chooseNat()` |
| `Skip` | `skip()` |
| `(e1, e2)`, `Fst e`, `Snd e` | `(e1, e2)`, `fst(e)`, `snd(e)` |
| `InjL e`, `InjR e`, `NONE`, `SOME e` | `injl(e)`, `injr(e)`, `none()`, `some(e)` |
| `match: e with InjL x => e1 \| InjR y => e2 end` | `match e with \| injl(x) => e1 \| injr(y) => e2` |
| `e1 + e2`, `-e`, `~e`, `e1 = e2`, `e1 < e2`, … | the same (`/`, `%` for `quot`, `rem`) |
| `e1 ≠ e2` | `e1 ≠ e2` |
| `e1 && e2`, `e1 \|\| e2` (short-circuit) | `e1 && e2`, `e1 \|\| e2` |

Lean terms are embedded with `&t` (a term of type `Expr`, or of type `Val` through the
coercion `↑`), values with `v(…)`. Example (Rocq `fairis/examples/yesno/yesno.v`):
```
def yesGo : Val := tl_val(
  rec yes_go n b :=
    (if cas(b, #true, #false) then n ← !n - #1 else #());
    if #0 < !n then yes_go n b else #())
def yes : Val := tl_val(λ N b, let n := ref(N); v(&yesGo) n b)
```
The entry points `tl(…)`, `tl_val(…)`, `tl_binder(…)` and the syntax categories (`tl_exp`,
`tl_val`, `tl_binder`, `tl_match_arm`) are distinct from iris-lean's `hl(…)` (which is imported
transitively through `Iris.HeapLang`), so the two notations do not interfere.
-/

namespace Trillium.HeapLang

open Lean Lean.PrettyPrinter Lean.PrettyPrinter.Delaborator Elab Parser
open Iris.HeapLang (Binder BaseLit UnOp BinOp)

declare_syntax_cat tl_exp
declare_syntax_cat tl_binder
declare_syntax_cat tl_match_arm
declare_syntax_cat tl_val

/-- embedding HeapLang expressions into terms -/
syntax:max "tl(" tl_exp ")" : term
syntax:min "tl% " tl_exp:min : term
macro_rules
  | `(tl% $t) => `(tl($t))
/-- embedding HeapLang binders into terms -/
syntax:max "tl_binder(" tl_binder ")" : term
/-- embedding HeapLang values into terms -/
syntax:max "tl_val(" tl_val ")" : term
syntax:min "tl_val% " tl_val:min : term
macro_rules
  | `(tl_val% $t) => `(tl_val($t))

/-- escaping -/
syntax:max "&" term:max : tl_binder
syntax:max binderIdent : tl_binder

/-- escaping -/
syntax:max "&" term:max : tl_val
/-- embedding literals -/
syntax:max "#" term:max : tl_val
/-- pairs -/
syntax:max "(" tl_val ", " tl_val,+ ")" : tl_val
/-- injL -/
syntax:100 "injl(" tl_val ")" : tl_val
/-- injR -/
syntax:100 "injr(" tl_val ")" : tl_val
/-- none and some -/
syntax:100 "none()" : tl_val
syntax:100 "some(" tl_val ")" : tl_val

/-- parenthesis -/
syntax:max "(" tl_exp ")" : tl_exp
/-- embedding values -/
syntax:max "v(" tl_val ")" : tl_exp
/-- escaping -/
syntax:max "&" term:max : tl_exp
/-- embedding literals -/
syntax:max "#" term:max : tl_exp
/-- variables -/
syntax:max ident : tl_exp
/-- addition -/
syntax:65 tl_exp:66 " + " tl_exp:65 : tl_exp
/-- offset -/
syntax:65 tl_exp:66 " +ₗ " tl_exp:65 : tl_exp
/-- subtraction -/
syntax:65 tl_exp:66 " - " tl_exp:65 : tl_exp
/-- multiplication -/
syntax:70 tl_exp:71 " * " tl_exp:70 : tl_exp
/-- division (Rocq `quot`) -/
syntax:70 tl_exp:71 " / " tl_exp:70 : tl_exp
/-- modulo (Rocq `rem`) -/
syntax:70 tl_exp:71 " % " tl_exp:70 : tl_exp
/-- and -/
syntax:60 tl_exp:61 " &&& " tl_exp:60 : tl_exp
/-- or -/
syntax:55 tl_exp:56 " ||| " tl_exp:55 : tl_exp
/-- xor -/
syntax:58 tl_exp:59 " ^^^ " tl_exp:58 : tl_exp
/-- shiftl -/
syntax:75 tl_exp:76 " <<< " tl_exp:75 : tl_exp
/-- shiftr -/
syntax:75 tl_exp:76 " >>> " tl_exp:75 : tl_exp
/-- le -/
syntax:50 tl_exp:50 " <= " tl_exp:50 : tl_exp
syntax:50 tl_exp:50 " ≤ " tl_exp:50 : tl_exp
/-- lt -/
syntax:50 tl_exp:50 " < " tl_exp:50 : tl_exp
/-- equality -/
syntax:50 tl_exp:50 " = " tl_exp:50 : tl_exp
/-- disequality -/
syntax:50 tl_exp:50 " ≠ " tl_exp:50 : tl_exp

/-- short-circuit conjunction -/
syntax:35 tl_exp:36 " && " tl_exp:35 : tl_exp
/-- short-circuit disjunction -/
syntax:30 tl_exp:31 " || " tl_exp:30 : tl_exp

/-- neg -/
syntax:100 "~" tl_exp:100 : tl_exp
/-- minus -/
syntax:75 "-" tl_exp:75 : tl_exp

/-- if -/
syntax:10 "if " tl_exp:10 " then " tl_exp:10 " else " tl_exp:10 : tl_exp

/-- application -/
syntax:100 tl_exp:100 colGt ppSpace tl_exp:101 : tl_exp
/-- let -/
syntax:10 "let " tl_binder " := " tl_exp:10 "; " tl_exp:1 : tl_exp
/-- sequencing -/
syntax:5 tl_exp:6 "; " tl_exp:5 : tl_exp
/-- lambda -/
syntax:10 "λ " tl_binder+ ", " tl_exp:1 : tl_exp
/-- lambda -/
syntax:10 "λ " tl_binder+ ", " tl_exp:1 : tl_val
/-- recursive function -/
syntax:10 "rec " tl_binder ppSpace tl_binder+ " := " tl_exp:1 : tl_exp
/-- recursive function -/
syntax:10 "rec " tl_binder ppSpace tl_binder+ " := " tl_exp:1 : tl_val

/-- pairs -/
syntax:max "(" tl_exp ", " tl_exp,+ ")" : tl_exp
/-- fst -/
syntax:100 "fst(" tl_exp ")" : tl_exp
/-- snd -/
syntax:100 "snd(" tl_exp ")" : tl_exp

/-- injL -/
syntax:100 "injl(" tl_exp ")" : tl_exp
/-- injR -/
syntax:100 "injr(" tl_exp ")" : tl_exp

/-- none and some -/
syntax:100 "none()" : tl_exp
syntax:100 "some(" tl_exp ")" : tl_exp

/-- match -/
syntax:100 "match " tl_exp:5 " with"
  " | " tl_match_arm " => " tl_exp:5
  " | " tl_match_arm " => " tl_exp:5 : tl_exp

syntax "injl(" tl_binder ")" : tl_match_arm
syntax "injr(" tl_binder ")" : tl_match_arm
syntax "some(" tl_binder ")" : tl_match_arm
syntax "none()" : tl_match_arm

/-- heap operations -/
syntax:100 "allocn(" tl_exp ", " tl_exp ")" : tl_exp
syntax:100 "ref(" tl_exp ")" : tl_exp
syntax:100 "alloc(" tl_exp ")" : tl_exp
syntax:100 "!" tl_exp:100 : tl_exp
syntax:15 tl_exp:16 " ← " tl_exp:15 : tl_exp
syntax:100 "cmpXchg(" tl_exp ", " tl_exp ", " tl_exp ")" : tl_exp
syntax:100 "cas(" tl_exp ", " tl_exp ", " tl_exp ")" : tl_exp
syntax:100 "faa(" tl_exp ", " tl_exp ")" : tl_exp

/-- fork -/
syntax:100 "fork(" tl_exp ")" : tl_exp

/-- non-deterministic choice of a natural number -/
syntax:100 "chooseNat()" : tl_exp

/-- `Skip`: an atomic no-op step -/
syntax:100 "skip()" : tl_exp

/-- holes -/
syntax "_" : tl_exp

open Lean.PrettyPrinter.Parenthesizer in
@[category_parenthesizer tl_exp]
def tl_exp.parenthesizer : CategoryParenthesizer := fun prec => do
  maybeParenthesize `tl_exp false (fun stx => Unhygienic.run `(tl_exp|($(⟨stx⟩)))) prec <|
    parenthesizeCategoryCore `tl_exp prec

partial def unpackHLExp [Monad m] [MonadQuotation m] :
    Term → m (TSyntax `tl_exp)
  | `(tl($e)) => `(tl_exp|$e)
  | `($t) => `(tl_exp|&$t)

partial def unpackHLVal [Monad m] [MonadQuotation m] :
    Term → m (TSyntax `tl_val)
  | `(tl_val($e)) => `(tl_val|$e)
  | `($t) => `(tl_val|&$t)

partial def unpackHLBinder [Monad m] [MonadQuotation m] :
    Term → m (TSyntax `tl_binder)
  | `(tl_binder($e)) => `(tl_binder|$e)
  | `($t) => `(tl_binder|&$t)

/-- elaborating binders -/
macro_rules
  | `(tl_binder(_)) => `(Iris.HeapLang.Binder.anon)
  | `(tl_binder($i:ident)) =>
    `(Iris.HeapLang.Binder.named $(Syntax.mkStrLit i.getId.toString))
  | `(tl_binder(&$t)) => `($t)

/-- elaborating values -/
macro_rules
  | `(tl_val(& $t)) => pure t
  | `(tl_val(# $n:num)) => `(Trillium.HeapLang.Val.lit (Iris.HeapLang.BaseLit.int $n))
  | `(tl_val(# $e)) => `(Trillium.HeapLang.Val.lit $e)
  | `(tl_val(rec $f $x := $e)) =>
    `(Trillium.HeapLang.Val.rec_ tl_binder($f) tl_binder($x) tl($e))
  | `(tl_val(rec $f $x $xs* := $e)) => `(tl_val(rec $f $x := λ $xs*, $e))
  | `(tl_val(λ $xs*, $e)) => `(tl_val(rec _ $xs* := $e))
  | `(tl_val(($e1, $e2))) => `(Trillium.HeapLang.Val.pair tl_val($e1) tl_val($e2))
  | `(tl_val(($e1, $e2, $e3,*))) => `(tl_val(($e1, ($e2, $e3,*))))
  | `(tl_val(injl($e1))) => `(Trillium.HeapLang.Val.injL tl_val($e1))
  | `(tl_val(injr($e1))) => `(Trillium.HeapLang.Val.injR tl_val($e1))
  | `(tl_val(none())) => `(tl_val(injl(#())))
  | `(tl_val(some($e))) => `(tl_val(injr($e)))

/-- elaborating expressions -/
macro_rules
  | `(tl(($e))) => `(tl($e))
  | `(tl(_)) => `(_)
  | `(tl(&$t)) => `(($t : Trillium.HeapLang.Expr))
  | `(tl(v($e))) => `(Trillium.HeapLang.Expr.val tl_val($e))
  | `(tl(# $e)) => `(tl(v(# $e)))
  | `(tl($i:ident)) => `(Trillium.HeapLang.Expr.var $(Syntax.mkStrLit i.getId.toString))
  | `(tl($e1 + $e2)) => `(Trillium.HeapLang.Expr.binop .plus tl($e1) tl($e2))
  | `(tl($e1 +ₗ $e2)) => `(Trillium.HeapLang.Expr.binop .offset tl($e1) tl($e2))
  | `(tl($e1 - $e2)) => `(Trillium.HeapLang.Expr.binop .minus tl($e1) tl($e2))
  | `(tl($e1 * $e2)) => `(Trillium.HeapLang.Expr.binop .mult tl($e1) tl($e2))
  | `(tl($e1 / $e2)) => `(Trillium.HeapLang.Expr.binop .tdiv tl($e1) tl($e2))
  | `(tl($e1 % $e2)) => `(Trillium.HeapLang.Expr.binop .tmod tl($e1) tl($e2))
  | `(tl($e1 &&& $e2)) => `(Trillium.HeapLang.Expr.binop .and tl($e1) tl($e2))
  | `(tl($e1 ||| $e2)) => `(Trillium.HeapLang.Expr.binop .or tl($e1) tl($e2))
  | `(tl($e1 ^^^ $e2)) => `(Trillium.HeapLang.Expr.binop .xor tl($e1) tl($e2))
  | `(tl($e1 <<< $e2)) => `(Trillium.HeapLang.Expr.binop .shiftl tl($e1) tl($e2))
  | `(tl($e1 >>> $e2)) => `(Trillium.HeapLang.Expr.binop .shiftr tl($e1) tl($e2))
  | `(tl($e1 <= $e2)) => `(tl($e1 ≤ $e2))
  | `(tl($e1 ≤ $e2)) => `(Trillium.HeapLang.Expr.binop .le tl($e1) tl($e2))
  | `(tl($e1 < $e2)) => `(Trillium.HeapLang.Expr.binop .lt tl($e1) tl($e2))
  | `(tl($e1 = $e2)) => `(Trillium.HeapLang.Expr.binop .eq tl($e1) tl($e2))
  | `(tl($e1 ≠ $e2)) => `(tl(~($e1 = $e2)))
  | `(tl($e1 && $e2)) => `(tl(if $e1 then $e2 else #false))
  | `(tl($e1 || $e2)) => `(tl(if $e1 then #true else $e2))
  | `(tl(~$e1)) => `(Trillium.HeapLang.Expr.unop .neg tl($e1))
  | `(tl(-$e1)) => `(Trillium.HeapLang.Expr.unop .minus tl($e1))
  | `(tl(if $e1 then $e2 else $e3)) => `(Trillium.HeapLang.Expr.if tl($e1) tl($e2) tl($e3))
  | `(tl($e1 $e2)) => `(Trillium.HeapLang.Expr.app tl($e1) tl($e2))
  | `(tl(rec $f $x := $e)) =>
    `(Trillium.HeapLang.Expr.rec_ tl_binder($f) tl_binder($x) tl($e))
  | `(tl(rec $f $x $xs* := $e)) => `(tl(rec $f $x := λ $xs*, $e))
  | `(tl(λ $xs*, $e)) => `(tl(rec _ $xs* := $e))
  | `(tl($e1; $e2)) => `(tl(let _ := $e1; $e2))
  | `(tl(let $i := $e1; $e2)) => `(tl((λ $i, $e2) $e1))
  | `(tl(($e1, $e2))) => `(Trillium.HeapLang.Expr.pair tl($e1) tl($e2))
  | `(tl(($e1, $e2, $e3,*))) => `(tl(($e1, ($e2, $e3,*))))
  | `(tl(fst($e1))) => `(Trillium.HeapLang.Expr.fst tl($e1))
  | `(tl(snd($e1))) => `(Trillium.HeapLang.Expr.snd tl($e1))
  | `(tl(match $e1 with | injl($i2) => $e2 | injr($i3) => $e3)) =>
    `(Trillium.HeapLang.Expr.case tl($e1) tl(λ $i2, $e2) tl(λ $i3, $e3))
  | `(tl(match $e1 with | injr($i2) => $e2 | injl($i3) => $e3)) =>
    `(tl(match $e1 with | injl($i3) => $e3 | injr($i2) => $e2))
  | `(tl(match $e1 with | some($i2) => $e2 | none() => $e3)) =>
    `(tl(match $e1 with | injr($i2) => $e2 | injl(_) => $e3))
  | `(tl(match $e1 with | none() => $e2 | some($i3) => $e3)) =>
    `(tl(match $e1 with | injl(_) => $e2 | injr($i3) => $e3))
  | `(tl(injl($e1))) => `(Trillium.HeapLang.Expr.injL tl($e1))
  | `(tl(injr($e1))) => `(Trillium.HeapLang.Expr.injR tl($e1))
  | `(tl(none())) => `(tl(injl(#())))
  | `(tl(some($e))) => `(tl(injr($e)))
  | `(tl(allocn($e1, $e2))) => `(Trillium.HeapLang.Expr.allocN tl($e1) tl($e2))
  | `(tl(ref($e1))) => `(tl(allocn(#1, $e1)))
  | `(tl(alloc($e1))) => `(tl(allocn(#1, $e1)))
  | `(tl(! $e1)) => `(Trillium.HeapLang.Expr.load tl($e1))
  | `(tl($e1 ← $e2)) => `(Trillium.HeapLang.Expr.store tl($e1) tl($e2))
  | `(tl(cmpXchg($e1, $e2, $e3))) => `(Trillium.HeapLang.Expr.cmpXchg tl($e1) tl($e2) tl($e3))
  | `(tl(cas($e1, $e2, $e3))) => `(tl(snd(cmpXchg($e1, $e2, $e3))))
  | `(tl(faa($e1, $e2))) => `(Trillium.HeapLang.Expr.faa tl($e1) tl($e2))
  | `(tl(fork($e1))) => `(Trillium.HeapLang.Expr.fork tl($e1))
  | `(tl(chooseNat())) => `(Trillium.HeapLang.Expr.chooseNat)
  | `(tl(skip())) => `(tl(v(λ _, #()) #()))

/-! ### Delaboration -/

/-- delaborating binders -/
@[app_unexpander Iris.HeapLang.Binder.anon]
def unexpAnon : Unexpander
  | `($_) => `(tl_binder(_))

@[app_unexpander Iris.HeapLang.Binder.named]
def unexpNamed : Unexpander
  | `($_ $s:str) => `(tl_binder($(Lean.mkIdent <| Name.mkSimple s.getString):ident))
  | _ => throw ()

/-- delaborating values -/
@[app_unexpander Val.lit]
def unexpLit : Unexpander
  | `($_ ↑$arg) => `(tl_val(# $arg))
  | `($_ $c:ident) =>
    if c.getId.getString! == "unit" then `(tl_val(# ())) else `(tl_val(# $c))
  | `($_ $arg) => `(tl_val(# $arg))
  | _ => throw ()

partial def unexpLamVal : Term → UnexpandM Term
  | `(tl_val(rec _ $x := $e)) => do
    unexpLamVal <| ← `(tl_val(λ $x, $e))
  | `(tl_val(λ $x, (λ $ys*, $e))) => do
    unexpLamVal <| ← `(tl_val(λ $x $ys*, $e))
  | x => return x

@[app_unexpander Val.rec_]
def unexpRecVal : Unexpander
  | `($_ $f $x $e) => do
    unexpLamVal <| ←
      `(tl_val(rec $(← unpackHLBinder f) $(← unpackHLBinder x) := $(← unpackHLExp e)))
  | _ => throw ()

partial def unexpPairVal' : Term → UnexpandM Term
  | `(tl_val(($e1, ($e2, $e3,*)))) => do
    unexpPairVal' <| ← `(tl_val(($e1, $e2, $e3,*)))
  | x => return x

@[app_unexpander Val.pair]
def unexpPairVal : Unexpander
  | `($_ $e1 $e2) => do
    unexpPairVal' <| ← `(tl_val(($(← unpackHLVal e1), $(← unpackHLVal e2))))
  | _ => throw ()

@[app_unexpander Val.injL]
def unexpInjlVal : Unexpander
  | `($_ $e1) => do `(tl_val(injl($(← unpackHLVal e1))))
  | _ => throw ()

@[app_unexpander Val.injR]
def unexpInjrVal : Unexpander
  | `($_ $e1) => do `(tl_val(injr($(← unpackHLVal e1))))
  | _ => throw ()

/-- delaborating expressions -/
partial def unexpValLit : Term → UnexpandM Term
  | `(tl(v(# $l))) => do
    unexpValLit <| ← `(tl(# $l))
  | x => return x

@[app_unexpander Expr.val]
def unexpVal : Unexpander
  | `($_ $v) => do unexpValLit <| ← `(tl(v($(← unpackHLVal v))))
  | _ => throw ()

@[app_unexpander Expr.var]
def unexpVar : Unexpander
  | `($_ $e:str) => do `(tl($(Lean.mkIdent <| Name.mkSimple e.getString):ident))
  | _ => throw ()

@[app_unexpander Expr.binop]
def unexpBinop : Unexpander
  | `($_ $op:ident $e1 $e2) => do
    let e1 ← unpackHLExp e1
    let e2 ← unpackHLExp e2
    match op.getId.getString! with
    | "plus" => `(tl(($e1 + $e2)))
    | "offset" => `(tl(($e1 +ₗ $e2)))
    | "minus" => `(tl(($e1 - $e2)))
    | "mult" => `(tl(($e1 * $e2)))
    | "tdiv" => `(tl(($e1 / $e2)))
    | "tmod" => `(tl(($e1 % $e2)))
    | "and" => `(tl(($e1 &&& $e2)))
    | "or" => `(tl(($e1 ||| $e2)))
    | "xor" => `(tl(($e1 ^^^ $e2)))
    | "shiftl" => `(tl(($e1 <<< $e2)))
    | "shiftr" => `(tl(($e1 >>> $e2)))
    | "le" => `(tl(($e1 ≤ $e2)))
    | "lt" => `(tl(($e1 < $e2)))
    | "eq" => `(tl(($e1 = $e2)))
    | _ => throw ()
  | _ => throw ()

@[app_unexpander Expr.unop]
def unexpUnop : Unexpander
  | `($_ $op:ident $e1) => do
    let e1 ← unpackHLExp e1
    match op.getId.getString! with
    | "neg" => `(tl((~$e1)))
    | "minus" => `(tl((-$e1)))
    | _ => throw ()
  | _ => throw ()

@[app_unexpander Expr.if]
def unexpIf : Unexpander
  | `($_ $e1 $e2 $e3) => do
    `(tl(if $(← unpackHLExp e1) then $(← unpackHLExp e2) else $(← unpackHLExp e3)))
  | _ => throw ()

partial def unexpLam : Term → UnexpandM Term
  | `(tl((rec _ $x := $e))) => do
    unexpLam <| ← `(tl((λ $x, $e)))
  | `(tl((λ $x, (λ $ys*, $e)))) => do
    unexpLam <| ← `(tl((λ $x $ys*, $e)))
  | x => return x

@[app_unexpander Expr.rec_]
def unexpRec : Unexpander
  | `($_ $f $x $e) => do
    unexpLam <| ←
      `(tl((rec $(← unpackHLBinder f) $(← unpackHLBinder x) := $(← unpackHLExp e))))
  | _ => throw ()

partial def unexpLet : Term → UnexpandM Term
  | `(tl((λ $f, $e2) $e1)) => do
    unexpLet <| ← `(tl(let $f := $e1; $e2))
  | `(tl(let _ := $e1; $e2)) => do `(tl($e1; $e2))
  | x => return x

@[app_unexpander Expr.app]
def unexpApp : Unexpander
  | `($_ $e1 $e2) => do
    unexpLet <| ← `(tl($(← unpackHLExp e1) $(← unpackHLExp e2)))
  | _ => throw ()

partial def unexpPair' : Term → UnexpandM Term
  | `(tl(($e1, ($e2, $e3,*)))) => do
    unexpPair' <| ← `(tl(($e1, $e2, $e3,*)))
  | x => return x

@[app_unexpander Expr.pair]
def unexpPair : Unexpander
  | `($_ $e1 $e2) => do
    unexpPair' <| ← `(tl(($(← unpackHLExp e1), $(← unpackHLExp e2))))
  | _ => throw ()

@[app_unexpander Expr.fst]
def unexpFst : Unexpander
  | `($_ $e1) => do `(tl(fst($(← unpackHLExp e1))))
  | _ => throw ()

@[app_unexpander Expr.snd]
def unexpSnd : Unexpander
  | `($_ $e1) => do `(tl(snd($(← unpackHLExp e1))))
  | _ => throw ()

@[app_unexpander Expr.injL]
def unexpInjl : Unexpander
  | `($_ $e1) => do `(tl(injl($(← unpackHLExp e1))))
  | _ => throw ()

@[app_unexpander Expr.injR]
def unexpInjr : Unexpander
  | `($_ $e1) => do `(tl(injr($(← unpackHLExp e1))))
  | _ => throw ()

@[app_unexpander Expr.case]
def unexpCase : Unexpander
  | `($_ $e1 tl((λ $i2, $e2)) tl((λ $i3, $e3))) =>
    do `(tl(match $(← unpackHLExp e1) with | injl($i2) => $e2 | injr($i3) => $e3))
  | _ => throw ()

partial def unexpRef : Term → UnexpandM Term
  | `(tl(allocn(#1, $e2))) => do `(tl(ref($e2)))
  | x => return x

@[app_unexpander Expr.allocN]
def unexpAllocN : Unexpander
  | `($_ $e1 $e2) => do
    unexpRef <| ← `(tl(allocn($(← unpackHLExp e1), $(← unpackHLExp e2))))
  | _ => throw ()

@[app_unexpander Expr.load]
def unexpLoad : Unexpander
  | `($_ $e1) => do `(tl(!$(← unpackHLExp e1)))
  | _ => throw ()

@[app_unexpander Expr.store]
def unexpStore : Unexpander
  | `($_ $e1 $e2) => do `(tl($(← unpackHLExp e1) ← $(← unpackHLExp e2)))
  | _ => throw ()

@[app_unexpander Expr.cmpXchg]
def unexpCmpXChg : Unexpander
  | `($_ $e1 $e2 $e3) => do
    `(tl(cmpXchg($(← unpackHLExp e1), $(← unpackHLExp e2), $(← unpackHLExp e3))))
  | _ => throw ()

@[app_unexpander Expr.faa]
def unexpFAA : Unexpander
  | `($_ $e1 $e2) => do `(tl(faa($(← unpackHLExp e1), $(← unpackHLExp e2))))
  | _ => throw ()

@[app_unexpander Expr.fork]
def unexpFork : Unexpander
  | `($_ $e1) => do `(tl(fork($(← unpackHLExp e1))))
  | _ => throw ()

@[app_unexpander Expr.chooseNat]
def unexpChooseNat : Unexpander
  | `($_) => `(tl(chooseNat()))

end Trillium.HeapLang
