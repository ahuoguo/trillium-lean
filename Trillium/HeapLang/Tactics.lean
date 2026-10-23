/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Trillium.HeapLang.Lang
import Qq

/-!
# Decomposing HeapLang expressions into evaluation contexts

Port of `heap_lang/tactics.v`.

The Rocq file only contains the Ltac `reshape_expr e tac`, which decomposes the expression `e`
into an evaluation context `K` and a subexpression `e'` and calls `tac K e'` for each possible
decomposition (outermost first) until `tac` succeeds. It is used by the `wp_bind`-style tactics
of `fairis/proofmode.v`. Following iris-lean's `Iris.HeapLang.Tactic`, its Lean counterpart is
the meta-level function `Trillium.HeapLang.findECtx` (and the innermost-first variant
`findECtxRev`), working on quoted `Q(Expr)` terms and generic in the tactic monad, so that it
can be used from `MetaM`, `TacticM` or iris-lean's `ProofModeM`.

The decomposition follows `reshape_expr` exactly: a right-to-left evaluation order, where a
left operand is only decomposed once the right operands are values. The resulting `K` satisfies
`fill K e' = e` definitionally (`fill` for a list of items folds `ECtxItem.fill`, innermost
item first).
-/

namespace Trillium.HeapLang

open Lean hiding Expr
open Qq

/-- Peel off the outermost evaluation context item of `e`, following Rocq's `reshape_expr`.
Returns `none` (together with `e`) if `e` is not of the form `Ki.fill e'`. -/
partial def extractEctxItem (e : Q(Expr)) : MetaM (Option Q(ECtxItem) × Q(Expr)) := do
  match e with
  | ~q(.app $e (.val $v₂))                => return (some q(.appL $v₂), e)
  | ~q(.app $e₁ $e)                       => return (some q(.appR $e₁), e)
  | ~q(.unop $op $e)                      => return (some q(.unOp $op), e)
  | ~q(.binop $op $e (.val $v₂))          => return (some q(.binOpL $op $v₂), e)
  | ~q(.binop $op $e₁ $e)                 => return (some q(.binOpR $op $e₁), e)
  | ~q(.if $e $e₁ $e₂)                    => return (some q(.if $e₁ $e₂), e)
  | ~q(.pair $e (.val $v₂))               => return (some q(.pairL $v₂), e)
  | ~q(.pair $e₁ $e)                      => return (some q(.pairR $e₁), e)
  | ~q(.fst $e)                           => return (some q(.fst), e)
  | ~q(.snd $e)                           => return (some q(.snd), e)
  | ~q(.injL $e)                          => return (some q(.injL), e)
  | ~q(.injR $e)                          => return (some q(.injR), e)
  | ~q(.case $e $e₁ $e₂)                  => return (some q(.case $e₁ $e₂), e)
  | ~q(.allocN $e (.val $v₂))             => return (some q(.allocNL $v₂), e)
  | ~q(.allocN $e₁ $e)                    => return (some q(.allocNR $e₁), e)
  | ~q(.load $e)                          => return (some q(.load), e)
  | ~q(.store $e (.val $v₂))              => return (some q(.storeL $v₂), e)
  | ~q(.store $e₁ $e)                     => return (some q(.storeR $e₁), e)
  | ~q(.cmpXchg $e (.val $v₁) (.val $v₂)) => return (some q(.cmpXchgL $v₁ $v₂), e)
  | ~q(.cmpXchg $e₀ $e (.val $v₂))        => return (some q(.cmpXchgM $e₀ $v₂), e)
  | ~q(.cmpXchg $e₀ $e₁ $e)               => return (some q(.cmpXchgR $e₀ $e₁), e)
  | ~q(.faa $e (.val $v₂))                => return (some q(.faaL $v₂), e)
  | ~q(.faa $e₁ $e)                       => return (some q(.faaR $e₁), e)
  | _ => return (none, e)

/-- Decompose `e` completely: the list of items (innermost first) and the innermost
subexpression. -/
partial def extractAllEctxItems (e : Q(Expr)) (acc : List Q(ECtxItem) := []) :
    MetaM (List Q(ECtxItem) × Q(Expr)) := do
  match ← extractEctxItem e with
  | (some Ki, e') => extractAllEctxItems e' (Ki :: acc)
  | (none, e) => return (acc, e)

/-- Quote a list of quoted terms. -/
def quoteList {u : Level} {α : Q(Type u)} : List Q($α) → Q(List $α)
  | [] => q([])
  | x :: xs => q($x :: $(quoteList xs))

/-- The result of `findECtx` for the expression `e`: the context `K`, the subexpression `e'`
(with `fill K e' = e` definitionally) and the result of the callback. -/
structure ECtxResult (α : Type) where
  result : α
  K : Q(List ECtxItem)
  e' : Q(Expr)

/-- Rocq's `reshape_expr e tac`: try `pred K e'` on the decompositions `fill K e' = e` of `e`,
starting with the outermost one (`K = []`), and return the first one on which `pred` does not
fail (backtracking the state of failed attempts). -/
partial def findECtx {m : Type → Type} {σ ε : Type} [Monad m] [MonadLiftT MetaM m]
    [MonadBacktrack σ m] [MonadExcept ε m] {α : Type} (e : Q(Expr))
    (pred : Q(List ECtxItem) → Q(Expr) → m α) : m (Option (ECtxResult α)) :=
  go e []
where
  /-- `acc` holds the items peeled off so far, innermost first. -/
  go (e : Q(Expr)) (acc : List Q(ECtxItem)) : m (Option (ECtxResult α)) := do
    let K := quoteList acc
    if let some a ← observing? (pred K e) then
      return some { result := a, K, e' := e }
    let (some Ki, e') ← (extractEctxItem e : MetaM _) | return none
    go e' (Ki :: acc)

/-- Like `findECtx`, but starting with the innermost decomposition. -/
partial def findECtxRev {m : Type → Type} {σ ε : Type} [Monad m] [MonadLiftT MetaM m]
    [MonadBacktrack σ m] [MonadExcept ε m] {α : Type} (e : Q(Expr))
    (pred : Q(List ECtxItem) → Q(Expr) → m α) : m (Option (ECtxResult α)) := do
  let (Kis, inner) ← (extractAllEctxItems e : MetaM _)
  go inner Kis
where
  /-- `Kis` is the context still to be peeled off from the innermost expression, innermost
  item first. -/
  go (e' : Q(Expr)) (Kis : List Q(ECtxItem)) : m (Option (ECtxResult α)) := do
    if let some a ← observing? (pred (quoteList Kis) e') then
      return some { result := a, K := quoteList Kis, e' }
    match Kis with
    | [] => return none
    | Ki :: Kis => go q(ECtxItem.fill $Ki $e') Kis

end Trillium.HeapLang
