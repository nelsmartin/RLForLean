import Lean
/-
Anything that can be written in lean has a corresponding `Expr`. The goal of tactics is to produce an `Expr` of the correct type that can be checked by the kernal.



namespace Playground

inductive Expr where
  | bvar    : Nat → Expr                              -- bound variables
  | fvar    : FVarId → Expr                           -- free variables
  | mvar    : MVarId → Expr                           -- meta variables
  | sort    : Level → Expr                            -- Sort
  | const   : Name → List Level → Expr                -- constants
  | app     : Expr → Expr → Expr                      -- application
  | lam     : Name → Expr → Expr → BinderInfo → Expr  -- lambda abstraction
  | forallE : Name → Expr → Expr → BinderInfo → Expr  -- (dependent) arrow
  | letE    : Name → Expr → Expr → Expr → Bool → Expr -- let expressions
  -- less essential constructors:
  | lit     : Literal → Expr                          -- literals
  | mdata   : MData → Expr → Expr                     -- metadata
  | proj    : Name → Nat → Expr → Expr                -- projection

end Playground

Bound variables (`Expr.bvar`) are "bound" because they are referred to somewhere else, for example, `x` in `λ x => x + 2`. The `x` in `x + 2`, however, is not bound.

Bound variables in the "inner" part of the expression, like the second `x` in  `λ x => x + 2`, are are referred to by a `de Bruijn Index`, (`#n`), and that tells you how many binders up the `Expr ` tree we should travel to find the binder that binds this variable.

If a `bvar` has a de Bruijn index that is larger then the number of binders:
lam `x _ (app #0 #1) or
λ x => x y
Then the  `bvar` is said to be "loose". If that happends, we want the `bvar` to turn into an `fvar`.

If there are no loose `bvar`s in an expression, it is said to be `closed`.
Replacing all instances of a loose `bvar` with an `Expr` is called `instantiation`.
Going the other way is called `abstraction`.

Some `Expr`s depend on universe levels, represented by `Lean.level` type. `.sort`s have a universe parameter, and `.const`s take a list of universe parameters. That means that their type depends on universe parameters.

Expr.const: constant defined earlier in lean document.
-/

open Lean
open Nat

def z₁ := Expr.const `zero []
#eval z₁ -- Lean.Expr.const `zero []

def z₂ := Expr.const ``zero []
#eval z₂ -- Lean.Expr.const `Nat.zero []

/-
The double backtick "resolves" the given name (finds the actually unique definition in the environment) to make it "fully qualified" (canonical name of definition, including prefix (Nat.zero))



-/
