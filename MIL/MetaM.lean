import Lean

open Lean Lean.Expr Lean.Meta

/-
The MetaM monad allows us to give meaning to every expression.

**Metavariables as Goals**
Goals are internally represented by metavariables.
Each metavar has a context containing hypothesis and a target type (the goal).

A goal is closed by finding an expression e of the target type. Expression may contain `fvars` from the mvar's local context, but no others. Closing the goal corresponds to assigning the metavariable: ?m := e. They can also be seen as "holes" in target types.

-/
example {α} (a : α) (f : α → α) (h : ∀ a, f a = a) : f (f a) = a := by
  apply Eq.trans
  apply h
  apply h

/-
When working with MetaM, we have read-write access to a structure called MetavarContext that contains info about the currently declared metavars. Each metavariable is defined by a MVarId (a unique `name`).

To make a mvar:
`mkFreshExprMVar (type? : Option Expr) (kind := MetavarKind.natural)`
    `(userName := Name.anonymous) : MetaM Expr`

type?: the target type of the new metavariable. If none, the target type is Sort ?u, where ?u is a universe level metavariable.
kind: the metavariable kind. The default is usually correct.

userName: the new metavariable's user-facing name. This is what gets printed when the metavariable appears in a goal. Unlike the MVarId, this name does not need to be unique.

Returns an `Expr` that is a metavariable. Extract MVarId with `Lean.Expr.mvarId!`

The context of the mvar is inherited from the local context. To use a different context, use Lean.`Meta.mkFreshExprMVarAt`.

To assign mvars, use `Lean.MVarId.assign` with type
  `assign (mvarId : MVarId) (val : Expr) : MetaM Unit`

This updates `MetavarContext` with `?mvarId := val`. You must ensure:
  - mvarId is is not assigned yet, or the reassignment is definitionally equal to the old one
  - The assigned `val` has the right type.
  - `val` contains only fvars from the local context of mvarId.

To get info from declared mvars:
  Lean.MVarId.getDec : MVarId -> MetavarDecl struct.
  Lean.MVarId.getType

To get current assignment of mvar:
  Lean.getExprMVarAssignment?
To check whether mvar is assigned:
  Lean.MVarId.isAssigned

Important thing to do:
`Lean.Meta.instantiateMVars` with type
  `instantiateMVars : Expr → MetaM Expr`

Given an expression e, this command will replace every metavariable in e with its assignemnt. So if e contains ?m, and we assign ?m := a, then ?m will be replaced by a in e.

-/

#eval show MetaM Unit from do

  let mvar1 ← mkFreshExprMVar (Expr.const ``Nat []) (userName := `mvar1)
  -- mkmkFreshExprMVar () () >>= fun mvar1 => do
  let mvar2 ← mkFreshExprMVar (Expr.const ``Nat []) (userName := `mvar2)

  let mvar3 ← mkFreshExprMVar (← mkArrow (Expr.const ``Nat []) (Expr.const ``Nat [])) (userName := `mvar3)

  let printMVars: MetaM Unit := do
    IO.println s!" meta1 :{ ← instantiateMVars mvar1}"
    IO.println s!" meta2 :{ ← instantiateMVars mvar2}"
    IO.println s!" meta3 :{ ← instantiateMVars mvar3}"

  IO.println "Initially, all metavariables are unassigned:"
  printMVars

  -- Assign `mvar1 : Nat := ?mvar3 ?mvar2`.
  mvar1.mvarId!.assign (.app mvar3 mvar2)
  IO.println "After assigning mvar1:"
  printMVars

  -- Assign `mvar2 : Nat := 0`.
  mvar2.mvarId!.assign (.const ``Nat.zero [])
  IO.println "After assigning mvar2:"
  printMVars

  mvar3.mvarId!.assign (.const ``Nat.succ [])
  IO.println "After assigning mvar3:"
  printMVars


/-
`fvars` are defined in a given context by a unique name, so if the context changes, so does the type of the fvar.

WAIT a minute idea. We need to change the context because different goals have different contexts. For example with the "cases" tactic, each goal has a different context with different hypothesis (based on what was split with cases).

So, we update ambient context to match the goal we are currently working on. For example:

To get local context, use, getLCtx : MetaM LocalContext.

def someTactic (mvarId : MVarId) ... : ... :=
  mvarId.withContext do
    ...

Once local context is set, we can manipulate fvars (identified by a unique FVarId : Name):
To retrieve info about a local hypothesis:
  - Lean.FVarId.getDecl : FVarId → MetaM LocalDecl
To get info about local hypothesis from user-facing name: (USEFUL)
 - Lean.Meta.getLocalDeclFromUserName : Name → MetaM LocalDecl

To loop over all hypothesis in loca context:
 - for ldecl in ← getLCtx do
  if ldecl.isImplementationDetail then
    continue
  -- do something with the ldecl

  This skips hypothesis which are "implementation deets."
-/

def myAssumption(mvarId : MVarId) : MetaM Bool := do
  -- check that myvarId is not assigned
  mvarId.checkNotAssigned `myAssumption
  -- use local context of mvarId
  mvarId.withContext do
    -- The target is the type of `mvarId.
    let target ← mvarId.getType
    -- For each hypothesis in the local context:
    for ldecl in ← getLCtx do
      -- If the hypothesis is an implementation detail, skip it.
      if ldecl.isImplementationDetail then
        continue
    -- If the type of the hypothesis is definitionally equal to the target type:
      if ← isDefEq ldecl.type target then
        mvarId.assign ldecl.toExpr
      return true

    return false
/-
Lean only assignes mvars if the depth of the mvar is the same as the depth of the current MetavarContext, so if you want to create/change new metavars without changing current ones, you can increase MetavarContext depth, play with metavariables, the change it back.
-/

/-
**Transparency**
Expressions can be in normal form according to four different levels of transparency.
`reducable`,  `instances`, `default`, `all`
-/

/-
**Weak Head Normalization**
An expression is in weak head normal form if it has the form e = f x₁ ... xₙ and f can't be reduced further at the current transparency (Basically the outermost wrapper is reduced).

You can call `whnf` to put it in whnf.
-/

/-
**Definitional Equality**
To check whether two expressions are equal (their normal forms are equal at the current transparency), use Lean.Meta.isDefEq with type signature `isDefEq : Expr → Expr → MetaM Bool`.

If the expressions being compared contain unassigned metavariables, isDefEq will attempt to assign them to match the two expressions. The `kind` value of a metavariable determines the behavior of isDefEq.
-`Natural`: isDefEq may assign any metavariable (default).
-`Synthetic`: isDefEq may assign any variable, but avoids doing so if possible, and favors natural
  metavariables over synthetic.

- `Synthetic opaque`: isDefEq never assigns a metavariable.

**Constructing Applications**
MetaM has some functions that make constructing expressions easier.

-`mkAppM : Name → Array Expr → MetaM Expr`
  - Like mkAppN, but infers implicit args and universe levels.
-`mkAppM'`
  - Accepts an Expr instead of a `Name`, so can be used with non-const exprs.

- `mkAppOptM : Name → Array (Option Expr) → MetaM Expr`
  - Like above, but lets us choose which arguments to include and which to infer.

-/
/-
**Lambdas and Foralls**
- To construct lambdas, instead of doing the whole thing at once, do it in two steps:
1. Construct the body of the expression, using fvars to stand in for bvars
2. replace fvars with bvars while simultaneously adding the bindings.
-/
def doubleExpr₂ : MetaM Expr :=
  withLocalDecl `x BinderInfo.default (.const ``Nat []) λ x => do
    let body ← mkAppM ``Nat.add #[x, x]
    mkLambdaFVars #[x] body

#eval show MetaM _ from do
  ppExpr (← doubleExpr₂)
-- fun x => Nat.add x x

def myApply (goal : MVarId) (e : Expr) : MetaM (List MVarId) := do
  -- Check that the goal is not yet assigned.
  goal.checkNotAssigned `myApply
  -- Operate in the local context of the goal.
  goal.withContext do
    -- Get the goal's target type.
    let target ← goal.getType
    -- Get the type of the given expression.
    let type ← inferType e
    -- If `type` has the form `∀ (x₁ : T₁) ... (xₙ : Tₙ), U`, introduce new
    -- metavariables for the `xᵢ` and obtain the conclusion `U`. (If `type` does
    -- not have this form, `args` is empty and `conclusion = type`.)
    let (args, _, conclusion) ← forallMetaTelescopeReducing type
    -- If the conclusion unifies with the target:
    if ← isDefEq target conclusion then
      -- Assign the goal to `e x₁ ... xₙ`, where the `xᵢ` are the fresh
      -- metavariables in `args`.
      goal.assign (mkAppN e args)
      -- `isDefEq` may have assigned some of the `args`. Report the rest as new
      -- goals.
      let newGoals ← args.filterMapM λ mvar => do
        let mvarId := mvar.mvarId!
        if ! (← mvarId.isAssigned) && ! (← mvarId.isDelayedAssigned) then
          return some mvarId
        else
          return none
      return newGoals.toList
    -- If the conclusion does not unify with the target, throw an error.
    else
      throwTacticEx `myApply goal m!"{e} is not applicable to goal with target {target}"



elab "custom_sorry_0" : tactic => do
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    Lean.Elab.admitGoal goal

example : 1 = 2 := by
  custom_sorry_0
-- unsolved goals: ⊢ 1 = 2
