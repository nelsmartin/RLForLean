import Lean

open Lean Lean.Expr Lean.Meta Lean.Elab.Tactic
set_option linter.unusedVariables false

/-
**Tactic Scope** (I belive)
If a (provable) theorem involves only `And`, `→`, `↔`, `False`, and variables of type `Prop`, then there exists a choice from the options presented by `so` that will solve the theorem.

The tactic will show options related to:
1. Splitting the goal with Iff.intro
2. Decomposing terms of type Iff intro mp and mpr
3. Splitting the goal with And.intro
4. Decomposing terms of type And into left and right
5. Applying all terms in the context to the goal (that don't throw an error)
6. Applying False.elim



-/
elab "so" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← getMainGoal
    let ctx ← getLCtx
    withoutModifyingState do -- apply Iff.intro
      let goalType ← Lean.Elab.Tactic.getMainTarget
      match ← whnf goalType with
          | (.app (.app (.const ``Iff _) P) Q) =>
            let newGoals ← goal.apply (mkConst ``Iff.intro)
            dbg_trace f!"apply Iff.intro"
            dbg_trace f!"------------"
            for goal in newGoals do
              dbg_trace f!"{ ← ppGoal goal}\n"
          | _ => pure ()

    withoutModifyingState do -- apply And.intro
      let goalType ← Lean.Elab.Tactic.getMainTarget
      match ← whnf goalType with
          | (.app (.app (.const ``And _) P) Q) =>
            let newGoals ← goal.apply (mkConst ``And.intro)
            dbg_trace f!"apply And.intro"
            dbg_trace f!"------------"
            for goal in newGoals do
              dbg_trace f!"{ ← ppGoal goal}\n"
          | _ => pure ()

    withoutModifyingState do -- intro
      try
        let fresh := ctx.getUnusedName `h
        let (fvarId, newGoal) ← goal.intro1
        dbg_trace f!"intro {fresh}"
        dbg_trace f!"------------"
        let renamedGoal ← newGoal.rename fvarId fresh
        renamedGoal.withContext do
          let newFVar := mkFVar fvarId
          let fVarType ← inferType newFVar
          dbg_trace f!"{← ppGoal renamedGoal}\n"
      catch e => pure ()
        --dbg_trace f!"error: {← e.toMessageData.toString}\n"

    withoutModifyingState do -- apply False.elim
      try
        let goalType ← goal.getType
        let u ← getLevel goalType
        evalTactic (← `(tactic| apply False.elim))
        let newGoals ← getGoals
        dbg_trace f!"apply False.elim"
        dbg_trace f!"------------"
        for goal in newGoals do
          dbg_trace f!"{← ppGoal goal}\n"
      catch e => --pure ()
      dbg_trace f!"This {← e.toMessageData.toString}\nHello"

    for ldecl in ctx do
      if ldecl.isImplementationDetail then
        continue
      let expr := mkFVar ldecl.fvarId
      withoutModifyingState do -- apply <eachTerm>
        try
          let newGoals ← goal.apply expr
          dbg_trace f!"apply {← ppExpr expr}!!!!!"
          dbg_trace f!"------------"
          if newGoals.isEmpty then
            dbg_trace f!"Current goal solved!\n"
          else
            for goal in newGoals do
            dbg_trace f!"{ ← ppGoal goal}\n"
        catch e => pure ()

        withoutModifyingState do --
        let declType ← inferType expr
        let fresh := ctx.getUnusedName `h
          match ← whnf declType with
          | (.app (.app (.const ``And _) P) Q) => -- Decompose And terms

            let leftProof ← mkAppM ``And.left #[expr]
            let rightProof ← mkAppM ``And.right #[expr]
            withoutModifyingState do
              liftMetaTactic fun mvarId => do
                let mvarIdNew ← mvarId.define fresh (← inferType leftProof) leftProof
                let (_, mvarIdNew) ← mvarIdNew.intro1P
                return [mvarIdNew]
              let goal ← getMainGoal
              dbg_trace f!"let {fresh} := {← ppExpr leftProof}"
              dbg_trace f!"-----------------"
              dbg_trace f!"{← ppGoal goal}\n"
            withoutModifyingState do
              liftMetaTactic fun mvarId => do
                let mvarIdNew ← mvarId.define fresh (← inferType rightProof) rightProof
                let (_, mvarIdNew) ← mvarIdNew.intro1P
                return [mvarIdNew]
              let goal ← getMainGoal
              dbg_trace f!"let {fresh} := {← ppExpr rightProof}"
              dbg_trace f!"------------------"
              dbg_trace f!"{← ppGoal goal}\n"
          | (.app (.app (.const ``Iff _) mp) mpr) => -- Decompose Iff terms
            let leftProof ← mkAppM ``Iff.mp #[expr]
            let rightProof ← mkAppM ``Iff.mpr #[expr]
            withoutModifyingState do
              liftMetaTactic fun mvarId => do
                let mvarIdNew ← mvarId.define fresh (← inferType leftProof) leftProof
                let (_, mvarIdNew) ← mvarIdNew.intro1P
                return [mvarIdNew]
              let goal ← getMainGoal
              dbg_trace f!"let {fresh} := {← ppExpr leftProof}"
              dbg_trace f!"-----------------"
              dbg_trace f!"{← ppGoal goal}\n"
            withoutModifyingState do
              liftMetaTactic fun mvarId => do
                let mvarIdNew ← mvarId.define fresh (← inferType rightProof) rightProof
                let (_, mvarIdNew) ← mvarIdNew.intro1P
                return [mvarIdNew]
              let goal ← getMainGoal
              dbg_trace f!"let {fresh} := {← ppExpr rightProof}"
              dbg_trace f!"-----------------"
              dbg_trace f!"{← ppGoal goal}\n"
          | _ =>
            pure ()



/-
Please try it out! Bonus points if you can break the tactic.
-/

variable (p q r s : Prop)

example : ((p ∧ q) → r) ∧ (s → False) ↔ ((p ∧ q → r) ∧ ¬s) := by
  apply Iff.intro
  intro h
  so
