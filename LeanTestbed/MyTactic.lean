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
5. Applying all terms in the context to the goal (if that won't throw an error)
6. Applying False.elim
-/

--dbg_trace f!"error: {← e.toMessageData.toString}\n"

elab "iff_intro_option" : tactic =>
  Lean.Elab.Tactic.withMainContext do
      let goal ← getMainGoal
      withoutModifyingState do
      let goalType ← Lean.Elab.Tactic.getMainTarget
      match ← whnf goalType with
        | (.app (.app (.const ``Iff _) P) Q) =>
          evalTactic (← `(tactic| apply Iff.intro))
          let newGoals ← getGoals
          dbg_trace f!"apply Iff.intro"
          dbg_trace f!"------------"
          for goal in newGoals do
            dbg_trace f!"{ ← ppGoal goal}\n"
        | _ => pure ()

elab "and_intro_option" : tactic =>
  Lean.Elab.Tactic.withMainContext do
      let goal ← getMainGoal
      withoutModifyingState do
      let goalType ← Lean.Elab.Tactic.getMainTarget
      match ← whnf goalType with
        | (.app (.app (.const ``And _) P) Q) =>
            evalTactic (← `(tactic| apply And.intro))
            let newGoals ← getGoals
            dbg_trace f!"apply And.intro"
            dbg_trace f!"------------"
            for goal in newGoals do
              dbg_trace f!"{ ← ppGoal goal}\n"
          | _ => pure ()

elab "intro_option" : tactic =>
  Lean.Elab.Tactic.withMainContext do
      let goal ← getMainGoal
      let ctx ← getLCtx
      withoutModifyingState do
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

elab "false_elim_option" : tactic =>
  Lean.Elab.Tactic.withMainContext do
      let goal ← getMainGoal
      withoutModifyingState do
        try
          evalTactic (← `(tactic| apply False.elim))
          let newGoals ← getGoals
          dbg_trace f!"apply False.elim"
          dbg_trace f!"------------"
          for goal in newGoals do
            dbg_trace f!"{← ppGoal goal}\n"
        catch e => pure ()

elab "apply_option" : tactic =>
  Lean.Elab.Tactic.withMainContext do
      let goal ← getMainGoal
      let ctx ← getLCtx
      for ldecl in ctx do
      if ldecl.isImplementationDetail then
        continue
      let expr := mkFVar ldecl.fvarId
      withoutModifyingState do
        try
          let newGoals ← goal.apply expr
          dbg_trace f!"apply {← ppExpr expr}"
          dbg_trace f!"------------"
          if newGoals.isEmpty then
            dbg_trace f!"Current goal solved!\n"
          else
            for goal in newGoals do
            dbg_trace f!"{ ← ppGoal goal}\n"
        catch e => pure ()

elab "and_decomp_option" : tactic =>
  Lean.Elab.Tactic.withMainContext do
      let goal ← getMainGoal
      let ctx ← getLCtx
      for ldecl in ctx do
      if ldecl.isImplementationDetail then
        continue
      let expr := mkFVar ldecl.fvarId
      withoutModifyingState do --
        let declType ← inferType expr
        let fresh := ctx.getUnusedName `h
        match ← whnf declType with
        | (.app (.app (.const ``And _) P) Q) =>
          let leftProof ← mkAppM ``And.left #[expr]
          let rightProof ← mkAppM ``And.right #[expr]
          let leftType ← inferType leftProof
          withoutModifyingState do
            try
              liftMetaTactic fun mvarId => do
                let mvarIdNew ← mvarId.define fresh (← inferType leftProof) leftProof
                let (_, mvarIdNew) ← mvarIdNew.intro1P
                return [mvarIdNew]
              let newGoal ← getMainGoal
              dbg_trace f!"let {fresh} := {← ppExpr leftProof}"
              dbg_trace f!"-----------------"
              dbg_trace f!"{← ppGoal newGoal}\n"
            catch e =>
              dbg_trace f!"error: {← e.toMessageData.toString}"
          withoutModifyingState do
            liftMetaTactic fun mvarId => do
                let mvarIdNew ← mvarId.define fresh (← inferType rightProof) rightProof
                let (_, mvarIdNew) ← mvarIdNew.intro1P
                return [mvarIdNew]
            let goal ← getMainGoal
            dbg_trace f!"let {fresh} := {← ppExpr rightProof}"
            dbg_trace f!"------------------"
            dbg_trace f!"{← ppGoal goal}\n"
        | _ => pure ()

elab "iff_decomp_option" : tactic =>
  Lean.Elab.Tactic.withMainContext do
      let goal ← getMainGoal
      let ctx ← getLCtx
      for ldecl in ctx do
      if ldecl.isImplementationDetail then
        continue
      let expr := mkFVar ldecl.fvarId
      withoutModifyingState do --
        let declType ← inferType expr
        let fresh := ctx.getUnusedName `h
        match ← whnf declType with
        | (.app (.app (.const ``Iff _) mp) mpr) =>
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

elab "so" : tactic =>
  Lean.Elab.Tactic.withMainContext do
  withoutModifyingState do
    evalTactic (← `(tactic| iff_intro_option))
    evalTactic (← `(tactic| and_intro_option))
    evalTactic (← `(tactic| intro_option))
    evalTactic (← `(tactic| false_elim_option))
    evalTactic (← `(tactic| apply_option))
    evalTactic (← `(tactic| and_decomp_option))
    evalTactic (← `(tactic| iff_decomp_option))




variable (p q r s: Prop)

-- From Theorem Proving in Lean 4:
example : p ∧ ¬q → ¬(p → q) := by
  intro h
  intro h_1
  let h_2 := h.right
  apply h_2
  let h_3 := h.left
  apply h_1
  apply h_3


example : (p → (q → r)) ↔ (p ∧ q → r) := by
  apply Iff.intro
  intro h
  intro h_1
  let h_2 := h_1.left
  let h_3 := h_1.right
  apply h
  apply h_2
  apply h_3
  intro h
  intro h_1
  intro h_2
  apply h
  apply And.intro
  apply h_1
  apply h_2
