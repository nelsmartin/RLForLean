import Lean

open Lean Lean.Expr Lean.Meta Lean.Elab.Tactic
set_option linter.unusedVariables false

/-
Usage:
Use `so` (short for show_options) at each step in the proof to see what the possible next moves are, as well the proof state that would result from using the given tactic.
-/

/-
Could check types before trying intro or apply; is that faster than just applying it?
-/

/-
Next:
If goal is of type Iff, apply Iff.intro
If term is of type Iff, let h_1 := h.mp, mpr

For Or:
Use Or.elim to prove goals of type or ()

-/
elab "so" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← getMainGoal
    let ctx ← getLCtx
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

    withoutModifyingState do -- apply False.elim
      try
        let goalType ← goal.getType
        let u ← getLevel goalType
        let elim := mkApp (mkConst ``False.elim [u]) goalType
        let newGoals ← goal.apply elim
        dbg_trace f!"apply False.elim"
        dbg_trace f!"------------"
        for goal in newGoals do
          dbg_trace f!"{← ppGoal goal}\n"
      catch e => dbg_trace f!"{← e.toMessageData.toString}\n"

    for ldecl in ctx do
      if ldecl.isImplementationDetail then
        continue
      let expr := mkFVar ldecl.fvarId
      withoutModifyingState do -- apply <eachTerm>
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

        withoutModifyingState do -- And.left and and.right
        let declType ← inferType expr
          match ← whnf declType with
          | (.app (.app (.const ``And _) P) Q) =>
            let fresh := ctx.getUnusedName `h
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
          | _ =>
            pure ()





/-
Please try it out! Bonus points if you can break the tactic.
-/

variable (p q r s : Prop)

example : (p ↔ q) → p → q := by
  intro h
  let hx := h.mp
  exact hx


theorem complex_and_false
  (h₁ : p ∧ q)       -- evidence of an And
  (h₂ : q → r)
  (h₃ : r → s)
  (h₄ : False → p) :
  (p ∧ r) ∧ (q ∧ s) := by
  apply And.intro
  apply And.intro
  let h := h₁.left
  apply h
  apply h₂
  let h := h₁.right
  apply h
  apply And.intro
  let h := h₁.right
  apply h
  apply h₃
  apply h₂
  let h := h₁.right
  apply h

example : p ∧ ¬q → ¬(p → q) := by
  intro h
  intro h_1
  let h_2 := h.right
  apply h_2
  apply h_1
  let h_3 := h.left
  apply h_3
