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
elab "so" : tactic =>
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
      catch e =>
        --dbg_trace f!"error: {← e.toMessageData.toString}\n"

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
        catch e =>
          dbg_trace f!""
        -- withoutModifyingState do
        --   match ← whnf epxr with
        --   | (.app (.app (.const ``And _) P) Q) =>
        --     dbg_trace f!"Expression {expr} is an And."
        --   | _ =>







            --dbg_trace f!"error: {← e.toMessageData.toString}\n"


/-
Please try it out! Bonus points if you can break the tactic.
-/

variable (p q : Prop)


-- 1. Identity
theorem imp_self' : p → p := by
  sorry

-- 2. Implication introduction / transitivity
theorem imp_trans : (p → q) → p → q := by
  sorry

-- 3. Currying
theorem curry : (p → q) → (p → p → q) := by
  sorry
-- 4. Uncurrying
theorem uncurry : (p → p → q) → (p → q) := by
  intro h
  intro h_1
  apply h
  apply h_1
  apply h_1



-- 5. Double implication
theorem imp_chain : (p → q) → (q → p) → p → p := by
  sorry
-- 6. Weakening on the right
theorem weaken_right : p → (q → p) := by
  sorry

-- 7. Weakening on the left
theorem weaken_left : (p → q) → (p → (q → q)) := by
  sorry

-- 8. Implication duplication
theorem imp_dup' : (p → q) → (p → p → q) := by
  sorry

-- 9. Composition
theorem comp : (q → p) → (p → q) → p → p := by
  sorry

-- 10. Tautology with implication nesting
theorem nested : p → (q → p) := by
  sorry

variable (p q r s t u v : Prop)

theorem complex_imp :
  (p → q → r) →
  (r → s → t) →
  (t → u) →
  (u → v) →
  (p → q) →
  (p → s) →
  p →
  v :=
by
  intro h
  intro h_1
  intro h_2
  intro h_3
  intro h_4
  intro h_5
  intro h_6
  apply h_3
  apply h_2
  apply h_1
  apply h
  apply h_6
  apply h_4
  apply h_6
  apply h_5
  apply h_6
