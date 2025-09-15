import Lean

open Lean Lean.Expr Lean.Meta Lean.Elab.Tactic
set_option linter.unusedVariables false
/-
**Tactic Scope** (I belive)
If a (provable) theorem involves only `∧`, `∨`, `→`, `↔`, `False`, and variables of type `Prop`, then there exists a choice from the options presented by `so` that will solve the theorem.

The tactic will show options related to:
1. Splitting the goal with Iff.intro
2. Decomposing terms of type Iff intro mp and mpr
3. Splitting the goal with And.intro
4. Decomposing terms of type And into left and right
5. Applying all terms in the context to the goal (if that won't throw an error)
6. Applying False.elim
7. Splitting hypothesis of type Or using cases
8. Proving goals of type Or with Or.inl or Or.inl
-/

--  dbg_trace f!"error: {← e.toMessageData.toString}\n"
-- Note: maybe want to focus on first goal when feeding info to RL so that it can focus on what it needs to atm
-- Infoview chooser!
-- Could do this procedurally
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
          dbg_trace f!"---------------"
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
          dbg_trace f!"---------------"
          for goal in newGoals do
            dbg_trace f!"{ ← ppGoal goal}\n"
        | _ => pure ()

elab "or_intro_option" : tactic =>
  Lean.Elab.Tactic.withMainContext do
      let goal ← getMainGoal
      withoutModifyingState do
      let goalType ← Lean.Elab.Tactic.getMainTarget
      match ← whnf goalType with
        | (.app (.app (.const ``Or _) mp) mpr) =>
          withoutModifyingState do
            evalTactic (← `(tactic| apply Or.inl))
            let newGoals ← getGoals
            dbg_trace f!"apply Or.inl"
            dbg_trace f!"------------"
            for goal in newGoals do
              dbg_trace f!"{ ← ppGoal goal}\n"
          withoutModifyingState do
            evalTactic (← `(tactic| apply Or.inr))
            let newGoals ← getGoals
            dbg_trace f!"apply Or.inr"
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
          dbg_trace f!"----------------"
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

elab "or_decomp_option" : tactic =>
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
        | (.app (.app (.const ``Or _) mp) mpr) =>
        let newNames : AltVarNames := ⟨ false, [fresh] ⟩
        let newGoals ← goal.cases ldecl.fvarId #[newNames, newNames]
        dbg_trace f!"cases { ← ppExpr expr} with | inl {fresh} | inr {fresh}"
        dbg_trace f!"------------------------------"
        for goal in newGoals do

            dbg_trace f!"{← ppGoal goal.mvarId}\n"
        | _ => pure ()


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
    evalTactic (← `(tactic| or_decomp_option))
    evalTactic (← `(tactic| or_intro_option))





variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro
  intro h
  apply And.intro
  let h_1 := h.right
  apply h_1
  let h_1 := h.left
  apply h_1
  intro h
  let h_1 := h.left
  let h_2 := h.right
  apply And.intro
  apply h_2
  apply h_1


example : p ∨ q ↔ q ∨ p := by
  apply Iff.intro
  intro h
  cases h with | inl h_1 | inr h_1
  apply Or.inr
  apply h_1
  apply Or.inl
  apply h_1
  intro h
  cases h with | inl h_1 | inr h_1
  apply Or.inr
  apply h_1
  apply Or.inl
  apply h_1

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  apply Iff.intro
  intro h
  let h_1 := h.left
  let h_2 := h.right
  let h_3 := h_1.left
  apply And.intro
  apply h_3
  let h_4 := h_1.right
  apply And.intro
  apply h_4
  apply h_2
  intro h
  let h_1 := h.left
  let h_2 := h.right
  let h_3 := h_2.left
  let h_4 := h_2.right
  apply And.intro
  apply And.intro
  apply h_1
  apply h_3
  apply h_4



example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  apply Iff.intro
  intro h
  cases h with | inl h_1 | inr h_1
  cases h_1 with | inl h | inr h
  apply Or.inl
  apply h
  apply Or.inr
  apply Or.inl
  apply h
  apply Or.inr
  apply Or.inr
  apply h_1
  intro h
  cases h with | inl h_1 | inr h_1
  apply Or.inl
  apply Or.inl
  apply h_1
  cases h_1 with | inl h | inr h
  apply Or.inl
  apply Or.inr
  apply h
  apply Or.inr
  apply h

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  intro h
  let h_1 := h.left
  let h_2 := h.right
  cases h_2 with | inl h_3 | inr h_3
  apply Or.inl
  apply And.intro
  apply h_1
  apply h_3
  cases h_2 with | inl h_4 | inr h_4
  apply Or.inl
  apply And.intro
  apply h_1
  apply h_4
  apply Or.inr
  apply And.intro
  apply h_1
  apply h_3
  intro h
  cases h with | inl h_1 | inr h_1
  let h := h_1.left
  let h_2 := h_1.right
  apply And.intro
  apply h
  apply Or.inl
  apply h_2
  let h := h_1.left
  let h_2 := h_1.right
  apply And.intro
  apply h
  apply Or.inr
  apply h_2

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  intro h
  cases h with | inl h_1 | inr h_1
  apply And.intro
  apply Or.inl
  apply h_1
  apply Or.inl
  apply h_1
  let h := h_1.left
  let h_2 := h_1.right
  apply And.intro
  apply Or.inr
  apply h
  apply Or.inr
  apply h_2
  intro h
  let h_1 := h.left
  let h_2 := h.right
  cases h_1 with | inl h_3 | inr h_3
  cases h_2 with | inl h_4 | inr h_4
  apply Or.inl
  apply h_3
  apply Or.inl
  apply h_3
  cases h_2 with | inl h_4 | inr h_4
  apply Or.inl
  apply h_4
  apply Or.inr
  apply And.intro
  apply h_3
  apply h_4

-- other properties
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




example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  apply Iff.intro
  intro h
  apply And.intro
  intro h_1
  apply h
  apply Or.inl
  apply h_1
  intro h_1
  apply h
  apply Or.inr
  apply h_1
  intro h
  intro h_1
  let h_2 := h.left
  let h_3 := h.right
  cases h_1 with | inl h_4 | inr h_4
  apply h_2
  apply h_4
  apply h_3
  apply h_4

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  apply Iff.intro
  intro h
  apply And.intro
  intro h_1
  apply h
  apply Or.inl
  apply h_1
  intro h_1
  apply h
  apply Or.inr
  apply h_1
  intro h
  intro h_1
  cases h_1 with | inl h_2 | inr h_2
  let h_1 := h.left
  let h_3 := h.right
  apply h_1
  apply h_2
  let h_1 := h.right
  apply h_1
  apply h_2

example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro h
  intro h_1
  cases h with | inl h_2 | inr h_2
  let h := h_1.left
  apply h_2
  apply h
  let h := h_1.right
  apply h_2
  apply h

example : ¬(p ∧ ¬p) :=  by
  intro h
  let h_1 := h.left
  let h_2 := h.right
  apply h_2
  apply h_1

example : p ∧ ¬q → ¬(p → q) := by
  intro h
  intro h_1
  let h_2 := h.left
  let h_3 := h.right
  apply h_3
  apply h_1
  apply h_2

example : ¬p → (p → q) := by
  intro h
  intro h_1
  apply False.elim
  apply h
  apply h_1


example : (¬p ∨ q) → (p → q) := by
  intro h
  intro h_1
  cases h with | inl h_2 | inr h_2
  apply False.elim
  apply h_2
  apply h_1
  apply h_2

example : p ∨ False ↔ p := by
  apply Iff.intro
  intro h
  cases h with | inl h_1 | inr h_1
  apply h_1
  apply False.elim
  apply h_1
  intro h
  apply Or.inl
  apply h

example : p ∧ False ↔ False := by
  apply Iff.intro
  intro h
  let h_1 := h.right
  apply h_1
  intro h
  apply False.elim
  apply h

example : (p → q) → (¬q → ¬p) := by
  intro h
  intro h_1
  intro h_2
  apply h_1
  apply h
  apply h_2
