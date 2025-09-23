import Lean
import Lean.Data.Json
import Lean.Data.Json

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

def optionToJson (option : String) (path : System.FilePath) : IO Unit := do
  let JSON := Json.obj {
    ("option", Json.str option)
  }
  IO.FS.withFile path IO.FS.Mode.append fun h => do
    h.putStr (JSON.compress)
    h.putStr "\n"
    dbg_trace option
    dbg_trace "--------"


def beforeStateToJson (goals : List MVarId) (path : System.FilePath) : MetaM Unit := do
  let mut goalList : Array Json := #[]
  for goal in goals do
    let goalFormat ← ppGoal goal
    let goalString := goalFormat.pretty 80
    let jsonGoal := Json.obj {
      ("goal", Json.str goalString)
    }
    goalList := goalList.push jsonGoal
  let JSON := Json.obj {
    ("before", Json.arr goalList)
  }
  IO.FS.withFile path IO.FS.Mode.append fun h => do
    h.putStr (JSON.compress)
    h.putStr "\n"

def afterStateToJson (goals : List MVarId) (path : System.FilePath) : MetaM Unit := do
  let mut goalList : Array Json := #[]
  if goals.isEmpty then do
    goalList := goalList.push (Json.str "Current goal solved!")
    dbg_trace f!"Current goal solved!\n"
  for goal in goals do
    let goalFormat ← ppGoal goal
    let goalString := goalFormat.pretty 80
    let jsonGoal := Json.obj {
      ("goal", Json.str goalString)
    }
    goalList := goalList.push jsonGoal
    dbg_trace f!"{ ← ppGoal goal}\n"
  let JSON := Json.obj {
    ("after", Json.arr goalList)
  }
  IO.FS.withFile path IO.FS.Mode.append fun h => do
    h.putStr (JSON.compress)
    h.putStr "\n"


open Lean.Elab.Tactic in
elab "iff_intro_option" filePath:Parser.strLit : tactic =>
  Lean.Elab.Tactic.withMainContext do
      withoutModifyingState do
      let goalType ← Lean.Elab.Tactic.getMainTarget
      match ← whnf goalType with
        | (.app (.app (.const ``Iff _) P) Q) =>
          beforeStateToJson (← getGoals) filePath.getString
          evalTactic (← `(tactic| apply Iff.intro))
          let newGoals ← getGoals
          let option := f!"apply Iff.intro"
          optionToJson option.pretty filePath.getString
          afterStateToJson newGoals filePath.getString
        | _ => pure ()

open Lean.Elab.Tactic in
elab "and_intro_option" filePath:Parser.strLit : tactic =>
  Lean.Elab.Tactic.withMainContext do
      withoutModifyingState do
      let goalType ← Lean.Elab.Tactic.getMainTarget
      match ← whnf goalType with
        | (.app (.app (.const ``And _) P) Q) =>
          beforeStateToJson ( ← getGoals)  filePath.getString
          evalTactic (← `(tactic| apply And.intro))
          let newGoals ← getGoals
          let option := f!"apply And.intro"
          optionToJson option.pretty filePath.getString
          afterStateToJson newGoals filePath.getString
        | _ => pure ()

open Lean.Elab.Tactic in
elab "or_intro_option" filePath:Parser.strLit : tactic =>
  Lean.Elab.Tactic.withMainContext do
      withoutModifyingState do
      let goalType ← Lean.Elab.Tactic.getMainTarget
      match ← whnf goalType with
        | (.app (.app (.const ``Or _) mp) mpr) =>
          withoutModifyingState do
            beforeStateToJson (← getGoals) filePath.getString
            evalTactic (← `(tactic| apply Or.inl))
            let newGoals ← getGoals
            let option := f!"apply Or.inl"
            optionToJson option.pretty filePath.getString
            afterStateToJson newGoals filePath.getString
          withoutModifyingState do
            beforeStateToJson (← getGoals) filePath.getString
            evalTactic (← `(tactic| apply Or.inr))
            let newGoals ← getGoals
            let option := f!"apply Or.inr"
            optionToJson option.pretty filePath.getString
            afterStateToJson newGoals filePath.getString
        | _ => pure ()

open Lean.Elab.Tactic in
elab "intro_option" filePath:Parser.strLit : tactic =>
  Lean.Elab.Tactic.withMainContext do
      let goal ← getMainGoal
      let ctx ← getLCtx
      withoutModifyingState do
        try
          let fresh := ctx.getUnusedName `h
          let (fvarId, newGoal) ← goal.intro1
          beforeStateToJson (← getGoals) filePath.getString
          let option := f!"intro {fresh}"
          optionToJson option.pretty filePath.getString
          let renamedGoal ← newGoal.rename fvarId fresh
          renamedGoal.withContext do
            let newFVar := mkFVar fvarId
            let fVarType ← inferType newFVar
            afterStateToJson [renamedGoal] filePath.getString
        catch e => pure ()

open Lean.Elab.Tactic in
elab "false_elim_option" filePath:Parser.strLit : tactic =>
  Lean.Elab.Tactic.withMainContext do
      beforeStateToJson (← getGoals) filePath.getString
      withoutModifyingState do
        try
          evalTactic (← `(tactic| apply False.elim))
          let newGoals ← getGoals
          let option := f!"apply False.elim"
          optionToJson option.pretty filePath.getString
          afterStateToJson newGoals filePath.getString
        catch e => pure ()

open Lean.Elab.Tactic in
elab "apply_option" filePath:Parser.strLit : tactic =>
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
          beforeStateToJson (← getGoals) filePath.getString
          let option := f!"apply {← ppExpr expr}"
          optionToJson option.pretty filePath.getString
          afterStateToJson newGoals filePath.getString
        catch e => pure ()

open Lean.Elab.Tactic in
elab "and_decomp_option" filePath:Parser.strLit : tactic =>
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
            withoutModifyingState do
                beforeStateToJson (← getGoals) filePath.getString
                liftMetaTactic fun mvarId => do
                  let mvarIdNew ← mvarId.define fresh (← inferType leftProof) leftProof
                  let (_, mvarIdNew) ← mvarIdNew.intro1P
                  return [mvarIdNew]
                let newGoals ← getGoals
                let option := f!"let {fresh} := {← ppExpr leftProof}"
                optionToJson option.pretty filePath.getString
                afterStateToJson newGoals filePath.getString
            withoutModifyingState do
              beforeStateToJson (← getGoals) filePath.getString
              liftMetaTactic fun mvarId => do
                  let mvarIdNew ← mvarId.define fresh (← inferType rightProof) rightProof
                  let (_, mvarIdNew) ← mvarIdNew.intro1P
                  return [mvarIdNew]
              let newGoals ← getGoals
              let option := f!"let {fresh} := {← ppExpr rightProof}"
              optionToJson option.pretty filePath.getString
              dbg_trace option
              afterStateToJson newGoals filePath.getString
          | _ => pure ()

open Lean.Elab.Tactic in
elab "iff_decomp_option" filePath:Parser.strLit : tactic =>
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
              beforeStateToJson (← getGoals) filePath.getString
              liftMetaTactic fun mvarId => do
                let mvarIdNew ← mvarId.define fresh (← inferType leftProof) leftProof
                let (_, mvarIdNew) ← mvarIdNew.intro1P
                return [mvarIdNew]
              let newGoals ← getGoals
              let option := f!"let {fresh} := {← ppExpr leftProof}"
              optionToJson option.pretty filePath.getString
              afterStateToJson newGoals filePath.getString
            withoutModifyingState do
              beforeStateToJson (← getGoals) filePath.getString
              liftMetaTactic fun mvarId => do
                let mvarIdNew ← mvarId.define fresh (← inferType rightProof) rightProof
                let (_, mvarIdNew) ← mvarIdNew.intro1P
                return [mvarIdNew]
              let newGoals ← getGoals
              let option := f!"let {fresh} := {← ppExpr rightProof}"
              optionToJson option.pretty filePath.getString
              afterStateToJson newGoals filePath.getString
          | _ =>
            pure ()

open Lean.Elab.Tactic in
elab "or_decomp_option" filePath:Parser.strLit : tactic =>
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
          beforeStateToJson (← getGoals) filePath.getString
          let newNames : AltVarNames := ⟨ false, [fresh] ⟩
          let newGoals ← goal.cases ldecl.fvarId #[newNames, newNames]
          let option := f!"cases { ← ppExpr expr} with | inl {fresh} | inr {fresh}"
          optionToJson option.pretty filePath.getString
          afterStateToJson (newGoals.map (·.mvarId)).toList filePath.getString
        | _ => pure ()

open Lean.Elab.Tactic in
elab "so" filePath:Parser.strLit :  tactic  =>
  Lean.Elab.Tactic.withMainContext do
  withoutModifyingState do
    evalTactic (← `(tactic| iff_intro_option $filePath:str))
    evalTactic (← `(tactic| and_intro_option $filePath:str))
    evalTactic (← `(tactic| intro_option $filePath:str))
    evalTactic (← `(tactic| false_elim_option $filePath:str))
    evalTactic (← `(tactic| apply_option $filePath:str))
    evalTactic (← `(tactic| and_decomp_option $filePath:str))
    evalTactic (← `(tactic| iff_decomp_option $filePath:str))
    evalTactic (← `(tactic| or_decomp_option $filePath:str))
    evalTactic (← `(tactic| or_intro_option $filePath:str))


def path := "output.json"
def other := "other.json"

variable (p q s r : Prop)


-- example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
--   apply Iff.intro
--   intro h
--   let h_1 := h.left
--   let h_2 := h.right
--   let h_3 := h_1.left
--   apply And.intro
--   apply h_3
--   let h_4 := h_1.right
--   apply And.intro
--   apply h_4
--   apply h_2
--   intro h
--   so "output.ndjson"
--   sorry
