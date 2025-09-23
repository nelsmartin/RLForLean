import Lean
import Lean.Data.Json

open Lean Lean.Expr Lean.Meta Lean.Elab.Tactic
set_option linter.unusedVariables false
/-
This just outputs the JSON associated with the next choices, without proof statee.
-/



def optionToJson (option : String) (path : System.FilePath) : IO Unit := do
  let JSON := Json.obj {
    ("option", Json.str option)
  }
  IO.FS.withFile path IO.FS.Mode.write fun h => do
    h.putStr (JSON.pretty 2)

open Lean.Elab.Tactic in
elab "and_test" filePath:Parser.strLit : tactic =>
  withMainContext do
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
              let option := f!"let {fresh} := {← ppExpr leftProof}"
              optionToJson option.pretty filePath.getString
              dbg_trace option
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

variable (p q s r : Prop)


example (h : p ∧ q) : q := by
  and_test "output.json"
  sorry
