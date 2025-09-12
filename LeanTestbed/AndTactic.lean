import Lean

open Lean Lean.Expr Lean.Meta Lean.Elab.Tactic
set_option linter.unusedVariables false

variable (p q : Prop)


example (h : p ∧ q) : q ∧ p := by
    let h_1 := h.left
    let h_2 := h.right
    apply And.intro
    apply h_2
    apply h_1
