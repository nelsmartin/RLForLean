import LeanTestbed.MyTactic


variable (p q r s : Prop)

example : (p ∧ q) ↔ q ∧ p := by
  apply Iff.intro
  intro h
  apply And.intro
  let h_1 := h.left
  let h_2 := h.right
  apply h_2

  so "output.ndjson"
