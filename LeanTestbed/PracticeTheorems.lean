variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := sorry

example : p ∨ q ↔ q ∨ p := by
  sorry
-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := sorry
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  sorry



example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry


/-
Note:

example : ((p ∧ q) → r) → (p → r) ∧ (q → r) := by
  apply Iff.intro
  apply False.elim
This fails but

-/

example : (¬p ∨ q) → (p → q) := by
intro h
intro h_1
cases h with | inl hnp | inr hq
apply False.elim
apply hnp
apply h_1
apply hq






example : (p ∨ q) → (q ∨ p) := by
  intro h
  cases h with | inl hnp | inr hq
  apply Or.inr
  apply hnp
  apply Or.inl
  apply hq
