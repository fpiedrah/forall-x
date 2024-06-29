theorem excluded_middle {P: Prop} : P ∨ ¬P := by
  by_cases h₁: P
  . left
    exact h₁
  . right
    exact h₁

theorem de_morgans_and {P Q: Prop} :  ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  . intro h₁
    by_cases h₂: P
    . right
      intro h₃
      apply h₁
      constructor
      . exact h₂
      . exact h₃
    . left
      exact h₂
  . intro h₁
    intro h₂
    obtain ⟨s₁, s₂⟩ := h₂
    cases h₁ with
    | inr h₃ => contradiction
    | inl h₃ => contradiction

theorem de_morgans_or {P Q: Prop} :  ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  . intro h₁
    constructor
    . intro h₂
      apply h₁
      left
      exact h₂
    . intro h₂
      apply h₁
      right
      exact h₂
  . intro h₁
    intro h₂
    obtain ⟨s₁, s₂⟩ := h₁
    cases h₂ with
    | inr h₃ => contradiction
    | inl h₃ => contradiction
