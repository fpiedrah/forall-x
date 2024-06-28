theorem disjunctive_syllogism {P Q: Prop} : ((P ∨ Q) ∧ ¬P) → Q := by
  intro h₁
  obtain ⟨s₁, s₂⟩ := h₁
  cases s₁ with
  | inr h₂ => exact h₂
  | inl h₂ => contradiction

theorem modus_ponens {P Q: Prop} : ((P → Q) ∧ P) → Q := by
  intro h₁
  obtain ⟨s₁, s₂⟩ := h₁
  specialize s₁ s₂
  exact s₁

theorem modus_tollens {P Q: Prop} : ((P → Q) ∧ ¬Q) → ¬P := by
  intro h₁
  obtain ⟨s₁, s₂⟩ := h₁
  intro h₂
  have s₃: Q := modus_ponens ⟨s₁, h₂⟩
  apply s₂
  exact s₃

theorem double_negation {P: Prop} : ¬¬P ↔ P := by
  constructor
  . intro h₁
    by_cases h₂: P
    . exact h₂
    . contradiction
  . intro h₁
    by_cases h₂: P
    . intro h₃
      apply h₃
      exact h₂
    . contradiction

--  ???
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

theorem or_commutative {P Q: Prop} : (P ∨ Q) ↔ (Q ∨ P) := by
  constructor
  . intro h₁
    cases h₁ with
    | inr h₂ =>
      . left
        exact h₂
    | inl h₂ =>
      . right
        exact h₂
  . intro h₁
    cases h₁ with
    | inr h₂ =>
      . left
        exact h₂
    | inl h₂ =>
      . right
        exact h₂
