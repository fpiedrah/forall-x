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

theorem excluded_middle {P: Prop} : P ∨ ¬P := by
  by_cases h₁: P
  . left
    exact h₁
  . right
    exact h₁
