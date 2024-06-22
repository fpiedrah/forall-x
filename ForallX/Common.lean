theorem MTP {P Q: Prop} : ((P ∨ Q) ∧ ¬P) → Q := by
  intro h₀
  obtain ⟨h₁, h₂⟩ := h₀
  cases h₁ with
  | inl h₃ => contradiction
  | inr h₃ => exact h₃

theorem MP {P Q: Prop} : ((P → Q) ∧ P) → Q := by
  intro h₀
  obtain ⟨h₁, h₂⟩ := h₀
  specialize h₁ h₂
  exact h₁

theorem MT {P Q: Prop} : ((P → Q) ∧ ¬Q) → ¬P := by
  intro h₀
  intro h₁
  obtain ⟨h₂, h₃⟩ := h₀
  specialize h₂ h₁
  apply h₃
  exact h₂

theorem DN {P: Prop} : ¬¬P ↔ P := by
  constructor
  . intro h₁
    by_cases h₂: P
    . exact h₂
    . contradiction
  . intro h₁
    intro h₂
    contradiction

theorem DMₒ {P Q: Prop} : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  . intro h₁
    by_cases h₂: P
    . constructor
      . intro a
        apply h₁
        left
        exact a
      . intro b
        apply h₁
        right
        exact b
    . constructor
      . exact h₂
      . intro b
        apply h₁
        right
        exact b
  . intro h₁
    intro h₂
    obtain ⟨not_a, not_b⟩ := h₁
    cases h₂ with
    | inr b => contradiction
    | inl a => contradiction

theorem DMₐ {P Q: Prop} : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
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
    obtain ⟨a, b⟩ := h₂
    cases h₁ with
    | inl h₃ => . contradiction
    | inr h₃ => . contradiction

theorem or_commutativity {P Q: Prop} : P ∨ Q ↔ Q ∨ P := by
  constructor
  . intro h₁
    cases h₁ with
    | inl h₂ => . right
                  exact h₂
    | inr h₂ => . left
                  exact h₂
  . intro h₁
    cases h₁ with
    | inl h₂ => . right
                  exact h₂
    | inr h₂ => . left
                  exact h₂
