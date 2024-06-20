example {A : Prop} (h₁: ¬¬A) : A := by
  by_cases h₂: A
  . exact h₂
  . contradiction

example {A B: Prop} (h₁: ¬A → ¬B) : B → A := by
  intro b
  by_cases h₂: A
  . exact h₂
  . specialize h₁ h₂
    contradiction

example {A B: Prop} (h₁: A → B) : ¬A ∨ B := by
  by_cases h₂: A
  . right
    specialize h₁ h₂
    exact h₁
  . left
    exact h₂

example {A B: Prop} : ¬(A ∧ B) → (¬A ∨ ¬B) := by
  intro not_a_and_b
  by_cases h₁: A
  . right
    intro b
    apply not_a_and_b
    constructor
    . exact h₁
    . exact b
  . left
    exact h₁

example {A B C: Prop} (h₁: A → (B ∨ C)) : (A → B) ∨ (A → C) := by
  by_cases h₁: (A → B)
  . left
    exact h₁
  . rw [not_imp] at h₁
    obtain ⟨a, not_b⟩ := h₁
    specialize h₁ a
    cases h₁ with
    | inl h₃ => . contradiction
    | inr h₃ => . right
                  intro _
                  exact h₃

example {A B: Prop} : (A → B) ∨ (B → A) := by
  by_cases h₁: A
  . right
    intro _
    exact h₁
  . left
    intro h₃
    contradiction

example {A B: Prop} : ((A → B) → A) → A := by
  intro h₁
  by_cases h₂: A
  . exact h₂
  . apply h₁
    intro h₃
    contradiction
