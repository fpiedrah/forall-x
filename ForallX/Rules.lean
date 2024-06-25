theorem modus_ponens {P Q: Prop} : ((P → Q) ∧ P) → Q := by
  intro h₁
  obtain ⟨s₁, s₂⟩ := h₁
  specialize s₁ s₂
  exact s₁
