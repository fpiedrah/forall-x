import Mathlib.Init.Classical
import ForallX.Rules


-- A. Provide proof schemes that justify the inclusion of the third
--    and fourth De Morgan rules as derived rules.
example {P Q: Prop} :  ¬(P ∨ Q) → ¬P ∧ ¬Q := by
  intro h₁
  constructor
  . intro h₂
    apply h₁
    left
    exact h₂
  . intro h₂
    apply h₁
    right
    exact h₂

example {P Q: Prop} : ¬P ∧ ¬Q → ¬(P ∨ Q) := by
  intro h₁
  intro h₂
  obtain ⟨s₁, s₂⟩ := h₁
  cases h₂ with
  | inr h₃ => contradiction
  | inl h₃ => contradiction

-- C. Provide a proof of A ∨ ¬A. Then, give a proof that uses
--    only the basic rules.
example {P: Prop} : P ∨ ¬P := by
  by_contra h₁
  rw [de_morgans_or] at h₁
  obtain ⟨s₁, s₂⟩ := h₁
  contradiction

example {P: Prop} : P ∨ ¬P := by
  by_contra h₁
  have s₁: ¬P ∧ ¬¬P := by {
    constructor
    . intro h₂
      apply h₁
      left
      exact h₂
    . intro h₂
      apply h₁
      right
      exact h₂
  }
  obtain ⟨s₂, _⟩ := s₁
  apply h₁
  right
  exact s₂
