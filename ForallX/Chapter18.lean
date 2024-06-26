import Mathlib.Init.Classical
import ForallX.Rules


example {A B: Prop} (p₁: A → B) (p₂: A → C) : A → (B ∧ C) := by
  intro h₁
  have s₁: B := modus_ponens ⟨p₁, h₁⟩
  have s₂: C := modus_ponens ⟨p₂, h₁⟩
  constructor
  . exact s₁
  . exact s₂

example {A B C: Prop} (p₁: (A ∧ B) → C) : A → (B → C) := by
  intro h₁
  intro h₂
  have s₁: A ∧ B := by
    constructor
    . exact h₁
    . exact h₂
  have s₂: C := modus_ponens ⟨p₁, s₁⟩
  exact s₂

example {A B C: Prop} (p₁: A → (B → C)) : (A → B) → (A → C) := by
  intro h₁
  intro h₂
  have s₁: B → C := modus_ponens ⟨p₁, h₂⟩
  have s₂: B := modus_ponens ⟨h₁, h₂⟩
  have s₃: C := modus_ponens ⟨s₁, s₂⟩
  exact s₃

example {A B C: Prop} (p₁: A ∨ (B ∧ C)) : (A ∨ B) ∧ (A ∨ C) := by
  constructor
  . cases p₁ with
    | inr h₁ =>
      . right
        obtain ⟨s₁, _⟩ := h₁
        exact s₁
    | inl h₁ =>
      . left
        exact h₁
  . cases p₁ with
    | inr h₁ =>
      . right
        obtain ⟨_, s₁⟩ := h₁
        exact s₁
    | inl h₁ =>
      . left
        exact h₁

example {A B C: Prop} (p₁: (A ∧ B) ∨ (A ∧ C)) : A ∧ (B ∨ C) := by
  constructor
  . cases p₁ with
    | inr h₁ =>
      . obtain ⟨s₁, _⟩ := h₁
        exact s₁
    | inl h₁ =>
      . obtain ⟨s₁, _⟩ := h₁
        exact s₁
  . cases p₁ with
    | inr h₁ =>
      . right
        obtain ⟨_, s₁⟩ := h₁
        exact s₁
    | inl h₁ =>
      . left
        obtain ⟨_, s₁⟩ := h₁
        exact s₁

example {A B C D: Prop} (p₁: A ∨ B) (p₂: A → C) (p₃: B → D) : C ∨ D := by
  cases p₁ with
    | inr h₁ =>
      . right
        have s₁: D := modus_ponens ⟨p₃, h₁⟩
        exact s₁
    | inl h₁ =>
      . left
        have s₁: C := modus_ponens ⟨p₂, h₁⟩
        exact s₁

example {A B: Prop} (p₁: ¬A ∨ ¬B) : ¬(A ∧ B) := by
  intro h₁
  obtain ⟨s₁, s₂⟩ := h₁
  cases p₁ with
    | inr h₁ =>
      . apply h₁
        exact s₂
    | inl h₁ =>
      . apply h₁
        exact s₁

example {A B: Prop} (p₁: A ∧ ¬B) : ¬(A → B) := by
  intro h₁
  obtain ⟨s₁, s₂⟩ := p₁
  apply s₂
  have s₃: B := modus_ponens ⟨h₁, s₁⟩
  exact s₃

example {A: Prop} : ¬(A ∧ ¬A) := by
  intro h₁
  obtain ⟨s₁, s₂⟩ := h₁
  apply s₂
  exact s₁

example {A B C: Prop} : ((A → C) ∧ (B → C)) → ((A ∨ B) → C) := by
  intro h₁
  intro h₂
  obtain ⟨s₁, s₂⟩ := h₁
  cases h₂ with
  | inr h₁ =>
    . have s₃: C := modus_ponens ⟨s₂, h₁⟩
      exact s₃
  | inl h₁ =>
    . have s₃: C := modus_ponens ⟨s₁, h₁⟩
      exact s₃

example {A B: Prop} : ¬(A → B) → (A ∧ ¬ B) := by
  intro h₁
  constructor
  . by_contra h₂
    apply h₁
    intro h₃
    contradiction
  . intro h₂
    apply h₁
    intro _
    exact h₂

example {A B: Prop} : (¬A ∨ B) → (A → B) := by
  intro h₁
  cases h₁ with
  | inr h₂ =>
    . intro _
      exact h₂
  | inl h₂ =>
    . intro h₃
      contradiction

example {A: Prop} : ¬¬A → A := by
  intro h₁
  by_cases h₂: A
  . exact h₂
  . contradiction

example {A B: Prop} (p₁: ¬A → ¬B) : B → A := by
  intro h₁
  by_contra h₂
  have s₁: ¬B := modus_ponens ⟨p₁, h₂⟩
  contradiction

example {A B: Prop} (p₁: A → B) : ¬A ∨ B := by
  by_cases h₁: A
  . right
    have s₁: B := modus_ponens ⟨p₁, h₁⟩
    exact s₁
  . left
    exact h₁

example {A B: Prop} : ¬(A ∧ B) → (¬A ∨ ¬B) := by
  intro h₁
  by_cases h₂: A
  . right
    intro h₃
    apply h₁
    constructor
    . exact h₂
    . exact h₃
  . left
    intro h₃
    contradiction

example {A B C: Prop} (p₁: A → (B ∨ C)) : (A → B) ∨ (A → C) := by
  by_cases h₁: A
  . have s₁: B ∨ C := modus_ponens ⟨p₁, h₁⟩
    cases s₁ with
    | inr h₂ =>
      . right
        intro _
        exact h₂
    | inl h₂ =>
      . left
        intro _
        exact h₂
  . left
    intro h₃
    contradiction

example {A B: Prop} : (A → B) ∨ (B → A) := by
  by_cases h₁: A
  . right
    intro _
    exact h₁
  . left
    intro h₂
    contradiction

example {A B: Prop} : ((A → B) → A) → A := by
  intro h₁
  by_cases h₂: A
  . exact h₂
  . apply h₁
    intro h₃
    contradiction
