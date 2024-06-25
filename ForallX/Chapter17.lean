import Mathlib.Init.Classical
import ForallX.Rules


example {J: Prop} (p₁: J  → ¬J) : ¬J := by
  intro h₁
  have w₁ : ¬J := modus_ponens ⟨p₁, h₁⟩
  apply w₁
  exact h₁

example {Q: Prop} (p₁: Q → (Q ∧ ¬Q)) : ¬Q := by
  intro h₁
  have w₁ : Q ∧ ¬Q := modus_ponens ⟨p₁, h₁⟩
  obtain ⟨w₂, w₃⟩ := w₁
  apply w₃
  exact w₂

example {A B C: Prop} (p₁: A → (B → C)) : (A ∧ B) → C := by
  intro h₁
  obtain ⟨w₁, w₂⟩ := h₁
  have w₃ : B → C := modus_ponens ⟨p₁, w₁⟩
  have w₄ : C := modus_ponens ⟨w₃, w₂⟩
  exact w₄

example {K L: Prop} (p₁: K ∧ L) : K ↔ L := by
  obtain ⟨w₁, w₂⟩ := p₁
  constructor
  . intro _
    exact w₂
  . intro _
    exact w₁

example {C D E: Prop} (p₁: (C ∧ D) ∨ E) : E ∨ D := by
  cases p₁ with
  | inl w₁ =>
    . right
      obtain ⟨_, w₂⟩ := w₁
      exact w₂
  | inr w₁ =>
    . left
      exact w₁

example {A B C: Prop} (p₁: A ↔ B) (p₂: B ↔ C) : A ↔ C := by
  obtain ⟨w₁, w₂⟩ := p₁
  obtain ⟨w₃, w₄⟩ := p₂
  constructor
  . intro h₁
    have w₅: B := modus_ponens ⟨w₁, h₁⟩
    have w₆: C := modus_ponens ⟨w₃, w₅⟩
    exact w₆
  . intro h₁
    have w₅: B := modus_ponens ⟨w₄, h₁⟩
    have w₆: A := modus_ponens ⟨w₂, w₅⟩
    exact w₆

example {F G H: Prop} (p₁: ¬F → G) (p₂: F → H) : G ∨ H := by
  by_cases h₁: F
  . right
    have w₁: H := modus_ponens ⟨p₂, h₁⟩
    exact w₁
  . left
    have w₁: G := modus_ponens ⟨p₁, h₁⟩
    exact w₁

example {Z K M D: Prop} (p₁: (Z ∧ K) ∨ (K ∧ M)) (p₂: K → D) : D := by
  cases p₁ with
  | inl h₁ =>
    . obtain ⟨_, w₂⟩ := h₁
      have w₃: D := modus_ponens ⟨p₂, w₂⟩
      exact w₃
  | inr h₁ =>
    . obtain ⟨w₁, _⟩ := h₁
      have w₃: D := modus_ponens ⟨p₂, w₁⟩
      exact w₃

example {P Q R E: Prop} (p₁: P ∧ (Q ∨ R)) (p₂: P → ¬R) : Q ∨ E := by
  obtain ⟨w₁, w₂⟩ := p₁
  have w₃: ¬R := modus_ponens ⟨p₂, w₁⟩
  cases w₂ with
  | inl h₁ =>
    . left
      exact h₁
  | inr h₁ => contradiction

example {S T: Prop} (p₁: S ↔ T) : S ↔ (T ∨ S) := by
  obtain ⟨w₁, w₂⟩ :=  p₁
  constructor
  . intro h₁
    have w₃: T := modus_ponens ⟨w₁, h₁⟩
    left
    exact w₃
  . intro h₁
    cases h₁ with
    | inl h₂ =>
      . have w₃: S := modus_ponens ⟨w₂, h₂⟩
        exact w₃
    | inr h₂ => exact h₂

example {P Q: Prop} (p₁: ¬(P → Q)) : ¬Q := by
  intro h₁
  apply p₁
  intro _
  exact h₁

example {P Q: Prop} (p₁: ¬(P → Q)) : P := by
  by_contra h₁
  apply p₁
  intro h₁
  contradiction
