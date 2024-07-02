import Mathlib.Init.Classical
import ForallX.Rules

-- A. Show that each of the following sentences is a theorem.

-- 1. O → O
example {O: Prop} : O → O := by
  intro h₁
  exact h₁

-- 2. N ∨ ¬N
example {N: Prop} : N ∨ ¬N := by
  by_cases h₁: N
  . left
    exact h₁
  . right
    exact h₁

-- 3. J ↔ (J ∨ (L ∧ ¬L))
example {J L: Prop} : J ↔ (J ∨ (L ∧ ¬L)) := by
  constructor
  . intro h₁
    left
    exact h₁
  . intro h₁
    cases h₁ with
    | inl h₂ => exact h₂
    | inr h₂ =>
      . obtain ⟨s₁, s₂⟩ := h₂
        contradiction

-- 4. ((A → B) → A) → A
example {A B: Prop} : ((A → B) → A) → A := by
  intro h₁
  by_contra h₂
  have s₁: ¬(A → B) := modus_tollens ⟨h₁, h₂⟩
  apply s₁
  intro h₃
  contradiction

-- B. Provide proofs for each of the following statements.

-- 1. C → (E ∧ G), ¬C → G ⊢ G
example {C E G: Prop} (p₁: C → (E ∧ G)) (p₂: ¬C → G) : G := by
  by_cases h₁: G
  . exact h₁
  . have s₁: ¬¬C := modus_tollens ⟨p₂, h₁⟩
    rw [double_negation] at s₁
    have s₂: E ∧ G := modus_ponens ⟨p₁, s₁⟩
    obtain ⟨_, s₃⟩ := s₂
    exact s₃

-- 2. M ∧ (¬N → ¬M) ⊢ (N ∧ M) ∨ ¬M
example {M N: Prop} (p₁: M ∧ (¬N → ¬M)) : (N ∧ M) ∨ ¬M := by
  left
  have ⟨s₁, s₂⟩ := p₁
  have s₁: ¬¬M := double_negation.mpr (s₁)
  have s₃: ¬¬N := modus_tollens ⟨s₂, s₁⟩
  rw [double_negation] at s₁
  rw [double_negation] at s₃
  constructor
  . exact s₃
  . exact s₁

-- 3. (Z ∧ K) ↔ (Y ∧ M), D ∧ (D → M) ⊢ Y → Z
example {Z K Y M D: Prop}
    (p₁: (Z ∧ K) ↔ (Y ∧ M))
    (p₂: D ∧ (D → M)) :
    Y → Z := by
  intro h₁
  obtain ⟨_, s₂⟩ := p₁
  obtain ⟨s₃, s₄⟩ := p₂
  have s₅: M := modus_ponens ⟨s₄, s₃⟩
  have s₆: Y ∧ M := by {
    constructor
    . exact h₁
    . exact s₅
  }
  have s₇: Z ∧ K := modus_ponens ⟨s₂, s₆⟩
  obtain ⟨s₈, _⟩ := s₇
  exact s₈

-- 4. (W ∨ X) ∨ (Y ∨ Z), X → Y, ¬Z ⊢ W ∨ Y
example {W X Y Z: Prop}
    (p₁: (W ∨ X) ∨ (Y ∨ Z))
    (p₂: X → Y)
    (p₃: ¬Z) :
    W ∨ Y := by
  cases p₁ with
  | inl h₁ =>
    . cases h₁ with
      | inl h₂ =>
        . left
          exact h₂
      | inr h₂ =>
        . right
          have s₁: Y := modus_ponens ⟨p₂, h₂⟩
          exact s₁
  | inr h₁ =>
    . cases h₁ with
      | inl h₂ =>
        . right
          exact h₂
      | inr h₂ => contradiction


example {R E: Prop} : (R ↔ E) ↔ (E ↔ R) := by
  constructor
  . intro h₁
    obtain ⟨s₁, s₂⟩ := h₁
    constructor
    . intro h₂
      have s₃: R := modus_ponens ⟨s₂, h₂⟩
      exact s₃
    . intro h₂
      have s₃: E := modus_ponens ⟨s₁, h₂⟩
      exact s₃
  . intro h₁
    obtain ⟨s₁, s₂⟩ := h₁
    constructor
    . intro h₂
      have s₃: E := modus_ponens ⟨s₂, h₂⟩
      exact s₃
    . intro h₂
      have s₃: R := modus_ponens ⟨s₁, h₂⟩
      exact s₃

example {G: Prop} : G ↔ ¬¬¬¬G := by
  constructor
  . intro h₁
    intro h₂
    rw [double_negation] at h₂
    contradiction
  . intro h₁
    rw [double_negation,
        double_negation] at h₁
    exact h₁

example {T S: Prop} : (T → S) ↔ (¬S → ¬T) := by
  constructor
  . intro h₁
    intro h₂
    have s₁: ¬T := modus_tollens ⟨h₁, h₂⟩
    exact s₁
  . intro h₁
    intro h₂
    have s₁: ¬¬T := double_negation.mpr (h₂)
    have s₂: ¬¬S := modus_tollens ⟨h₁, s₁⟩
    rw [double_negation] at s₂
    exact s₂

example {U I: Prop} : (U → I) ↔ ¬(U ∧ ¬I) := by
  constructor
  . intro h₁
    intro h₂
    obtain ⟨s₁, s₂⟩ := h₂
    have s₃: ¬U := modus_tollens ⟨h₁, s₂⟩
    contradiction
  . intro h₁
    intro h₂
    rw [de_morgans_and] at h₁
    cases h₁ with
    | inr h₃ =>
      . rw [double_negation] at h₃
        exact h₃
    | inl h₃ => contradiction

example {C D: Prop} : ¬(C → D) ↔ (C ∧ ¬D) := by
  constructor
  . intro h₁
    constructor
    . have h₂: C := by {
        by_contra
        apply h₁
        intro h₃
        contradiction
      }
      exact h₂
    . intro h₂
      have h₃: ¬D := by {
        intro _
        apply h₁
        intro _
        exact h₂
      }
      contradiction
  . intro h₁
    intro h₂
    obtain ⟨s₁, s₂⟩ := h₁
    have s₃: D := modus_ponens ⟨h₂, s₁⟩
    contradiction

example {G H: Prop} : (¬G ↔ H) ↔ ¬(G ↔ H) := by
  constructor
  . intro h₁
    intro h₂
    obtain ⟨s₁, s₂⟩ := h₁
    obtain ⟨s₃, s₄⟩ := h₂
    have h₃: ¬H := by {
      intro h₄
      have s₅: G := modus_ponens ⟨s₄, h₄⟩
      have s₆: ¬¬G := double_negation.mpr (s₅)
      have s₇: ¬H := modus_tollens ⟨s₂, s₆⟩
      contradiction
    }
    have s₅: ¬G := modus_tollens ⟨s₃, h₃⟩
    have s₆: H := modus_ponens ⟨s₁, s₅⟩
    contradiction
  . intro h₁
    constructor
    . intro h₂
      by_contra
      apply h₁
      constructor
      . intro h₃
        contradiction
      . intro h₃
        contradiction
    . intro h₂
      intro h₃
      apply h₁
      constructor
      . intro _
        exact h₂
      . intro _
        exact h₃
