import Mathlib.Init.Classical
import ForallX.Rules

-- B. Provide a proof for each of these arguments.

-- 1.  E ∨ F, F ∨ G, ¬F ∴ E ∧ G
example {E F G: Prop} (p₁: E ∨ F) (p₂: F ∨ G) (p₃: ¬F) : E ∧ G := by
  rw [or_commutative] at p₁
  have s₁: E := disjunctive_syllogism ⟨p₁, p₃⟩
  have s₂: G := disjunctive_syllogism ⟨p₂, p₃⟩
  constructor
  . exact s₁
  . exact s₂

-- 2. M ∨ (N → M) ∴ ¬M → ¬N
example {M N: Prop} (p₁: M ∨ (N → M)) : ¬M → ¬N := by
  intro h₁
  cases p₁ with
  | inr h₂ =>
    . have s₁: ¬N := modus_tollens ⟨h₂, h₁⟩
      exact s₁
  | inl h₂ => contradiction

-- 3. (M ∨ N) ∧ (O ∨ P), N → P,  ¬P ∴ M ∧ O
example {M N O P: Prop}
    (p₁: (M ∨ N) ∧ (O ∨ P))
    (p₂: N → P)
    (p₃: ¬P) :
    M ∧ O := by
  obtain ⟨s₁, s₂⟩ := p₁
  rw [or_commutative] at s₁
  rw [or_commutative] at s₂
  have s₃: ¬N := modus_tollens ⟨p₂, p₃⟩
  have s₄: M := disjunctive_syllogism ⟨s₁, s₃⟩
  have s₅: O := disjunctive_syllogism ⟨s₂, p₃⟩
  constructor
  . exact s₄
  . exact s₅

-- 4. (X ∨ Y) ∨ (X ∨ Z), ¬(X ∨ D), D ∨ M ∴ M
example {X Y Z D: Prop}
    (_: (X ∨ Y) ∨ (X ∨ Z))
    (p₂: ¬(X ∨ D))
    (p₃: D ∨ M) :
    M := by
  rw [de_morgans_or] at p₂
  obtain ⟨_, s₁⟩ := p₂
  have s₃: M := disjunctive_syllogism ⟨p₃, s₁⟩
  exact s₃
