import ForallX.Common

example {E F G: Prop}
    (h₁: E ∨ F)
    (h₂: F ∨ G)
    (h₃: ¬F) :
    E ∧ G := by
  constructor
  . rw [or_commutativity] at h₁
    have h₄ : E := MTP ⟨h₁, h₃⟩
    exact h₄
  . have h₄ : G := MTP ⟨h₂, h₃⟩
    exact h₄

example {M N: Prop} (h₁: M ∨ (N → M)) : ¬M → ¬N := by
  intro h₂
  have h₃ : N → M := MTP ⟨h₁, h₂⟩
  have h₄ : ¬N := MT ⟨h₃, h₂⟩
  exact h₄

example {M N O P: Prop}
    (h₁: (M ∨ N) ∧ (O  ∨ P))
    (h₂: N → P)
    (h₃: ¬P) :
    M ∧ O := by
  obtain ⟨h₄, h₅⟩ := h₁
  rw [or_commutativity] at h₄
  rw [or_commutativity] at h₅
  have h₆ : ¬N := MT ⟨h₂, h₃⟩
  have h₇ : M := MTP ⟨h₄, h₆⟩
  have h₈ : O := MTP ⟨h₅, h₃⟩
  constructor
  . exact h₇
  . exact h₈

example {D M X Y Z: Prop}
    (h₁: (X ∧ Y) ∨ (X ∧ Z))
    (h₂: ¬(X ∧ D))
    (h₃: D ∨ M) :
    M := by
  rw [DMₐ] at h₂
  cases h₁ with
  | inl h₄ => . obtain ⟨h₅, _⟩ := h₄
                have h₇ : ¬¬X := DN.mpr (h₅)
                have h₈ : ¬D := MTP ⟨h₂, h₇⟩
                have h₉ : M := MTP ⟨h₃, h₈⟩
                exact h₉
  | inr h₄ => . obtain ⟨h₅, _⟩ := h₄
                have h₇ : ¬¬X := DN.mpr (h₅)
                have h₈ : ¬D := MTP ⟨h₂, h₇⟩
                have h₉ : M := MTP ⟨h₃, h₈⟩
                exact h₉
