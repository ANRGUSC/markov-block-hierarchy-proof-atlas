import Mathlib.Data.Real.Basic

namespace BlockHierarchy

/-- Proposition 1, transition-word numerator only. A, C, C, B are the pair masses. -/
def TransitionZeroContract : Prop :=
  ∀ A B C D : ℝ, A + 2 * C + B = 1 → 0 ≤ D → D < 1 / 2 →
    (let u := D / (1 - D)
     (C * (1 + u ^ 2) - (A + B) * u = 0 ↔ D * (1 - D) = C))

/-- Positivity portion of the persistent branch, using the manuscript pair-mass identity. -/
def PersistentConstantsContract : Prop :=
  ∀ A B C ρ π₀ π₁ : ℝ, 0 < A → 0 < B → 0 < ρ → 0 < π₀ → 0 < π₁ →
    A * B - C ^ 2 = ρ * π₀ * π₁ → ∀ u : ℝ,
      0 < A - 2 * C * u + B * u ^ 2 ∧ 0 < B - 2 * C * u + A * u ^ 2

end BlockHierarchy
