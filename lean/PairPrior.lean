import Mathlib.Analysis.Real.Sqrt

namespace BlockHierarchy

/-- The inverse-prior formula for either constant word; swap A and B for 11. -/
noncomputable def constantMass (A B C D : ℝ) : ℝ :=
  let u := D / (1 - D)
  (A - 2 * C * u + B * u ^ 2) / (1 - u) ^ 2

/-- Stationarity gives the same inverse-prior mass for 01 and 10. -/
noncomputable def transitionMass (A B C D : ℝ) : ℝ :=
  let u := D / (1 - D)
  (C * (1 + u ^ 2) - (A + B) * u) / (1 - u) ^ 2

/-- The positive-persistence branch, starting from the stationary two-symbol model.
The conclusions describe the four explicit inverse-prior masses on the admissible interval. -/
def PositiveThresholdContract : Prop :=
  ∀ π₀ π₁ ρ : ℝ, 0 < π₀ → 0 < π₁ → π₀ + π₁ = 1 → 0 < ρ → ρ < 1 →
    let C := (1 - ρ) * π₀ * π₁
    let A := π₀ - C
    let B := π₁ - C
    let r := (1 - Real.sqrt (1 - 4 * C)) / 2
    0 < r ∧ r < 1 / 2 ∧ ∀ D : ℝ, 0 ≤ D → D < 1 / 2 →
      0 < constantMass A B C D ∧ 0 < constantMass B A C D ∧
      (0 < transitionMass A B C D ↔ D < r) ∧ (transitionMass A B C D = 0 ↔ D = r)

end BlockHierarchy
