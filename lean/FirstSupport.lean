import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace BlockHierarchy

/-- Clear the change-of-variable denominator in the transition numerator. -/
theorem scaled_numerator (A B C D : ℝ) (mass : A + 2 * C + B = 1)
    (h : 1 - D ≠ 0) :
    (C * (1 + (D / (1 - D)) ^ 2) - (A + B) * (D / (1 - D))) *
      (1 - D) ^ 2 = C - D * (1 - D) := by
  have hab : A + B = 1 - 2 * C := by linarith
  rw [hab]
  field_simp [h]
  ring

theorem transition_zero (A B C D : ℝ) (mass : A + 2 * C + B = 1)
    (_hD : 0 ≤ D) (hD : D < 1 / 2) :
    C * (1 + (D / (1 - D)) ^ 2) - (A + B) * (D / (1 - D)) = 0 ↔
      D * (1 - D) = C := by
  have h : 1 - D ≠ 0 := by linarith
  have scaled := scaled_numerator A B C D mass h
  constructor
  · intro hz
    rw [hz, zero_mul] at scaled
    linarith
  · intro hz
    rw [hz, sub_self] at scaled
    exact (mul_eq_zero.mp scaled).resolve_right (pow_ne_zero 2 h)

/-- Completing the square after multiplying by the positive leading coefficient. -/
theorem constant_numerator_pos (A B C u : ℝ) (hB : 0 < B) (hdet : C ^ 2 < A * B) :
    0 < A - 2 * C * u + B * u ^ 2 := by
  by_contra! hn
  have hmul := mul_nonpos_of_nonneg_of_nonpos hB.le hn
  nlinarith [sq_nonneg (B * u - C)]

/-- In the persistent case both constant-word numerators stay strictly positive. -/
theorem persistent_constants (A B C ρ π₀ π₁ u : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hρ : 0 < ρ) (h₀ : 0 < π₀) (h₁ : 0 < π₁)
    (det : A * B - C ^ 2 = ρ * π₀ * π₁) :
    0 < A - 2 * C * u + B * u ^ 2 ∧ 0 < B - 2 * C * u + A * u ^ 2 := by
  have hdet : C ^ 2 < A * B := by linarith [mul_pos (mul_pos hρ h₀) h₁]
  exact ⟨constant_numerator_pos A B C u hB hdet,
         constant_numerator_pos B A C u hA (by rwa [mul_comm B A])⟩

end BlockHierarchy
