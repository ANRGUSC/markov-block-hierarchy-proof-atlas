import FiniteChannel

open scoped BigOperators
namespace BlockHierarchy.Four

theorem active_mass_derivative : ∀ {ι : Type} [Fintype ι] (g w v : ι → ℝ) (η : ℝ), (∑ i, v i)=0 →
  (∀ i, w i=0 → v i=0) → (∀ i, w i≠0 → g i=η) → (∑ i, g i*v i)=0 := by
  intro ι _ g w v η mass vanish active
  have point (i : ι) : g i*v i=η*v i := by
    by_cases e : w i=0
    · simp [vanish i e]
    · rw [active i e]
  simp_rw [point,← Finset.mul_sum,mass,mul_zero]

theorem parity_endpoint_rule : ∀ (f : ℝ → ℝ) (θ g : ℝ), θ ∈ Set.Icc (0:ℝ) 1 →
  (∀ x ∈ Set.Icc (0:ℝ) 1, f x ≤ f θ+g*(x-θ)) →
  ((θ=0 ∧ g ≤ 0) ∨ (θ=1 ∧ 0 ≤ g) ∨ g=0) →
  ∀ x ∈ Set.Icc (0:ℝ) 1, f x ≤ f θ := by
  intro f θ g hθ tangent conditions x hx
  have step := tangent x hx
  rcases conditions with ⟨rfl,hg⟩ | ⟨rfl,hg⟩ | rfl
  · linarith only [step,mul_nonpos_of_nonpos_of_nonneg hg hx.1]
  · linarith only [step,mul_nonpos_of_nonneg_of_nonpos hg (sub_nonpos.mpr hx.2)]
  · simpa using step

end BlockHierarchy.Four
