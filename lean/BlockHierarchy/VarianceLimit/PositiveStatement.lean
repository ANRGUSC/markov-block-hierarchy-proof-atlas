import BlockHierarchy.VarianceLimit.Statement

open Filter Topology
namespace BlockHierarchy.VarianceLimit
open Cut

noncomputable def endpointLower (τ : ℝ) := 2 * Real.log (Real.cosh (τ/2)) / τ

/-- Corollary 9. At every strictly positive multiplier, the lower bound is
for the actual limiting normalized score deviation of the stationary chain. -/
def QuantitativePositivityStatement : Prop :=
  ∀ p τ : ℝ, 0<p → p<1/2 → 0<τ →
    ∃ W : ℝ, 0<W ∧
      ((1-2*p)*Real.sqrt (p*(1-p))/2)*(endpointLower τ)^4 ≤ W ∧
      ∀ q : (n : ℕ) → Word n → ℝ,
        (∀ n, Optimal (mass p n) τ (distance n) (q n)) →
        Tendsto (fun n => omegaAt p τ n (q n)) atTop (𝓝 W)

end BlockHierarchy.VarianceLimit
