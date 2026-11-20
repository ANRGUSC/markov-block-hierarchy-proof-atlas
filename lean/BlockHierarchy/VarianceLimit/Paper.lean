import BlockHierarchy.VarianceLimit.Positive
import BlockHierarchy.VarianceLimit.SlopePositive
import BlockHierarchy.VarianceLimit.RatePositive

namespace BlockHierarchy.VarianceLimit

/-- The full common-multiplier and fixed-distortion conclusions of Theorem 8. -/
theorem variance_limit : VarianceLimitStatement := by
  intro p hp ph
  refine ⟨commonOmega p,commonOmega_continuous hp ph,commonOmega_zero p,?_,?_,?_⟩
  · intro τ ht
    exact commonOmega_pos hp ph ht
  · intro τ ht n q hq
    exact omegaAt_enclosure hp ph ht n hq
  · intro D hD Dh
    refine ⟨rate_convergence hp ph hD,?_⟩
    intro r der
    have ht := positive_slope_of_commonCost hp ph hD der (exists_positive_objective hp ph hD Dh)
    have w := commonOmega_pos hp ph ht
    refine ⟨div_pos (pow_pos w _) (pow_pos (Real.log_pos (by norm_num)) _),?_,?_⟩
    · intro n
      exact (finite_duality hp ph hD n).2.1
    · intro T q ht' hq
      exact moving_variance hp ph hD der T q ht' hq

#print axioms variance_limit
end BlockHierarchy.VarianceLimit
