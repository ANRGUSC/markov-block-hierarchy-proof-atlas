import BlockHierarchy.VarianceLimit.EndpointProfile
import BlockHierarchy.VarianceLimit.GainUpper
import BlockHierarchy.VarianceLimit.GainLimit
import BlockHierarchy.VarianceLimit.Uniform
import BlockHierarchy.VarianceLimit.Common
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

open Filter Topology
open scoped BigOperators
namespace BlockHierarchy.VarianceLimit
open Cut

theorem endpointLower_pos {τ : ℝ} (h : 0<τ) : 0<endpointLower τ := by
  unfold endpointLower
  exact div_pos (mul_pos (by norm_num) (Real.log_pos (Real.one_lt_cosh.mpr (by linarith)))) h

theorem commonOmega_lower {p τ : ℝ} (hp : 0<p) (ph : p<1/2) (ht : 0<τ) :
    ((1-2*p)*Real.sqrt (p*(1-p))/2)*(endpointLower τ)^4 ≤ commonOmega p τ := by
  obtain ⟨b,del,lo⟩ := exists_endpoint_profile (τ:=τ) hp (show p<1 by linarith)
  let b' := fun n => b (n-1)
  let F := totalCost p τ
  let g := fun i j => F i+F j-F (i+j)
  let ω := fun n : ℕ => blockSD p τ n/Real.sqrt n
  have avg (N : ℕ) (_ : 0<N) : (N:ℝ)*endpointLower τ ≤ ∑ i ∈ Finset.range N, b' (i+1) := by
    apply mean_endpoint_lower hp ph ht
    simpa [b'] using del
  have lower (i j : ℕ) : ((1-2*p)^2/2)*b' (i+1)^2*b' (j+1)^2 ≤ g (i+1) (j+1) := by
    simpa [b',g,F,mul_pow,div_eq_mul_inv,mul_comm,mul_assoc,mul_left_comm] using lo i j
  have upper (k : ℕ) : (∑ i ∈ Finset.range (k+1), g (i+1) (k-i+1)) ≤
      ((1/2-p)/Real.sqrt (p*(1-p)))*Real.sqrt (((k:ℝ)+2)*((k:ℝ)+1))*ω (k+2) := by
    have e (i : ℕ) (hi : i ∈ Finset.range (k+1)) : (i+1)+(k-i+1)=k+2 := by
      have := Finset.mem_range.mp hi
      omega
    have re : (∑ i ∈ Finset.range (k+1), g (i+1) (k-i+1)) =
       ∑ i ∈ Finset.range (k+1), (F (i+1)+F (k-i+1)-F (k+2)) := by
      apply Finset.sum_congr rfl
      intro i hi
      unfold g
      rw [e i hi]
    rw [re]
    simpa [F,ω] using gain_upper (τ:=τ) hp ph k
  have pos (k : ℕ) : 0 ≤ ω (k+2) := by
    unfold ω
    exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  exact gain_positivity hp ph (endpointLower_pos ht).le avg lower upper pos
    (blockSD_tendsto_commonOmega hp ph ht.le)

theorem commonOmega_pos {p τ : ℝ} (hp : 0<p) (ph : p<1/2) (ht : 0<τ) :
    0<commonOmega p τ := by
  apply lt_of_lt_of_le _ (commonOmega_lower hp ph ht)
  exact mul_pos (div_pos (mul_pos (by linarith) (Real.sqrt_pos.2 (mul_pos hp (by linarith)))) (by norm_num))
    (pow_pos (endpointLower_pos ht) _)

theorem quantitative_positivity : QuantitativePositivityStatement := by
  intro p τ hp ph ht
  refine ⟨commonOmega p τ,commonOmega_pos hp ph ht,commonOmega_lower hp ph ht,?_⟩
  intro q hq
  have agree (n : ℕ) : omegaAt p τ n (q n)=blockSD p τ (n+1)/Real.sqrt (n+1:ℕ) := by
    have hz := optimal_Z_eq (mass_pos hp (by linarith) n) (hq n) (canonical_optimal p τ n)
    have eq : score τ (distance n) (q n) = blockScore p τ n := by
      funext x
      unfold blockScore score
      rw [hz]
    simp [omegaAt,eq,blockSD]
  simp_rw [agree]
  exact (blockSD_tendsto_commonOmega hp ph ht.le).comp (tendsto_add_atTop_nat 1)

#print axioms quantitative_positivity
end BlockHierarchy.VarianceLimit
