import BlockHierarchy.Four.Maximizer
import BlockHierarchy.Four.Derivatives
import BlockHierarchy.Four.ParityOptimality

open scoped BigOperators
namespace BlockHierarchy.Four

noncomputable def baselineD (u : ℝ) (w : Class → ℝ) (i : Class) :=
  2*u*groupMass w i + ((1+3*u^2)/2)*otherMass w i

noncomputable def coefficientD (u : ℝ) (i : Class) := (2*u^3-2*u)/(cardinal i/2)

theorem cost_numerator_formula (u : ℝ) (w : Class → ℝ) (i : Class) :
    costNumerator u w i = u*(baselineD u w i+coefficientD u i*w i) := by
  unfold costNumerator classKernel baselineD coefficientD
  norm_num
  ring

theorem baseline_derivative (u : ℝ) (w : Class → ℝ) (i : Class) :
    HasDerivAt (fun t => baseline t w i) (baselineD u w i) u := by
  have a := ((hasDerivAt_id u).pow 2).mul_const (groupMass w i)
  have b := (((hasDerivAt_id u).add ((hasDerivAt_id u).pow 3)).div_const 2).mul_const (otherMass w i)
  have h := a.add b
  change HasDerivAt (fun t => baseline t w i) _ u at h
  convert h using 1
  unfold baselineD
  norm_num <;> ring

theorem coefficient_derivative (u : ℝ) (i : Class) :
    HasDerivAt (fun t => coefficient t i) (coefficientD u i) u := by
  have a := (((hasDerivAt_id u).pow 4).const_add 1).div_const 2
  have b := (a.sub ((hasDerivAt_id u).pow 2)).div_const (cardinal i/2)
  change HasDerivAt (fun t => coefficient t i) _ u at b
  convert b using 1
  unfold coefficientD
  norm_num <;> ring

theorem objective_derivative (p : ℝ) {u : ℝ} (hu : 0 < u) (w : Class → ℝ)
    (hw : ∀ i, 0 ≤ w i) (unit : ∑ i,w i=1) :
    HasDerivAt (fun t => objective p t w)
      (∑ i, sourceClasses p i*((baselineD u w i+coefficientD u i*w i)/Z u w i)) u := by
  have pos (i) : 0 < Z u w i := by
    simpa only [orbit_rep] using Z_pos hu w hw unit (representative i)
  simpa only [objective,affine_Z] using affine_class_derivative (sourceClasses p) w
    (fun i t => baseline t w i) (fun i t => coefficient t i) (baselineD u w)
    (coefficientD u) u (baseline_derivative u w) (coefficient_derivative u)
    (fun i => (affine_Z u w i) ▸ pos i)

theorem distortion_eq (p u : ℝ) (w : Class → ℝ) :
    Channel.cost (fun x y => (distance x y:ℝ))
      (FiniteRD.joint (source p) (fun x => Z u w (orbit x)) (prior w) distance u) =
      u*∑ i, sourceClasses p i*((baselineD u w i+coefficientD u i*w i)/Z u w i) := by
  rw [normalized_cost,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [cost_numerator_formula]
  ring

end BlockHierarchy.Four
