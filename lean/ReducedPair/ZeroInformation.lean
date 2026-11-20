import ChannelEquality
import ReducedPair.RateStatement

open scoped BigOperators
namespace BlockHierarchy.Channel

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem independent_info (P : X → ℝ) (t : Y → ℝ) (pos : ∀ x, 0 < P x) :
    info P t (fun x y => t y*P x) = 0 := by
  unfold info
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  by_cases h : t y = 0
  · simp [h]
  · rw [Real.log_mul h (pos x).ne']
    ring

theorem info_nonnegative (P : X → ℝ) (t : Y → ℝ) (J : X → Y → ℝ)
    (nonneg : ∀ x y, 0 ≤ J x y) (col : ∀ y, ∑ x, J x y=t y)
    (pos : ∀ x, 0 < P x) (mass : ∑ x, P x=1) : 0 ≤ info P t J := by
  have h := backward_entropy_bound J (fun x _ => P x) t nonneg (fun x _ => pos x) col (fun _ => mass)
  convert h using 1
  unfold info
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem zero_info_independent (P : X → ℝ) (t : Y → ℝ) (J : X → Y → ℝ)
    (nonneg : ∀ x y, 0 ≤ J x y) (src : ∀ x, ∑ y, J x y=P x)
    (col : ∀ y, ∑ x, J x y=t y) (pos : ∀ x, 0 < P x) (mass : ∑ x, P x=1)
    (zero : info P t J = 0) : ∀ x y, J x y=t y*P x := by
  have tot : ∑ y, t y = 1 := by simp_rw [←col]; rw [Finset.sum_comm]; simp_rw [src]; exact mass
  have prodRow (x : X) : ∑ y, t y*P x = P x := by rw [←Finset.sum_mul,tot,one_mul]
  -- A cost depending on X alone has the same expectation under every joint
  -- with input law P. This specializes the Gibbs equality case to independence.
  have sameCost : cost (fun x _ => -Real.log (P x)) J =
      cost (fun x _ => -Real.log (P x)) (fun x y => t y*P x) := by
    unfold cost
    simp only [← Finset.sum_mul,src,prodRow]
  exact optimal_joint_factors P t t (fun x _ => P x) J (fun x _ => -Real.log (P x))
    (-1) 0 (by norm_num) (fun x _ => pos x) nonneg prodRow mass (fun _ => mass)
    (fun _ _ => by ring) src col sameCost.le (by rw [zero, independent_info P t pos])

end BlockHierarchy.Channel
