import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace BlockHierarchy.Channel

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Mutual information in nats, expressed in terms of the joint mass and marginals. -/
noncomputable def info (P : X → ℝ) (q : Y → ℝ) (J : X → Y → ℝ) : ℝ :=
  ∑ x, ∑ y, J x y * (Real.log (J x y) - Real.log (P x) - Real.log (q y))

def cost (d J : X → Y → ℝ) : ℝ := ∑ x, ∑ y, J x y * d x y

private theorem gibbs_term {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (support : y = 0 → x = 0) :
    x-y ≤ x*(Real.log x - Real.log y) := by
  rcases eq_or_lt_of_le hx with h | hp
  · rw [← h]
    simp [hy]
  have hq : 0 < y := lt_of_le_of_ne hy (fun h => hp.ne' (support h.symm))
  have ht := Real.log_le_sub_one_of_pos (div_pos hq hp)
  rw [Real.log_div hq.ne' hp.ne'] at ht
  have h := mul_le_mul_of_nonneg_right ht hp.le
  have hc := div_mul_cancel₀ y hp.ne'
  nlinarith only [h,hc]

/-- Gibbs' inequality for conditional distributions, including zero output mass. -/
theorem backward_entropy_bound (J K : X → Y → ℝ) (q : Y → ℝ)
    (hJ : ∀ x y, 0 ≤ J x y) (hK : ∀ x y, 0 < K x y)
    (col : ∀ y, ∑ x, J x y = q y) (norm : ∀ y, ∑ x, K x y = 1) :
    0 ≤ ∑ x, ∑ y, J x y * (Real.log (J x y)-Real.log (q y)-Real.log (K x y)) := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_nonneg
  intro y _
  have hq : 0 ≤ q y := by rw [← col y]; exact Finset.sum_nonneg (fun x _ => hJ x y)
  have point (x : X) : J x y - q y*K x y ≤
      J x y*(Real.log (J x y)-Real.log (q y)-Real.log (K x y)) := by
    by_cases hz : q y = 0
    · have leq : J x y ≤ ∑ i, J i y := Finset.single_le_sum (fun i _ => hJ i y) (Finset.mem_univ x)
      rw [col,hz] at leq
      simp [le_antisymm leq (hJ x y), hz]
    · have hpos := mul_pos (lt_of_le_of_ne hq (Ne.symm hz)) (hK x y)
      have h := gibbs_term (hJ x y) hpos.le (fun h => (hpos.ne' h).elim)
      rwa [Real.log_mul hz (hK x y).ne', ← sub_sub] at h
  have total := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => point x)
  simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum, col, norm, mul_one, sub_self] using total

/-- On any discrete alphabet a normalized backward Gibbs kernel gives the
Shannon lower bound for every competitor joint law with source marginal P. -/
theorem rate_lower_bound (P : X → ℝ) (q : Y → ℝ) (J K d : X → Y → ℝ)
    (s z : ℝ) (hJ : ∀ x y, 0 ≤ J x y) (hK : ∀ x y, 0 < K x y)
    (row : ∀ x, ∑ y, J x y = P x) (col : ∀ y, ∑ x, J x y = q y)
    (norm : ∀ y, ∑ x, K x y = 1) (mass : ∑ x, P x = 1)
    (kernel : ∀ x y, Real.log (K x y) = s*d x y-z) :
    -(∑ x, P x * Real.log (P x)) + s*cost d J-z ≤ info P q J := by
  have h := backward_entropy_bound J K q hJ hK col norm
  have id (x : X) (y : Y) :
      J x y*(Real.log (J x y)-Real.log (q y)-Real.log (K x y)) =
      J x y*(Real.log (J x y)-Real.log (P x)-Real.log (q y)) +
      J x y*Real.log (P x) - s*(J x y*d x y) + z*J x y := by rw [kernel]; ring
  simp_rw [id] at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, row, mass, mul_one] at h
  unfold info cost
  linarith only [h]

end BlockHierarchy.Channel
