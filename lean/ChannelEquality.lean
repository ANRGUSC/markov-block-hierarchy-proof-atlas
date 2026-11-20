import ChannelOptimizer

open scoped BigOperators

namespace BlockHierarchy.Channel

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Strictness of the scalar entropy inequality off the equality case. -/
private theorem gap_pos {v t k : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t) (hk : 0 < k)
    (support : t = 0 → v = 0) (ne : v ≠ t*k) :
    0 < v*(Real.log v-Real.log t-Real.log k) - (v-t*k) := by
  have pt : 0 < t := lt_of_le_of_ne ht (by
    intro e
    exact ne (by rw [← e,zero_mul]; exact support e.symm))
  have pk := mul_pos pt hk
  rcases eq_or_lt_of_le hv with z | pv
  · simpa [← z] using pk
  have diff : t*k/v ≠ 1 := fun h => ne (by linarith only [(div_eq_iff pv.ne').mp h])
  have bound := Real.log_lt_sub_one_of_pos (div_pos pk pv) diff
  rw [Real.log_div pk.ne' pv.ne',Real.log_mul pt.ne' hk.ne'] at bound
  have h := mul_lt_mul_of_pos_right bound pv
  nlinarith only [h, div_mul_cancel₀ (t*k) pv.ne']

/-- Every minimizer at a feasible backward-channel point has the same
conditional law of the input given each used output. -/
theorem optimal_joint_factors (P : X → ℝ) (q t : Y → ℝ) (K J d : X → Y → ℝ) (s z : ℝ)
    (hs : s ≤ 0) (hK : ∀ x y, 0 < K x y) (hJ : ∀ x y, 0 ≤ J x y)
    (row : ∀ x, ∑ y, q y*K x y = P x) (mass : ∑ x, P x = 1)
    (norm : ∀ y, ∑ x, K x y = 1) (kernel : ∀ x y, Real.log (K x y) = s*d x y-z)
    (src : ∀ x, ∑ y, J x y = P x) (dst : ∀ y, ∑ x, J x y = t y)
    (budget : cost d J ≤ cost d (fun x y => q y*K x y))
    (optimal : info P t J ≤ info P q (fun x y => q y*K x y)) :
    ∀ x y, J x y = t y*K x y := by
  classical
  let g (x : X) (y : Y) := J x y*(Real.log (J x y)-Real.log (t y)-Real.log (K x y)) -
      (J x y-t y*K x y)
  have support (x : X) (y : Y) (h : t y = 0) : J x y = 0 := by
    have leq : J x y ≤ ∑ i, J i y := Finset.single_le_sum (fun i _ => hJ i y) (Finset.mem_univ x)
    rw [dst,h] at leq
    exact le_antisymm leq (hJ x y)
  have tnon (y : Y) : 0 ≤ t y := by rw [←dst y]; exact Finset.sum_nonneg (fun i _ => hJ i y)
  have nonneg (x : X) (y : Y) : 0 ≤ g x y := by
    by_cases e : J x y = t y*K x y
    · by_cases h : t y = 0
      · simp [g,e,h]
      · simp [g,e,Real.log_mul h (hK x y).ne',add_sub_cancel_left]
    · exact (gap_pos (hJ x y) (tnon y) (hK x y) (support x y) e).le
  have id (x : X) (y : Y) : g x y =
      J x y*(Real.log (J x y)-Real.log (P x)-Real.log (t y)) + J x y*Real.log (P x) -
      s*(J x y*d x y) + z*J x y - (J x y-t y*K x y) := by
    dsimp [g]; rw [kernel]; ring
  have diff : (∑ x, ∑ y, (J x y-t y*K x y)) = 0 := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, dst, norm, mul_one, sub_self, Finset.sum_const_zero]
  have total : (∑ x, ∑ y, g x y) =
      info P t J + (∑ x, P x*Real.log (P x)) - s*cost d J + z := by
    simp_rw [id]
    unfold info cost
    -- Sum the final difference separately to use the column marginals.
    have split (x : X) : (∑ y, (J x y*(Real.log (J x y)-Real.log (P x)-Real.log (t y)) +
        J x y*Real.log (P x)-s*(J x y*d x y)+z*J x y-(J x y-t y*K x y))) =
        (∑ y, (J x y*(Real.log (J x y)-Real.log (P x)-Real.log (t y)) +
        J x y*Real.log (P x)-s*(J x y*d x y)+z*J x y)) - ∑ y, (J x y-t y*K x y) :=
      Finset.sum_sub_distrib _ _
    simp_rw [split]
    rw [Finset.sum_sub_distrib,diff]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.sum_mul,
      ← Finset.mul_sum,src,mass,mul_one,sub_zero]
  rw [backward_attains P q K d s z hK row mass kernel] at optimal
  intro x y
  by_contra ne
  have strict : 0 < g x y := gap_pos (hJ x y) (tnon y) (hK x y) (support x y) ne
  have upper : g x y ≤ ∑ i, ∑ j, g i j :=
    (Finset.single_le_sum (fun j _ => nonneg x j) (Finset.mem_univ y)).trans
    (Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => nonneg i j)) (Finset.mem_univ x))
  linarith only [strict,upper,total,optimal,mul_le_mul_of_nonpos_left budget hs]

end BlockHierarchy.Channel
