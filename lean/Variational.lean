import FiniteChannel

open scoped BigOperators

namespace BlockHierarchy.Channel

variable {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X]

/-- A column mass below one is sufficient in the finite-channel dual bound. -/
theorem subprob_entropy_bound (J K : X → Y → ℝ) (q : Y → ℝ)
    (hJ : ∀ x y, 0 ≤ J x y) (hK : ∀ x y, 0 < K x y)
    (col : ∀ y, ∑ x, J x y = q y) (test : ∀ y, ∑ x, K x y ≤ 1) :
    0 ≤ ∑ x, ∑ y, J x y*(Real.log (J x y)-Real.log (q y)-Real.log (K x y)) := by
  classical
  let c (y : Y) := ∑ x, K x y
  have hc (y : Y) : 0 < c y := Finset.sum_pos (fun x _ => hK x y) Finset.univ_nonempty
  have normalized (y : Y) : ∑ x, K x y/c y = 1 := by
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
    exact mul_inv_cancel₀ (hc y).ne'
  have h := backward_entropy_bound J (fun x y => K x y/c y) q hJ
    (fun x y => div_pos (hK x y) (hc y)) col normalized
  refine h.trans (Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => ?_)))
  apply mul_le_mul_of_nonneg_left _ (hJ x y)
  rw [Real.log_div (hK x y).ne' (hc y).ne']
  linarith only [Real.log_nonpos (hc y).le (test y)]

/-- A feasible reproduction distribution whose backward columns pass the
column test minimizes mutual information at the realized distortion. -/
theorem column_optimal (P : X → ℝ) (q t : Y → ℝ) (K J d : X → Y → ℝ)
    (s : ℝ) (f : X → ℝ) (hs : s ≤ 0) (hK : ∀ x y, 0 < K x y)
    (hJ : ∀ x y, 0 ≤ J x y) (row : ∀ x, ∑ y, q y*K x y = P x)
    (col : ∀ y, ∑ x, J x y = t y) (src : ∀ x, ∑ y, J x y = P x)
    (test : ∀ y, ∑ x, K x y ≤ 1) (kernel : ∀ x y, Real.log (K x y) = s*d x y+f x)
    (budget : cost d J ≤ cost d (fun x y => q y*K x y)) :
    info P q (fun x y => q y*K x y) ≤ info P t J := by
  let k (x : X) := f x - Real.log (P x)
  have attain : info P q (fun x y => q y*K x y) =
      s*cost d (fun x y => q y*K x y) + ∑ x, P x*k x := by
    have term (x : X) (y : Y) : q y*K x y*(Real.log (q y*K x y)-Real.log (P x)-Real.log (q y)) =
        s*(q y*K x y*d x y)+(q y*K x y)*k x := by
      by_cases hz : q y = 0
      · simp [hz]
      · rw [Real.log_mul hz (hK x y).ne',kernel]
        dsimp [k]; ring
    unfold info cost
    simp_rw [term]
    simp only [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul,row]
  have term (x : X) (y : Y) : J x y*(Real.log (J x y)-Real.log (t y)-Real.log (K x y)) =
      J x y*(Real.log (J x y)-Real.log (P x)-Real.log (t y)) - s*(J x y*d x y) - J x y*k x := by
    rw [kernel]; dsimp [k]; ring
  have h := subprob_entropy_bound J K t hJ hK col test
  simp_rw [term] at h
  simp only [Finset.sum_sub_distrib,← Finset.sum_mul,← Finset.mul_sum,src] at h
  rw [attain]
  have hb := mul_le_mul_of_nonpos_left budget hs
  unfold info cost at *
  linarith only [h,hb]

end BlockHierarchy.Channel
