import FiniteChannel

open scoped BigOperators

namespace BlockHierarchy.Channel

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The backward joint attains the entropy bound, including unused outputs. -/
theorem backward_attains (P : X → ℝ) (q : Y → ℝ) (K d : X → Y → ℝ) (s z : ℝ)
    (hK : ∀ x y, 0 < K x y) (row : ∀ x, ∑ y, q y*K x y = P x)
    (mass : ∑ x, P x = 1) (kernel : ∀ x y, Real.log (K x y) = s*d x y-z) :
    info P q (fun x y => q y*K x y) =
      -(∑ x, P x*Real.log (P x)) + s*cost d (fun x y => q y*K x y)-z := by
  have term (x : X) (y : Y) :
      q y*K x y*(Real.log (q y*K x y)-Real.log (P x)-Real.log (q y)) =
      -(q y*K x y*Real.log (P x)) + s*(q y*K x y*d x y)-z*(q y*K x y) := by
    by_cases h : q y = 0
    · simp [h]
    · rw [Real.log_mul h (hK x y).ne', kernel]
      ring
  unfold info cost
  simp_rw [term]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, row, mass, mul_one]

/-- Optimality against every feasible channel with the same source and a
distortion budget equal to the backward joint's realized cost. -/
theorem backward_optimal (P : X → ℝ) (q t : Y → ℝ) (K J d : X → Y → ℝ) (s z : ℝ)
    (hs : s ≤ 0) (hK : ∀ x y, 0 < K x y) (hJ : ∀ x y, 0 ≤ J x y)
    (row : ∀ x, ∑ y, q y*K x y = P x) (mass : ∑ x, P x = 1)
    (norm : ∀ y, ∑ x, K x y = 1) (kernel : ∀ x y, Real.log (K x y) = s*d x y-z)
    (src : ∀ x, ∑ y, J x y = P x) (dst : ∀ y, ∑ x, J x y = t y)
    (budget : cost d J ≤ cost d (fun x y => q y*K x y)) :
    info P q (fun x y => q y*K x y) ≤ info P t J := by
  rw [backward_attains P q K d s z hK row mass kernel]
  have lb := rate_lower_bound P t J K d s z hJ hK src dst norm mass kernel
  linarith only [lb, mul_le_mul_of_nonpos_left budget hs]

end BlockHierarchy.Channel
