import PositiveThreshold

namespace BlockHierarchy.NegativeSupport

/-- Numerator of the inverse-prior mass of the constant word with input mass A. -/
def N (A B C u : ℝ) : ℝ := A - 2*C*u + B*u^2

/-- On the full-support interval, the constant words retain their input ordering. -/
theorem constant_gap (A B C u : ℝ) :
    N B A C u - N A B C u = (B-A)*(1-u^2) := by unfold N; ring

/-- At a zero of one constant, the other vanishes exactly in the equal-bias case. -/
theorem constant_tie {A B C u : ℝ} (hu : 0 ≤ u) (hlt : u < 1)
    (hz : N A B C u = 0) : N B A C u = 0 ↔ B = A := by
  have hpos : 0 < 1-u^2 := by nlinarith only [mul_pos (sub_pos.mpr hlt) (show 0 < 1+u by linarith)]
  have h := constant_gap A B C u
  rw [hz, sub_zero] at h
  rw [h, mul_eq_zero]
  simp [ne_of_gt hpos, sub_eq_zero]

/-- The printed smaller quadratic root annihilates the rarer constant numerator. -/
theorem smaller_root {A B C : ℝ} (hB : 0 < B) (hd : 0 < C^2-A*B) :
    N A B C ((C-Real.sqrt (C^2-A*B))/B) = 0 := by
  unfold N
  field_simp [hB.ne']
  nlinarith only [Real.sq_sqrt hd.le]

/-- The first zero is approached through strictly positive values. -/
theorem positive_before_root {A B C r u : ℝ} (hB : 0 < B)
    (hz : N A B C r = 0) (hslope : 0 < C-B*r) (hu : u < r) :
    0 < N A B C u := by
  have hf : N A B C u = N A B C r + (r-u)*(2*(C-B*r)+B*(r-u)) := by unfold N; ring
  rw [hf, hz, zero_add]
  exact mul_pos (sub_pos.mpr hu) (add_pos (by linarith) (mul_pos hB (sub_pos.mpr hu)))

/-- Both transition words stay positive while the smaller root is approached. -/
theorem transition_positive {A B C u : ℝ} (hC : 0 < C) (hAB : A ≤ B)
    (hd : 0 < C^2-A*B) (hu : 0 ≤ u) (hslope : 0 < C-B*u) :
    0 < C*(1+u^2)-(A+B)*u := by
  have hA : 0 < C-A*u := by linarith [mul_le_mul_of_nonneg_right hAB hu]
  have hf : C*(C*(1+u^2)-(A+B)*u) =
      (C-A*u)*(C-B*u)+(C^2-A*B)*u^2 := by ring
  have hp := add_pos_of_pos_of_nonneg (mul_pos hA hslope) (mul_nonneg hd.le (sq_nonneg u))
  rw [← hf] at hp
  exact pos_of_mul_pos_right hp hC.le

end BlockHierarchy.NegativeSupport
