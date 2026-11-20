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

/-- Stationary flow balance and negative persistence give the discriminant sign. -/
theorem markov_discriminant {p q a b : ℝ} (hp : 0 < p) (hq : 0 < q)
    (balance : p*a = q*b) (negative : 1 < a+b) :
    0 < (p*a)^2 - (p*(1-a))*(q*(1-b)) := by
  have product : (p*a)^2 = (p*a)*(q*b) := by rw [← balance, pow_two]
  rw [product]
  nlinarith only [mul_pos (mul_pos hp hq) (sub_pos.mpr negative)]

/-- Label the rarer constant A. The smaller root is interior and gives a
positive slope factor on the entire interval up to that root. -/
theorem root_bounds {A B C : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (order : A ≤ B) (hd : 0 < C^2-A*B) :
    let r := (C-Real.sqrt (C^2-A*B))/B
    0 < r ∧ r < 1 ∧ ∀ u ≤ r, 0 < C-B*u := by
  let s := Real.sqrt (C^2-A*B)
  have hs : 0 < s := Real.sqrt_pos.mpr hd
  have hs2 : s^2 = C^2-A*B := Real.sq_sqrt hd.le
  have hac : A < C := by
    by_contra! h
    nlinarith only [mul_le_mul_of_nonneg_right h hC.le,
      mul_le_mul_of_nonneg_left (h.trans order) hA.le, hd]
  have sumpos := add_pos hC hs
  have rationalized : (C-s)/B = A/(C+s) := by
    apply (div_eq_div_iff hB.ne' sumpos.ne').mpr
    nlinarith only [hs2]
  change 0 < (C-s)/B ∧ (C-s)/B < 1 ∧ ∀ u ≤ (C-s)/B, 0 < C-B*u
  refine ⟨rationalized.symm ▸ div_pos hA sumpos, ?_, ?_⟩
  · rw [rationalized]
    apply (div_lt_iff₀ sumpos).mpr
    linarith
  · intro u hu
    have bound := (le_div_iff₀ hB).mp hu
    linarith [mul_comm u B]

/-- Assemble the numerator signs through the first zero in the ordering A ≤ B. -/
theorem ordered_markov_first_zero {p q a b : ℝ} (hp : 0 < p) (hq : 0 < q)
    (ha : 0 < a) (ha1 : a < 1) (hb1 : b < 1) (balance : p*a = q*b)
    (negative : 1 < a+b) (order : p*(1-a) ≤ q*(1-b)) :
    let A := p*(1-a)
    let B := q*(1-b)
    let C := p*a
    let r := (C-Real.sqrt (C^2-A*B))/B
    0 < r ∧ r < 1 ∧ N A B C r = 0 ∧ (N B A C r = 0 ↔ B = A) ∧
      (∀ u, 0 ≤ u → u < r → 0 < N A B C u ∧ 0 < N B A C u) ∧
      (∀ u, 0 ≤ u → u ≤ r → 0 < C*(1+u^2)-(A+B)*u) := by
  dsimp only
  have hA := mul_pos hp (sub_pos.mpr ha1)
  have hB := mul_pos hq (sub_pos.mpr hb1)
  have hC := mul_pos hp ha
  have hd := markov_discriminant hp hq balance negative
  obtain ⟨hr, hr1, slope⟩ := root_bounds hA hB hC order hd
  have hz := smaller_root hB hd
  refine ⟨hr, hr1, hz, constant_tie hr.le hr1 hz, ?_, ?_⟩
  · intro u hu hur
    have hpos := positive_before_root hB hz (slope _ le_rfl) hur
    have hlt := lt_trans hur hr1
    have hsq : 0 < 1-u^2 := by
      nlinarith only [mul_pos (sub_pos.mpr hlt) (show 0 < 1+u by linarith)]
    have gap := constant_gap (p*(1-a)) (q*(1-b)) (p*a) u
    exact ⟨hpos, by linarith [mul_nonneg (sub_nonneg.mpr order) hsq.le]⟩
  · intro u hu hur
    exact transition_positive hC order hd hu (slope u hur)

end BlockHierarchy.NegativeSupport
