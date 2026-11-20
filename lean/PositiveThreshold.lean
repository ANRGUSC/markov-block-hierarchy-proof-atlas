import PairPrior
import FirstSupport

namespace BlockHierarchy

theorem positive_first_change : PositiveThresholdContract := by
  intro p q ρ hp hq hpq hρ hρlt
  let C := (1 - ρ) * p * q
  let A := p - C
  let B := q - C
  let r := (1 - Real.sqrt (1 - 4 * C)) / 2
  change 0 < r ∧ r < 1 / 2 ∧ ∀ D : ℝ, 0 ≤ D → D < 1 / 2 → _
  have hC : 0 < C := mul_pos (mul_pos (sub_pos.mpr hρlt) hp) hq
  have hCpq : C < p * q := by
    dsimp [C]
    nlinarith only [mul_pos (mul_pos hρ hp) hq]
  have hdisc : 0 < 1 - 4 * C := by
    have hsum : (p + q)^2 = 1 := by rw [hpq]; norm_num
    nlinarith only [hsum, sq_nonneg (p - q), hCpq]
  have hs := Real.sq_sqrt hdisc.le
  have hspos := Real.sqrt_pos.mpr hdisc
  have hslt : Real.sqrt (1 - 4 * C) < 1 := (Real.sqrt_lt' (by norm_num)).mpr (by nlinarith)
  have hr : 0 < r := by dsimp [r]; linarith
  have hrhalf : r < 1 / 2 := by dsimp [r]; linarith
  have hroot : r * (1 - r) = C := by dsimp [r]; nlinarith only [hs]
  have hA : 0 < A := by
    dsimp [A]
    linarith [mul_lt_mul_of_pos_left (show q < 1 by linarith) hp, mul_one p]
  have hB : 0 < B := by
    dsimp [B]
    linarith [mul_lt_mul_of_pos_right (show p < 1 by linarith) hq, one_mul q]
  have mass : A + 2*C + B = 1 := by dsimp [A, B]; linarith
  have det : A*B - C^2 = ρ*p*q := by
    calc A*B - C^2 = p*q - C*(p+q) := by dsimp [A, B]; ring
         _ = ρ*p*q := by rw [hpq]; dsimp [C]; ring
  refine ⟨hr, hrhalf, ?_⟩
  intro D _hD hD
  let u := D / (1 - D)
  have hd : 0 < 1 - D := by linarith
  have hu : u < 1 := (div_lt_iff₀ hd).mpr (by linarith)
  have den : 0 < (1-u)^2 := sq_pos_of_pos (sub_pos.mpr hu)
  obtain ⟨posA, posB⟩ := persistent_constants A B C ρ p q u hA hB hρ hp hq det
  refine ⟨div_pos posA den, div_pos posB den, ?_⟩
  have factor : 0 < 1-r-D := by linarith
  have scale : 0 < (1-u)^2 * (1-D)^2 := mul_pos den (sq_pos_of_pos hd)
  have scaled : transitionMass A B C D * ((1-u)^2 * (1-D)^2) = (r-D)*(1-r-D) := by
    change (_ / (1-u)^2) * ((1-u)^2 * (1-D)^2) = _
    rw [← mul_assoc, div_mul_cancel₀ _ den.ne', scaled_numerator A B C D mass hd.ne']
    rw [← hroot]
    ring
  constructor
  · rw [← mul_pos_iff_of_pos_right scale, scaled, mul_pos_iff_of_pos_right factor]
    exact sub_pos
  · constructor
    · intro h
      rw [h, zero_mul] at scaled
      have hz := (mul_eq_zero.mp scaled.symm).resolve_right factor.ne'
      exact (sub_eq_zero.mp hz).symm
    · intro h
      have hz : r-D = 0 := sub_eq_zero.mpr (show D = r from h).symm
      rw [hz, zero_mul] at scaled
      exact (mul_eq_zero.mp scaled).resolve_right scale.ne'

end BlockHierarchy
