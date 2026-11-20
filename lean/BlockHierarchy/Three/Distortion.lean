import BlockHierarchy.Three.Classes

namespace BlockHierarchy.Three

noncomputable def middleCost (p u : ℝ) :=
  p^2 + u/(1+u) + (1-p^2)*(u*(1+2*u)/(1+u+u^2))

noncomputable def constantCost (p u : ℝ) :=
  (1-p)^2*(3*u^3/(1+u^3)) + (1-(1-p)^2)*(1+u/(1+u))

private theorem odds_lt {u v : ℝ} (hu : 0 ≤ u) (h : u < v) :
    u/(1+u) < v/(1+v) := by
  apply (div_lt_div_iff₀ (by linarith : 0 < 1+u) (by linarith : 0 < 1+v)).mpr
  linarith

private theorem middleFactor_lt {u v : ℝ} (hu : 0 ≤ u) (h : u < v) :
    u*(1+2*u)/(1+u+u^2) < v*(1+2*v)/(1+v+v^2) := by
  have hv := hu.trans h.le
  apply (div_lt_div_iff₀ (by positivity : 0 < 1+u+u^2) (by positivity : 0 < 1+v+v^2)).mpr
  have hf : 0 < 1+2*u+2*v+u*v := by positivity
  nlinarith only [mul_pos (sub_pos.mpr h) hf]

theorem middleCost_strict {p u v : ℝ} (hp : 0 < p) (half : p < 1/2)
    (hu : 0 ≤ u) (h : u < v) : middleCost p u < middleCost p v := by
  have m : 0 < 1-p^2 := by nlinarith only [mul_pos hp (show 0 < 1-p by linarith), half]
  exact add_lt_add (add_lt_add_right (odds_lt hu h) _) (mul_lt_mul_of_pos_left (middleFactor_lt hu h) m)

theorem constantCost_strict {p u v : ℝ} (hp : 0 < p) (half : p < 1/2)
    (hu : 0 ≤ u) (h : u < v) : constantCost p u < constantCost p v := by
  have hv := hu.trans_lt h
  have h3 : u^3 < v^3 := by
    have hf : 0 < v^2 + v*u + u^2 := by positivity
    nlinarith only [mul_pos (sub_pos.mpr h) hf]
  have hc := odds_lt (pow_nonneg hu 3) h3
  have hc' : 3*u^3/(1+u^3) < 3*v^3/(1+v^3) := by
    simpa only [mul_div_assoc] using mul_lt_mul_of_pos_left hc (by norm_num : (0:ℝ)<3)
  have m : 0 < 1-(1-p)^2 := by nlinarith only [mul_pos hp (show 0 < 2-p by linarith)]
  exact add_lt_add (mul_lt_mul_of_pos_left hc' (sq_pos_of_pos (by linarith)))
    (mul_lt_mul_of_pos_left (add_lt_add_right (odds_lt hu h) _) m)

theorem middle_cubic {p D u : ℝ} (hu : 0 ≤ u) : 3*D = middleCost p u ↔
    (3*D-p^2)*(1+u)*(1+u+u^2) =
      u*(1+u+u^2) + (1-p^2)*u*(1+2*u)*(1+u) := by
  unfold middleCost
  have h1 : 0 < 1+u := by positivity
  have h2 : 0 < 1+u+u^2 := by positivity
  constructor <;> intro h <;> field_simp [h1.ne',h2.ne'] at * <;> linarith only [h]

theorem constant_cubic {p D u : ℝ} (hu : 0 ≤ u) : 3*D = constantCost p u ↔
    3*D*(1+u^3) = (1-p)^2*3*u^3 + (1-(1-p)^2)*(1+2*u)*(1-u+u^2) := by
  unfold constantCost
  have h1 : 0 < 1+u := by positivity
  have h3 : 0 < 1+u^3 := by positivity
  have eq : (1+u^3)=(1-u+u^2)*(1+u) := by ring
  have aux : (1+u/(1+u))*(1+u^3) = (1+2*u)*(1-u+u^2) := by
    rw [eq]
    field_simp [h1.ne']
    ring
  rw [eq_comm, ← mul_left_inj' h3.ne']
  simp only [add_mul, mul_assoc, div_mul_cancel₀ _ h3.ne', aux]
  constructor <;> intro h <;> linarith only [h]

end BlockHierarchy.Three

