import FiniteChannel

open scoped BigOperators
namespace BlockHierarchy.Four

theorem class_totals : (∀ p : ℝ, (1-p)^3+p*(1-p)^2+p^2*(1-p)+p^3+2*p*(1-p)^2+2*p^2*(1-p)=1) ∧ (∀ p : ℝ, 2*p*(1-p)^2+2*p^2*(1-p)=2*p*(1-p) ∧ p*(1-p)^2+p^2*(1-p)+p^3=1-(1-p)^3-2*p*(1-p)) := by
  constructor
  · intro p; ring
  · intro p; constructor <;> ring

theorem even_threshold_test : (∀ p u : ℝ, 0 < p → p < 1/2 → 0 < u → (p*(1-p)^2/u^2 ≤ (1-p)^3/((1+u^4)/2) ↔ p/(1-p) ≤ 2*u^2/(1+u^4))) ∧ (∀ u v : ℝ, 0 ≤ u → u < v → v < 1 → 2*u^2/(1+u^4) < 2*v^2/(1+v^4)) := by
  constructor
  · intro p u hp ph hu
    have q : 0 < 1-p := by linarith
    have b : 0 < 1+u^4 := by positivity
    rw [div_le_div_iff₀ (sq_pos_of_pos hu) (half_pos b),div_le_div_iff₀ q b]
    have f := sq_pos_of_pos q
    constructor
    · intro h
      apply le_of_mul_le_mul_right (a := (1-p)^2) _ f
      nlinarith only [h]
    · intro h
      nlinarith only [mul_le_mul_of_nonneg_right h f.le]
  · intro u v hu h hv
    have vp := hu.trans_lt h
    have q := mul_pos (sub_pos.mpr h) (show 0 < v+u by linarith)
    have a : u*v < 1 := by
      have x := mul_lt_mul_of_pos_right h vp
      have y := mul_lt_mul_of_pos_left hv vp
      nlinarith only [x,y,hv]
    have pos := mul_pos (sub_pos.mpr a) (show 0 < 1+u*v by positivity)
    apply (div_lt_div_iff₀ (by positivity : 0 < 1+u^4) (by positivity : 0 < 1+v^4)).mpr
    nlinarith only [mul_pos (show 0 < v^2-u^2 by linarith only [q]) (show 0 < 1-u^2*v^2 by linarith only [pos])]

theorem odd_interior_weights : (∀ s t c m : ℝ, 0 < t → 0 < s → 0 < c → 0 ≤ m → let l := (s+t)/(m+2*c); (s/l-c)+(t/l-c)=m) ∧ (∀ s t c m : ℝ, 0 < t → t ≤ s → 0 < c → 0 ≤ m → let l := (s+t)/(m+2*c); (0 < t/l-c ↔ s*c < t*(m+c)) ∧ t/l-c ≤ s/l-c) := by
  constructor
  · intro s t c m ht hs hc hm
    dsimp only
    have a : 0 < s+t := by linarith
    have b : 0 < m+2*c := by linarith
    field_simp [a.ne',b.ne'] <;> ring
  · intro s t c m ht hts hc hm
    dsimp only
    have a : 0 < s+t := by linarith
    have b : 0 < m+2*c := by linarith
    have ep := div_pos a b
    constructor
    · rw [sub_pos,lt_div_iff₀ ep,← mul_div_assoc,div_lt_iff₀ b]
      constructor <;> intro h <;> nlinarith only [h]
    · exact sub_le_sub_right (div_le_div_of_nonneg_right hts ep.le) _

end BlockHierarchy.Four
