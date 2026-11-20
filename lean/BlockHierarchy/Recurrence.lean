import BlockHierarchy.Three.Thresholds
import BlockHierarchy.Three.Distortion

open scoped BigOperators
namespace BlockHierarchy.Recurrence

theorem recurrence_strict : ∀ ρ z x y : ℝ, 0 < ρ → 0 < z → z < 1 → 0 ≤ x → x < y → y < z → ρ*((1-z*x)/(z-x)) < ρ*((1-z*y)/(z-y)) := by
  intro ρ z x y hr hz hz1 hx hxy hy
  apply mul_lt_mul_of_pos_left _ hr
  apply (div_lt_div_iff₀ (sub_pos.mpr (hxy.trans hy)) (sub_pos.mpr hy)).mpr
  have zz := mul_pos (sub_pos.mpr hz1) (show 0 < 1+z by linarith)
  nlinarith only [mul_pos (sub_pos.mpr hxy) zz]

theorem fixed_point_equation : ∀ ρ z h : ℝ, h < z → (h=ρ*((1-z*h)/(z-h)) ↔ h^2-z*(1+ρ)*h+ρ=0) := by
  intro ρ z h hz
  rw [← mul_div_assoc,eq_div_iff (sub_pos.mpr hz).ne']
  constructor <;> intro e <;> linarith only [e]

theorem critical_distortion_identity : ∀ p : ℝ, 0 < p → p < 1/2 → let ρ := 1-2*p; (1-2*Real.sqrt ρ/(1+ρ))/2 = (1-Real.sqrt (1-(p/(1-p))^2))/2 := by
  intro p hp hhalf
  dsimp only
  have hρ : 0 < 1-2*p := by linarith
  have hm : 0 < 1-p := by linarith
  have sq := Real.sq_sqrt hρ.le
  have rad : 1-(p/(1-p))^2=(Real.sqrt (1-2*p)/(1-p))^2 := by
    rw [div_pow,div_pow,sq]
    field_simp [hm.ne'] <;> ring
  rw [rad,Real.sqrt_sq (div_nonneg (Real.sqrt_nonneg _) hm.le)]
  have den : 1+(1-2*p)=2*(1-p) := by ring
  rw [den]
  field_simp [hm.ne'] <;> ring

end BlockHierarchy.Recurrence
