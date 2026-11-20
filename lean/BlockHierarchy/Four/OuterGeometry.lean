import BlockHierarchy.Four.Maximizer
import Mathlib.Analysis.Convex.Function

open Set
open scoped BigOperators

namespace BlockHierarchy.Four

theorem outer_Z_linear (u a b : ℝ) (w v : Class → ℝ) (i : Class) :
    Z u (a • w + b • v) i = a * Z u w i + b * Z u v i := by
  by_cases e : evenGroup i <;>
    simp [Z, classKernel, groupMass, otherMass, e] <;> ring

/-- The two-point logarithmic Jensen bound follows from the tangent at the mixture. -/
private theorem outer_log_mix {x y a b : ℝ} (hx : 0 < x) (hy : 0 < y)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) (hz : 0 < a*x+b*y) :
    a * Real.log x + b * Real.log y ≤ Real.log (a*x+b*y) := by
  let z := a*x+b*y
  have tx := Real.log_le_sub_one_of_pos (div_pos hx hz)
  have ty := Real.log_le_sub_one_of_pos (div_pos hy hz)
  rw [Real.log_div hx.ne' hz.ne'] at tx
  rw [Real.log_div hy.ne' hz.ne'] at ty
  have bound : a * (x/z-1) + b * (y/z-1) = 0 := by
    calc
      _ = (a*x+b*y)/z - (a+b) := by ring
      _ = 0 := by change z/z-(a+b)=0; rw [div_self hz.ne', hab, sub_self]
  have weighted := add_le_add (mul_le_mul_of_nonneg_left tx ha) (mul_le_mul_of_nonneg_left ty hb)
  change a * (Real.log x - Real.log z) + b * (Real.log y - Real.log z) ≤
    a * (x/z-1) + b * (y/z-1) at weighted
  rw [bound] at weighted
  have identity : a*Real.log z + b*Real.log z = Real.log z := by rw [← add_mul, hab, one_mul]
  change _ ≤ Real.log z
  linarith only [weighted, identity]

/-- Each fixed-multiplier objective is concave on the entire reproduction simplex. -/
theorem outer_objective_concave {p u : ℝ} (hp : 0 < p) (ph : p < 1/2) (hu : 0 < u) :
    ConcaveOn ℝ (stdSimplex ℝ Class) (objective p u) := by
  refine ⟨convex_stdSimplex ℝ Class, ?_⟩
  intro w hw v hv a b ha hb hab
  have mix := (convex_stdSimplex ℝ Class) hw hv ha hb hab
  have pos (q : Class → ℝ) (hq : q ∈ stdSimplex ℝ Class) (i : Class) : 0 < Z u q i := by
    simpa only [orbit_rep] using Z_pos hu q hq.1 hq.2 (representative i)
  change a * objective p u w + b * objective p u v ≤ objective p u (a • w + b • v)
  unfold objective
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have z := pos _ mix i
  rw [outer_Z_linear] at z ⊢
  have h := outer_log_mix (pos w hw i) (pos v hv i) ha hb hab z
  calc
    _ = sourceClasses p i * (a * Real.log (Z u w i) + b * Real.log (Z u v i)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (source_classes_pos hp ph i).le

/-- The optimal laws for a fixed multiplier form a connected fibre, including when
multiple classes simultaneously have zero mass or when the multiplier equals one. -/
theorem outer_optimal_fibre {p u : ℝ} (hp : 0 < p) (ph : p < 1/2) (hu : 0 < u) :
    IsPreconnected {w : stdSimplex ℝ Class |
      ∀ v : stdSimplex ℝ Class, objective p u v ≤ objective p u w} := by
  apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
  apply Convex.isPreconnected
  rintro x ⟨w, hw, rfl⟩ y ⟨v, hv, rfl⟩ a b ha hb hab
  have hconc := outer_objective_concave hp ph hu
  have mix := (convex_stdSimplex ℝ Class) w.property v.property ha hb hab
  refine ⟨⟨_,mix⟩, ?_, rfl⟩
  intro q
  calc
    objective p u q = a * objective p u q + b * objective p u q := by rw [← add_mul, hab, one_mul]
    _ ≤ a * objective p u w + b * objective p u v :=
      add_le_add (mul_le_mul_of_nonneg_left (hw q) ha) (mul_le_mul_of_nonneg_left (hv q) hb)
    _ ≤ _ := hconc.2 w.property v.property ha hb hab

end BlockHierarchy.Four
