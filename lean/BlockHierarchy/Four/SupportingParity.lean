import BlockHierarchy.Four.ParityOptimality
import BlockHierarchy.Four.Maximizer

open scoped BigOperators
namespace BlockHierarchy.Four

theorem weighted_Z_swap (u : ℝ) (a w : Class → ℝ) :
    (∑ i, a i * Z u w i) = ∑ i, w i * Z u a i := by
  simp only [class_sum,affine_Z]
  norm_num [baseline,groupMass,otherMass,evenGroup]
  <;> ring

theorem objective_tangent {p u : ℝ} (hp : 0 < p) (ph : p < 1/2) (hu : 0 < u)
    {w v : Class → ℝ} (hw : w ∈ stdSimplex ℝ Class) (hv : v ∈ stdSimplex ℝ Class) :
    objective p u v-objective p u w ≤
      ∑ i, Z u (ratio p u w) i*(v i-w i) := by
  have zp (a : Class → ℝ) (ha : a ∈ stdSimplex ℝ Class) (i : Class) : 0 < Z u a i := by
    simpa only [orbit_rep] using Z_pos hu a ha.1 ha.2 (representative i)
  have point (i : Class) : sourceClasses p i*Real.log (Z u v i)-sourceClasses p i*Real.log (Z u w i)
      ≤ ratio p u w i*(Z u v i-Z u w i) := by
    have h := Real.log_le_sub_one_of_pos (div_pos (zp v hv i) (zp w hw i))
    rw [Real.log_div (zp v hv i).ne' (zp w hw i).ne'] at h
    calc
      _ ≤ sourceClasses p i*(Z u v i/Z u w i-1) := by
        simpa only [mul_sub] using mul_le_mul_of_nonneg_left h (source_classes_pos hp ph i).le
      _ = _ := by unfold ratio; field_simp [(zp w hw i).ne'] <;> ring
  unfold objective
  rw [← Finset.sum_sub_distrib]
  apply (Finset.sum_le_sum (fun i _ => point i)).trans_eq
  simp_rw [mul_sub,Finset.sum_sub_distrib]
  rw [weighted_Z_swap u (ratio p u w) v,weighted_Z_swap u (ratio p u w) w]
  simp only [mul_comm]

theorem parity_support {p u : ℝ} (hp : 0 < p) (ph : p < 1/2) (hu : 0 < u)
    {w v : Class → ℝ} (hw : w ∈ stdSimplex ℝ Class) (hv : v ∈ stdSimplex ℝ Class)
    (ηE ηO : ℝ)
    (gains : ∀ i, let g := coefficient u i*ratio p u w i; let η := if evenGroup i then ηE else ηO
                   g ≤ η ∧ (w i≠0 → g=η)) :
    objective p u v ≤ objective p u w +
      paritySlope u (ratio p u w) ηE ηO*(evenMass v-evenMass w) := by
  let a := ratio p u w
  let E := u^2*evenMass a+((u+u^3)/2)*oddMass a+ηE
  let O := u^2*oddMass a+((u+u^3)/2)*evenMass a+ηO
  let cap (i : Class) := if evenGroup i then E else O
  have col (i : Class) : Z u a i ≤ cap i ∧ (w i ≠ 0 → Z u a i=cap i) := by
    obtain ⟨b,e⟩ := gains i
    rw [affine_Z]
    by_cases g : evenGroup i <;>
      simp only [g,if_true,if_false] at b e <;>
      simp only [cap,baseline,groupMass,otherMass,g,if_true,if_false,E,O,evenMass,oddMass] <;>
      exact ⟨add_le_add_right b _,fun h => by rw [e h]⟩
  have bound (i : Class) : Z u a i*(v i-w i) ≤ cap i*(v i-w i) := by
    by_cases e : w i=0
    · simpa only [e,sub_zero] using mul_le_mul_of_nonneg_right (col i).1 (hv.1 i)
    · rw [(col i).2 e]
  have groups (x : Class → ℝ) : (∑ i, cap i*x i)=E*evenMass x+O*oddMass x := by
    rw [class_sum]
    norm_num [cap,evenGroup,evenMass,oddMass] <;> ring
  have diff : E-O=paritySlope u a ηE ηO := by unfold E O paritySlope; ring
  have wm := (mass_partition w).symm.trans hw.2
  have vm := (mass_partition v).symm.trans hv.2
  have h := (objective_tangent hp ph hu hw hv).trans (Finset.sum_le_sum (fun i _ => bound i))
  simp_rw [mul_sub,Finset.sum_sub_distrib,groups] at h
  change objective p u v ≤ objective p u w + paritySlope u a ηE ηO*(evenMass v-evenMass w)
  rw [← diff]
  rw [show oddMass v=1-evenMass v by linarith only [vm],
      show oddMass w=1-evenMass w by linarith only [wm]] at h
  linarith only [h]

end BlockHierarchy.Four
