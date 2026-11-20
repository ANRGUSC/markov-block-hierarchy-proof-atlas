import BlockHierarchy.Four.FourWord
import BlockHierarchy.Four.OuterGeometry

open scoped BigOperators
namespace BlockHierarchy.Four

theorem class_Z_injective {u : ℝ} (hu : 0 ≤ u) (h1 : u < 1) :
    Function.Injective (Z u) := by
  intro w v same
  have nonzero : (1-u^2)^4 ≠ 0 := pow_ne_zero _ (by
    have := mul_pos (sub_pos.mpr h1) (show 0 < 1+u by linarith)
    nlinarith)
  have recover (q : Class → ℝ) (x : Word) :
      ∑ y, (-u)^distance x y * Z u q (orbit y) = prior q x*(1-u^2)^4 := by
    simp_rw [← class_normalizer,Finset.mul_sum]
    rw [Finset.sum_comm]
    have term (y z : Word) : (-u)^distance x y*(prior q z*u^distance y z)=
        prior q z*((-u)^d4 x y*u^d4 y z) := by change _ = prior q z*((-u)^distance x y*u^distance y z); ring
    simp_rw [term,← Finset.mul_sum,hamming_inverse]
    simp [mul_ite]
  funext i
  have eq : prior w (representative i)=prior v (representative i) := by
    apply (mul_left_inj' nonzero).mp
    rw [← recover w,← recover v,same]
  simpa only [prior,orbit_rep,div_left_inj' (cardinal_pos i).ne'] using eq

private theorem log_midpoint_strict {x y : ℝ} (hx : 0<x) (hy : 0<y) (hne : x≠y) :
    (1/2:ℝ)*Real.log x+(1/2:ℝ)*Real.log y < Real.log ((1/2:ℝ)*x+(1/2:ℝ)*y) := by
  let m := (1/2:ℝ)*x+(1/2:ℝ)*y
  have hm : 0<m := by dsimp [m]; positivity
  have lt : x*y<m*m := by dsimp [m]; nlinarith only [sq_pos_of_ne_zero (sub_ne_zero.mpr hne)]
  have h := Real.log_lt_log (mul_pos hx hy) lt
  rw [Real.log_mul hx.ne' hy.ne',Real.log_mul hm.ne' hm.ne'] at h
  change _ < Real.log m
  linarith only [h]

theorem unique_maximizer {p u : ℝ} (hp : 0 < p) (ph : p < 1/2) (hu : 0 < u) (uh : u < 1)
    {w v : Class → ℝ} (hw : w ∈ stdSimplex ℝ Class) (hv : v ∈ stdSimplex ℝ Class)
    (ow : IsMaxOn (objective p u) (stdSimplex ℝ Class) w)
    (ov : IsMaxOn (objective p u) (stdSimplex ℝ Class) v) : w=v := by
  apply class_Z_injective hu.le uh
  funext j
  by_contra ne
  let a : ℝ := 1/2
  have ha : 0 < a := by norm_num [a]
  have hab : a+a=1 := by norm_num [a]
  let mid := a • w + a • v
  have hm : mid ∈ stdSimplex ℝ Class := (convex_stdSimplex ℝ Class) hw hv ha.le ha.le hab
  have pos (q : Class → ℝ) (hq : q ∈ stdSimplex ℝ Class) (i : Class) : 0 < Z u q i := by
    simpa only [orbit_rep] using Z_pos hu q hq.1 hq.2 (representative i)
  let L (i : Class) := sourceClasses p i*(a*Real.log (Z u w i)+a*Real.log (Z u v i))
  let R (i : Class) := sourceClasses p i*Real.log (Z u mid i)
  have point (i : Class) : L i ≤ R i := by
    apply mul_le_mul_of_nonneg_left _ (source_classes_pos hp ph i).le
    rw [show Z u mid i = _ from outer_Z_linear u a a w v i]
    by_cases e : Z u w i=Z u v i
    · rw [e,← add_mul,← add_mul,hab,one_mul,one_mul]
    · exact (log_midpoint_strict (pos w hw i) (pos v hv i) e).le
  have strict : L j < R j := by
    apply mul_lt_mul_of_pos_left _ (source_classes_pos hp ph j)
    rw [show Z u mid j = _ from outer_Z_linear u a a w v j]
    exact log_midpoint_strict (pos w hw j) (pos v hv j) ne
  have total := Finset.sum_lt_sum (fun i (_ : i ∈ Finset.univ) => point i) ⟨j,Finset.mem_univ _,strict⟩
  have hL : ∑ i, L i = a*objective p u w+a*objective p u v := by
    unfold L objective
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hL] at total
  change _ < objective p u mid at total
  have same : objective p u w = objective p u v := le_antisymm (ov hw) (ow hv)
  rw [← same,← add_mul,hab,one_mul] at total
  exact (not_lt_of_ge (ow hm)) total

end BlockHierarchy.Four
