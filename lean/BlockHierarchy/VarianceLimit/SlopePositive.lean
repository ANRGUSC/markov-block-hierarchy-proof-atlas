import BlockHierarchy.VarianceLimit.FixedSlope
import BlockHierarchy.VarianceLimit.Uniform

open Filter Topology
namespace BlockHierarchy.VarianceLimit

theorem positive_slope_of_commonCost {p D r : ℝ} (hp : 0<p) (ph : p<1/2) (hD : 0<D)
    (der : HasDerivAt (rateBits p) r D) (witness : ∃ t : ℝ, 0<t ∧ 0<commonCost p t-t*D) :
    0 < -(Real.log 2)*r := by
  obtain ⟨t,ht,pos⟩ := witness
  choose T hT using (fun n => (finite_duality hp ph hD n).2.1)
  have cap (n : ℕ) : canonicalCost p n (T n)≤T n := by
    rw [canonicalCost_eq]
    apply (div_le_iff₀ (by positivity : 0<(n:ℝ)+1)).2
    have uniform := totalCost_uniform hp ph (T n) (n+1)
    rw [Nat.cast_succ] at uniform
    apply uniform.trans
    rw [mul_comm (T n)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have coshpos (x : ℝ) : 1≤Real.cosh x := by
      rw [Real.cosh_eq]
      linarith only [Real.add_one_le_exp x,Real.add_one_le_exp (-x)]
    have logpos := Real.log_nonneg (coshpos (T n/2))
    linarith only [(hT n).1,logpos]
  have LB (n : ℕ) : commonCost p t-t*D ≤ T n := by
    have h := ((cost_redundancy hp ph t).2 n).1
    have best := (hT n).2 t ht.le
    have nz := mul_nonneg (hT n).1 hD.le
    linarith only [h,best,nz,cap n]
  exact pos.trans_le (ge_of_tendsto' (maximizingSlope_convergence hp ph hD der T hT) LB)

#print axioms positive_slope_of_commonCost
end BlockHierarchy.VarianceLimit