import BlockHierarchy.Four.WaterSolution

open scoped BigOperators
namespace BlockHierarchy.Four.WaterFilling

theorem empty_group {s : ℕ → ℝ} {n : ℕ} {c : ℝ}
    (hn : 0 < n) (hc : 0 < c) (hs : 0 < s 0)
    (sorted : ∀ i < n, s i ≤ s 0) :
    ratio s 0 c 1 = s 0/c ∧
    (∀ j, 1 ≤ j → j ≤ n → ratio s 0 c j ≤ ratio s 0 c 1) ∧
    (∀ i < n, clipped s (ratio s 0 c 1) c i = 0) := by
  have first : ratio s 0 c 1 = s 0/c := by simp [ratio,pref]
  refine ⟨first, ?_, ?_⟩
  · intro j hj hjn
    have jp : (0:ℝ) < j := by exact_mod_cast hj
    have bound : pref s j ≤ (j:ℝ)*s 0 := by
      calc
        _ ≤ ∑ i ∈ Finset.range j, s 0 :=
          Finset.sum_le_sum (fun i hi => sorted i ((Finset.mem_range.mp hi).trans_le hjn))
        _ = _ := by simp
    rw [first,ratio,zero_add]
    apply (div_le_div_iff₀ (mul_pos jp hc) hc).mpr
    calc
      _ ≤ ((j:ℝ)*s 0)*c := mul_le_mul_of_nonneg_right bound hc.le
      _ = _ := by ring
  · intro i hi
    rw [first,clipped]
    apply max_eq_left
    apply sub_nonpos.mpr
    apply (div_le_iff₀ (div_pos hs hc)).mpr
    simpa [mul_div_cancel₀, hc.ne', mul_div_assoc'] using
      (show s i ≤ s 0 from sorted i hi)

end BlockHierarchy.Four.WaterFilling
