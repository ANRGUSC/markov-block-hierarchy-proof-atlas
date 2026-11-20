import BlockHierarchy.Four.WaterFilling

open scoped BigOperators
namespace BlockHierarchy.Four.WaterFilling

theorem prefix_maximum (s : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (m c : ℝ) :
    ∃ k, 1 ≤ k ∧ k ≤ n ∧ ∀ j, 1 ≤ j → j ≤ n → ratio s m c j ≤ ratio s m c k := by
  have nonempty : (Finset.Icc 1 n).Nonempty := ⟨1,Finset.mem_Icc.mpr ⟨le_rfl,hn⟩⟩
  obtain ⟨k,hk,best⟩ := Finset.exists_max_image (Finset.Icc 1 n) (ratio s m c) nonempty
  exact ⟨k,(Finset.mem_Icc.mp hk).1,(Finset.mem_Icc.mp hk).2,fun j h1 hj => best j (Finset.mem_Icc.mpr ⟨h1,hj⟩)⟩

theorem positive_ratio {s : ℕ → ℝ} {k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    {m c : ℝ} (hm : 0 ≤ m) (hc : 0 < c) (hs : ∀ i<n, 0 < s i) : 0 < ratio s m c k := by
  have kpos : (0:ℝ)<k := by exact_mod_cast hk
  apply div_pos _ (add_pos_of_nonneg_of_pos hm (mul_pos kpos hc))
  apply Finset.sum_pos
  · intro i hi
    exact hs i ((Finset.mem_range.mp hi).trans_le hkn)
  · exact ⟨0,Finset.mem_range.mpr hk⟩

theorem clipped_gain {s : ℕ → ℝ} {r c : ℝ} (hr : 0 < r) (hc : 0 < c) (i : ℕ) :
    s i/(c+clipped s r c i) ≤ r ∧
    (clipped s r c i ≠ 0 → s i/(c+clipped s r c i)=r) := by
  have den : 0 < c+clipped s r c i := add_pos_of_pos_of_nonneg hc (le_max_left ..)
  have ge : s i/r-c ≤ clipped s r c i := le_max_right .. 
  have em := div_mul_cancel₀ (s i) hr.ne'
  constructor
  · apply (div_le_iff₀ den).mpr
    nlinarith only [mul_le_mul_of_nonneg_right ge hr.le,em]
  · intro active
    have pp : 0 < s i/r-c := lt_of_not_ge (fun h => active (max_eq_left h))
    rw [clipped,max_eq_right pp.le]
    apply (div_eq_iff (by linarith : c+(s i/r-c) ≠ 0)).mpr
    linarith only [em]

theorem clipped_total {s : ℕ → ℝ} {n k : ℕ} {m c : ℝ} (hm : 0 < m) (hc : 0 < c)
    (hk : 1 ≤ k) (hkn : k ≤ n) (hs : ∀ i<n, 0 < s i)
    (sorted : ∀ i j, i ≤ j → j<n → s j ≤ s i)
    (best : ∀ j, 1 ≤ j → j ≤ n → ratio s m c j ≤ ratio s m c k) :
    (∑ i ∈ Finset.range n, clipped s (ratio s m c k) c i)=m := by
  let r := ratio s m c k
  have hr : 0 < r := positive_ratio hk hkn hm.le hc hs
  obtain ⟨left,right⟩ := maximal_prefix_bounds s n k m c hm hc hk hkn hs sorted best
  have em : r*(m+(k:ℝ)*c)=pref s k := div_mul_cancel₀ _ (by positivity)
  have pre : (∑ i ∈ Finset.range k, clipped s r c i) = m := by
    calc
      _ = ∑ i ∈ Finset.range k, (s i/r-c) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact max_eq_right (sub_nonneg.mpr ((le_div_iff₀ hr).mpr (left i (Finset.mem_range.mp hi))))
      _ = pref s k/r-(k:ℝ)*c := by
        simp [pref,Finset.sum_sub_distrib,div_eq_mul_inv,Finset.sum_mul]
      _ = m := by
        have e : pref s k/r=m+(k:ℝ)*c := (div_eq_iff hr.ne').mpr (by linarith only [em])
        linarith only [e]
  have post : (∑ j ∈ Finset.range (n-k), clipped s r c (k+j))=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have h := Finset.mem_range.mp hj
    exact max_eq_left (sub_nonpos.mpr ((div_le_iff₀ hr).mpr (right _ (by omega) (by omega))))
  change (∑ i ∈ Finset.range n, clipped s r c i)=m
  conv_lhs => rw [show n=k+(n-k) by omega,Finset.sum_range_add]
  rw [pre,post,add_zero]

end BlockHierarchy.Four.WaterFilling
