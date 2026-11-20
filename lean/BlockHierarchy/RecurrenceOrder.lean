import BlockHierarchy.RecurrenceCrossing

namespace BlockHierarchy.Recurrence

def ScalarFeasible (ρ z : ℝ) (n : ℕ) : Prop :=
  (∀ j<n, orbit ρ z j<z) ∧ orbit ρ z n≤z

theorem nextMoment_pos {ρ z x : ℝ} (hr : 0<ρ) (hz : 0<z) (hz1 : z<1)
    (h : x<z) : 0<nextMoment ρ z x := by
  apply mul_pos hr
  apply div_pos _ (sub_pos.mpr h)
  have zz := mul_pos (sub_pos.mpr hz1) (show 0<1+z by linarith)
  nlinarith only [zz,mul_lt_mul_of_pos_left h hz]

theorem nextMoment_antitone_parameter {ρ z t x : ℝ} (hr : 0<ρ)
    (hx : 0≤x) (xz : x<z) (zt : z≤t) (t1 : t<1) :
    nextMoment ρ t x ≤ nextMoment ρ z x := by
  apply mul_le_mul_of_nonneg_left _ hr.le
  apply (div_le_div_iff₀ (sub_pos.mpr (xz.trans_le zt)) (sub_pos.mpr xz)).mpr
  have x1 := xz.trans_le (zt.trans t1.le)
  have xx := mul_pos (sub_pos.mpr x1) (show 0<1+x by linarith)
  nlinarith only [mul_nonneg (sub_nonneg.mpr zt) (show 0≤1-x^2 by linarith only [xx])]

theorem feasible_increases_with_z {ρ z t : ℝ} (hr : 0<ρ) (hz : 0<z) (zt : z≤t) (t1 : t<1)
    (n : ℕ) (f : ScalarFeasible ρ z n) : ScalarFeasible ρ t n := by
  have cmp (j : ℕ) (hj : j≤n) : 0≤orbit ρ t j ∧ orbit ρ t j≤orbit ρ z j := by
    induction j with
    | zero => simp [orbit]
    | succ j ih =>
      have jn : j<n := by omega
      obtain ⟨nonneg,le⟩ := ih jn.le
      have old := f.1 j jn
      have small := le.trans_lt old
      have xt := old.trans_le zt
      have increase : nextMoment ρ t (orbit ρ t j) ≤ nextMoment ρ t (orbit ρ z j) := by
        rcases eq_or_lt_of_le le with h|h
        · rw [h]
        · exact (recurrence_strict ρ t _ _ hr (hz.trans_le zt) t1 nonneg h xt).le
      exact ⟨(nextMoment_pos hr (hz.trans_le zt) t1 (small.trans_le zt)).le,
        increase.trans (nextMoment_antitone_parameter hr (nonneg.trans le) old zt t1)⟩
  exact ⟨fun j hj => ((cmp j hj.le).2.trans_lt (f.1 j hj)).trans_le zt,
    (cmp n le_rfl).2.trans (f.2.trans zt)⟩

end BlockHierarchy.Recurrence
