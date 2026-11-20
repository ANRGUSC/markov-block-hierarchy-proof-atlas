import FiniteChannel

open scoped BigOperators
namespace BlockHierarchy

theorem variance_enclosure : ∀ (V W b e : ℝ), 0 ≤ V → 0 ≤ W → 0 < b → 0 ≤ e →
  |Real.sqrt V - Real.sqrt (W/b)| ≤ e →
  (max 0 (Real.sqrt (W/b)-e))^2 ≤ V ∧ V ≤ (Real.sqrt (W/b)+e)^2 := by
  intro V W b e hV hW hb he err
  obtain ⟨lo,hi⟩ := abs_le.mp err
  have lower : max 0 (Real.sqrt (W/b)-e) ≤ Real.sqrt V :=
    max_le (Real.sqrt_nonneg _) (by linarith)
  have upper : Real.sqrt V ≤ Real.sqrt (W/b)+e := by linarith
  rw [← Real.sq_sqrt hV]
  exact ⟨pow_le_pow_left₀ (le_max_left _ _) lower 2, pow_le_pow_left₀ (Real.sqrt_nonneg _) upper 2⟩

end BlockHierarchy
