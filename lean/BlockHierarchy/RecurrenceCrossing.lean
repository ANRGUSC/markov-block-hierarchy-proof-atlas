import BlockHierarchy.Recurrence

namespace BlockHierarchy.Recurrence

noncomputable def nextMoment (ρ z x : ℝ) := ρ*((1-z*x)/(z-x))
noncomputable def orbit (ρ z : ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => nextMoment ρ z (orbit ρ z n)

/-- Below the discriminant threshold the smallest possible increment has a uniform
positive lower bound. The estimate is valid up to the first visit to the pole. -/
theorem uniform_increment {ρ z x : ℝ} (hz : 0<z) (hx : 0≤x) (before : x<z)
    (gap : 0 < 4*ρ-(z*(1+ρ))^2) :
    (4*ρ-(z*(1+ρ))^2)/(4*z) ≤ nextMoment ρ z x-x := by
  let d := (4*ρ-(z*(1+ρ))^2)/(4*z)
  have hd : 0<d := div_pos gap (by positivity)
  have deq : d*(4*z)=4*ρ-(z*(1+ρ))^2 := div_mul_cancel₀ _ (by positivity)
  have bound : d*(z-x) ≤ x^2-z*(1+ρ)*x+ρ := by
    nlinarith only [deq,sq_nonneg (2*x-z*(1+ρ)),mul_nonneg hd.le hx]
  change d ≤ ρ*((1-z*x)/(z-x))-x
  rw [le_sub_iff_add_le,←mul_div_assoc,le_div_iff₀ (sub_pos.mpr before)]
  linarith only [bound]

theorem finite_crossing {ρ z : ℝ} (hz : 0<z) (gap : 0 < 4*ρ-(z*(1+ρ))^2) :
    ∃ n : ℕ, z ≤ orbit ρ z n := by
  by_contra! h
  let d := (4*ρ-(z*(1+ρ))^2)/(4*z)
  have hd : 0<d := div_pos gap (by positivity)
  have lower (n : ℕ) : (n:ℝ)*d ≤ orbit ρ z n := by
    induction n with
    | zero => simp [orbit]
    | succ n ih =>
      have pos : 0≤orbit ρ z n := (mul_nonneg (Nat.cast_nonneg n) hd.le).trans ih
      have inc := uniform_increment hz pos (h n) gap
      change d ≤ orbit ρ z (n+1)-orbit ρ z n at inc
      push_cast
      linarith only [inc,ih]
  obtain ⟨n,hn⟩ := exists_nat_gt (z/d)
  have top := (div_lt_iff₀ hd).mp hn
  exact (not_lt_of_ge (lower n)) ((h n).trans top)

end BlockHierarchy.Recurrence
