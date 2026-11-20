import BlockHierarchy.Recurrence

namespace BlockHierarchy.Recurrence

noncomputable def signedChild (ρ z μ y : ℝ) := ρ*((μ+y/z)/(1+y*μ/z))

noncomputable def peak (ρ z x : ℝ) := ρ*((1-z*x)/(z-x))

private theorem nonnegative_extrema {ρ z x : ℝ} (hr : 0<ρ) (hz : 0<z) (hz1 : z<1)
    (hx : 0≤x) (h : x<z) :
    |signedChild ρ z x 1| ≤ peak ρ z x ∧ |signedChild ρ z x (-1)| = peak ρ z x := by
  have xp : 0<z+x := by linarith
  have xm : 0<z-x := by linarith
  have zx : z*x<1 := by
    have := mul_lt_mul_of_pos_left (h.trans hz1) hz
    linarith
  have plus : signedChild ρ z x 1=ρ*((1+z*x)/(z+x)) := by
    unfold signedChild
    simp only [one_mul]
    rw [show 1+x/z=(z+x)/z by field_simp [hz.ne']]
    field_simp [xp.ne',hz.ne'] <;> ring
  have minus : signedChild ρ z x (-1) = -peak ρ z x := by
    unfold signedChild peak
    rw [neg_one_mul,show 1+ -x/z=(z-x)/z by field_simp [hz.ne']; ring]
    field_simp [xm.ne',hz.ne'] <;> ring
  have qpos : 0<peak ρ z x := mul_pos hr (div_pos (sub_pos.mpr zx) xm)
  rw [plus,minus,abs_neg,abs_of_pos qpos,abs_of_nonneg (by positivity : 0 ≤ ρ*((1+z*x)/(z+x)))]
  refine ⟨mul_le_mul_of_nonneg_left ?_ hr.le,rfl⟩
  apply (div_le_div_iff₀ xp xm).mpr
  have fact := mul_nonneg hx (mul_nonneg (sub_nonneg.mpr hz1.le) (show 0≤1+z by positivity))
  nlinarith only [fact]

private theorem child_reflect (ρ z x y : ℝ) :
    signedChild ρ z (-x) (-y) = -signedChild ρ z x y := by
  unfold signedChild
  rw [neg_mul_neg,neg_div,← neg_add,neg_div,mul_neg]

/-- The worse extension has the opposite sign. For a zero moment either sign attains the bound. -/
theorem signed_child_max {ρ z μ : ℝ} (hr : 0<ρ) (hz : 0<z) (hz1 : z<1) (inside : |μ|<z) :
    max |signedChild ρ z μ 1| |signedChild ρ z μ (-1)|=peak ρ z |μ| ∧
    |signedChild ρ z μ (if 0≤μ then -1 else 1)|=peak ρ z |μ| := by
  by_cases h : 0≤μ
  · rw [abs_of_nonneg h] at inside ⊢
    obtain ⟨le,eq⟩ := nonnegative_extrema hr hz hz1 h inside
    simp [if_pos h,eq,max_eq_right le]
  · have hm : μ<0 := lt_of_not_ge h
    rw [abs_of_neg hm] at inside ⊢
    obtain ⟨le,eq⟩ := nonnegative_extrema hr hz hz1 (neg_nonneg.mpr hm.le) inside
    have neg : |signedChild ρ z (-μ) (-1)|=|signedChild ρ z μ 1| := by
      rw [child_reflect,abs_neg]
    have pos : |signedChild ρ z (-μ) 1|=|signedChild ρ z μ (-1)| := by
      simpa only [neg_neg,abs_neg] using congrArg abs (child_reflect ρ z μ (-1))
    rw [neg] at eq
    rw [pos] at le
    rw [if_neg h,eq,max_eq_left le]
    exact ⟨rfl,rfl⟩

def spin (b : Bool) : ℝ := if b then 1 else -1

/-- Prefixes are actual finite sign strings. The child layer consists of both
possible extensions to each parent, indexed by its original string and appended bit. -/
theorem next_layer_peak (parents : Finset (List Bool)) (nonempty : parents.Nonempty)
    (μ : List Bool → ℝ) {ρ z : ℝ} (hr : 0<ρ) (hz : 0<z) (hz1 : z<1)
    (inside : ∀ x ∈ parents, |μ x|<z) :
    ∃ x ∈ parents, (∀ y ∈ parents, |μ y|≤|μ x|) ∧
      IsGreatest {v : ℝ | ∃ y ∈ parents, ∃ b : Bool, v=|signedChild ρ z (μ y) (spin b)|}
        (peak ρ z |μ x|) := by
  obtain ⟨x,hx,hmax⟩ := Finset.exists_max_image parents (fun y => |μ y|) nonempty
  refine ⟨x,hx,hmax,?_,?_⟩
  · refine ⟨x,hx,decide (μ x < 0),?_⟩
    have opp := (signed_child_max hr hz hz1 (inside x hx)).2.symm
    by_cases h : 0≤μ x
    · simpa [spin,h,not_lt.mpr h] using opp
    · simpa [spin,h,lt_of_not_ge h] using opp
  · rintro _ ⟨y,hy,b,rfl⟩
    have bound := (signed_child_max hr hz hz1 (inside y hy)).1
    have localB : |signedChild ρ z (μ y) (spin b)| ≤ peak ρ z |μ y| := by
      rw [← bound]
      cases b
      · exact le_max_right .. 
      · exact le_max_left ..
    apply localB.trans
    rcases eq_or_lt_of_le (hmax y hy) with eq | lt
    · rw [eq]
    · exact (recurrence_strict ρ z _ _ hr hz hz1 (abs_nonneg _) lt (inside x hx)).le

#print axioms signed_child_max
#print axioms next_layer_peak
end BlockHierarchy.Recurrence
