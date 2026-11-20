import BlockHierarchy.Four.Maximizer

open Set
open scoped BigOperators

namespace BlockHierarchy.Four

/-- The distortion of the tilted channel, in units of errors per four-letter block. -/
noncomputable def outerCost (p u : ℝ) (w : Class → ℝ) : ℝ :=
  ∑ i, sourceClasses p i * (costNumerator u w i / Z u w i)

theorem outer_source_sum (p : ℝ) : ∑ i, sourceClasses p i = 1 := by
  rw [class_sum]
  exact class_totals.1 p

/-- Complement symmetry gives mean distance two at the unweighted channel. -/
theorem outer_cost_one (p : ℝ) {w : Class → ℝ} (hw : w ∈ stdSimplex ℝ Class) :
    outerCost p 1 w = 2 := by
  have unit := hw.2
  rw [class_sum] at unit
  have z (i : Class) : Z 1 w i = 1 := by
    by_cases e : evenGroup i <;>
      norm_num [Z, classKernel, groupMass, otherMass, cardinal, e] <;> linarith only [unit]
  have n (i : Class) : costNumerator 1 w i = 2 := by
    by_cases e : evenGroup i <;>
      norm_num [costNumerator, classKernel, groupMass, otherMass, cardinal, e] <;> linarith only [unit]
  simp only [outerCost, z, n, div_one, ← Finset.sum_mul, outer_source_sum, one_mul]

private theorem outer_distance_self (x : Word) : distance x x = 0 := by
  simp [distance, Three.hamming]

private theorem outer_distance_bound : ∀ x y : Word, distance x y ≤ 4 := by decide

private theorem outer_Z_diag {u : ℝ} (hu : 0 ≤ u) {w : Class → ℝ}
    (hw : ∀ i, 0 ≤ w i) (x : Word) : prior w x ≤ Z u w (orbit x) := by
  rw [← class_normalizer]
  calc
    prior w x = prior w x * u ^ distance x x := by simp [outer_distance_self]
    _ ≤ ∑ y, prior w y * u ^ distance x y := Finset.single_le_sum
      (fun y _ => mul_nonneg (div_nonneg (hw _) (cardinal_pos _).le) (pow_nonneg hu _))
      (Finset.mem_univ x)

theorem outer_Z_le_one {u : ℝ} (hu : 0 ≤ u) (uh : u ≤ 1)
    {w : Class → ℝ} (hw : w ∈ stdSimplex ℝ Class) (i : Class) : Z u w i ≤ 1 := by
  rw [← orbit_rep i, ← class_normalizer]
  calc
    _ ≤ ∑ y, prior w y * 1 := Finset.sum_le_sum fun y _ =>
      mul_le_mul_of_nonneg_left (pow_le_one₀ hu uh) (div_nonneg (hw.1 _) (cardinal_pos _).le)
    _ = 1 := by simp only [mul_one, group_weight, hw.2]

/-- Every off-diagonal term contains at least one factor of the multiplier. -/
theorem outer_numerator_le {u : ℝ} (hu : 0 ≤ u) (uh : u ≤ 1)
    {w : Class → ℝ} (hw : w ∈ stdSimplex ℝ Class) (i : Class) :
    costNumerator u w i ≤ 4*u := by
  have power (n : ℕ) (hn : n ≤ 4) : u^n * (n : ℝ) ≤ 4*u := by
    cases n with
    | zero => simpa using mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hu
    | succ k =>
      have h : u ^ (k+1) ≤ u := by
        simpa only [pow_succ, one_mul] using
          mul_le_mul_of_nonneg_right (show u^k ≤ 1 from pow_le_one₀ hu uh) hu
      have cast_bound : ((k+1:ℕ):ℝ) ≤ 4 := by exact_mod_cast hn
      calc
        u^(k+1) * ((k+1:ℕ):ℝ) ≤ u*4 := mul_le_mul h cast_bound (by positivity) hu
        _ = 4*u := mul_comm _ _
  rw [← orbit_rep i, ← class_cost_numerator]
  calc
    _ ≤ ∑ y, prior w y * (4*u) := Finset.sum_le_sum fun y _ =>
      mul_le_mul_of_nonneg_left (power _ (outer_distance_bound _ y))
        (div_nonneg (hw.1 _) (cardinal_pos _).le)
    _ = 4*u := by rw [← Finset.sum_mul, group_weight, hw.2, one_mul]

private noncomputable def outerUniform (i : Class) : ℝ := cardinal i / 16

private theorem outerUniform_mem : outerUniform ∈ stdSimplex ℝ Class := by
  constructor
  · intro i
    exact div_nonneg (cardinal_pos i).le (by norm_num)
  · rw [class_sum]
    norm_num [outerUniform, cardinal, evenGroup]

private theorem outerUniform_lower {u : ℝ} (hu : 0 ≤ u) (i : Class) :
    1/16 ≤ Z u outerUniform i := by
  have h := outer_Z_diag hu outerUniform_mem.1 (representative i)
  rw [orbit_rep] at h
  have e : prior outerUniform (representative i) = 1/16 := by
    unfold prior outerUniform
    rw [orbit_rep]
    field_simp [(cardinal_pos i).ne']
  rwa [e] at h

/-- Comparing with the uniform word law bounds every optimal normalizer away from
zero uniformly in the multiplier. The estimate remains valid at support changes. -/
theorem outer_optimal_Z_lower {p u : ℝ} (hp : 0 < p) (ph : p < 1/2)
    (hu : 0 < u) (uh : u ≤ 1) {w : Class → ℝ} (hw : w ∈ stdSimplex ℝ Class)
    (opt : IsMaxOn (objective p u) (stdSimplex ℝ Class) w) (i : Class) :
    Real.exp (Real.log (1/16) / sourceClasses p i) ≤ Z u w i := by
  have src := source_classes_pos hp ph
  have hz (j : Class) : 0 < Z u w j := by
    simpa only [orbit_rep] using Z_pos hu w hw.1 hw.2 (representative j)
  have lower : Real.log (1/16) ≤ objective p u w := by
    calc
      _ = ∑ j, sourceClasses p j * Real.log (1/16) := by
        rw [← Finset.sum_mul, outer_source_sum, one_mul]
      _ ≤ objective p u outerUniform := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num) (outerUniform_lower hu.le j)) (src j).le
      _ ≤ objective p u w := isMaxOn_iff.mp opt _ outerUniform_mem
  have rest : ∑ j ∈ Finset.univ.erase i, sourceClasses p j * Real.log (Z u w j) ≤ 0 :=
    Finset.sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (src j).le
      (Real.log_nonpos (hz j).le (outer_Z_le_one hu.le uh hw j))
  unfold objective at lower
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at lower
  have logr : Real.log (1/16) / sourceClasses p i ≤ Real.log (Z u w i) :=
    (div_le_iff₀ (src i)).2 (by linarith only [rest, lower])
  simpa only [Real.exp_log (hz i)] using Real.exp_le_exp.mpr logr

/-- A single sufficiently small positive multiplier gives optimal cost below any
positive budget. The chosen multiplier depends on the source and budget only. -/
theorem outer_small_multiplier {p d : ℝ} (hp : 0 < p) (ph : p < 1/2) (hd : 0 < d) :
    ∃ a ∈ Ioc (0:ℝ) 1, ∀ w ∈ stdSimplex ℝ Class,
      IsMaxOn (objective p a) (stdSimplex ℝ Class) w → outerCost p a w ≤ d := by
  let floor (i : Class) := Real.exp (Real.log (1/16) / sourceClasses p i)
  let k := ∑ i, sourceClasses p i * (4 / floor i)
  have hfloor (i : Class) : 0 < floor i := Real.exp_pos _
  have src := source_classes_pos hp ph
  have hk : 0 ≤ k := Finset.sum_nonneg fun i _ =>
    mul_nonneg (src i).le (div_nonneg (by norm_num) (hfloor i).le)
  have hkp : 0 < k+1 := by linarith
  let a := min 1 (d/(k+1))
  have ha : 0 < a := lt_min (by norm_num) (div_pos hd hkp)
  have ah : a ≤ 1 := min_le_left _ _
  refine ⟨a, ⟨ha,ah⟩, ?_⟩
  intro w hw opt
  have row (i : Class) : costNumerator a w i / Z a w i ≤ a * (4 / floor i) := by
    have z := outer_optimal_Z_lower hp ph ha ah hw opt i
    have pos : 0 < Z a w i := (hfloor i).trans_le z
    calc
      _ ≤ (4*a) / Z a w i := div_le_div_of_nonneg_right (outer_numerator_le ha.le ah hw i) pos.le
      _ ≤ (4*a) / floor i := div_le_div_of_nonneg_left (by positivity) (hfloor i) z
      _ = a * (4 / floor i) := by ring
  calc
    outerCost p a w ≤ ∑ i, sourceClasses p i * (a*(4/floor i)) := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (row i) (src i).le
    _ = a*k := by unfold k; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
    _ ≤ a*(k+1) := mul_le_mul_of_nonneg_left (by linarith) ha.le
    _ ≤ d := (le_div_iff₀ hkp).mp (min_le_right _ _)

end BlockHierarchy.Four
