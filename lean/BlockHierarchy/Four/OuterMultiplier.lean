import BlockHierarchy.Four.OuterBounds
import BlockHierarchy.Four.OuterConnected
import BlockHierarchy.Four.OuterGeometry

open Set
open scoped BigOperators

namespace BlockHierarchy.Four

private abbrev TrialInterval (a : ℝ) := ↥(Icc a (1:ℝ))
private abbrev TrialPrior := ↥(stdSimplex ℝ Class)

private noncomputable def trialObjective (a p : ℝ) (z : TrialInterval a × TrialPrior) :=
  objective p z.1.1 z.2.1

private noncomputable def trialCost (a p : ℝ) (z : TrialInterval a × TrialPrior) :=
  outerCost p z.1.1 z.2.1

private theorem trialCoords (a : ℝ) :
    Continuous (fun z : TrialInterval a × TrialPrior => (z.1.1, z.2.1)) :=
  (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)

private theorem trialZ_continuous (a : ℝ) (i : Class) :
    Continuous (fun z : TrialInterval a × TrialPrior => Z z.1.1 z.2.1 i) :=
  (Z_continuous i).comp (trialCoords a)

private theorem trialZ_ne_zero {a : ℝ} (ha : 0 < a) (i : Class) (z : TrialInterval a × TrialPrior) :
    Z z.1.1 z.2.1 i ≠ 0 := by
  have pos := Z_pos (ha.trans_le z.1.property.1) z.2.1 z.2.property.1 z.2.property.2 (representative i)
  simpa only [orbit_rep] using pos.ne'

private theorem trialObjective_continuous {a : ℝ} (ha : 0 < a) (p : ℝ) :
    Continuous (trialObjective a p) := by
  unfold trialObjective objective
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul ((trialZ_continuous a i).log (trialZ_ne_zero ha i))

private theorem outer_numerator_continuous (i : Class) :
    Continuous (fun t : ℝ × (Class → ℝ) => costNumerator t.1 t.2 i) := by
  unfold costNumerator classKernel groupMass otherMass
  by_cases e : evenGroup i <;> simp only [e, if_true, if_false] <;> fun_prop

private theorem trialCost_continuous {a : ℝ} (ha : 0 < a) (p : ℝ) :
    Continuous (trialCost a p) := by
  unfold trialCost outerCost
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul (((outer_numerator_continuous i).comp (trialCoords a)).div
    (trialZ_continuous a i) (trialZ_ne_zero ha i))

private theorem trial_optimal_fibre {p a : ℝ} (hp : 0 < p) (ph : p < 1/2)
    (ha : 0 < a) (t : TrialInterval a) :
    IsPreconnected {w : TrialPrior | ∀ v, trialObjective a p (t,v) ≤ trialObjective a p (t,w)} := by
  simp only [trialObjective]
  exact outer_optimal_fibre (p := p) (u := t.1) hp ph (ha.trans_le t.property.1)

/-- The outer search in the four-symbol theorem attains every interior distortion.
The probability vector is a global maximizer at the returned multiplier. -/
theorem exists_optimal_multiplier {p D : ℝ} (hp : 0 < p) (ph : p < 1/2)
    (hD : 0 < D) (Dh : D < 1/2) :
    ∃ u ∈ Ioo (0:ℝ) 1, ∃ w ∈ stdSimplex ℝ Class,
      IsMaxOn (objective p u) (stdSimplex ℝ Class) w ∧
      (∑ i, sourceClasses p i * (costNumerator u w i / Z u w i)) = 4*D := by
  obtain ⟨a, ha, small⟩ := outer_small_multiplier hp ph (show 0 < 4*D by positivity)
  let : PreconnectedSpace (TrialInterval a) := Subtype.preconnectedSpace isPreconnected_Icc
  let : Nonempty TrialPrior := ⟨⟨_, single_mem_stdSimplex ℝ (0:Class)⟩⟩
  obtain ⟨v,hv,mv⟩ := exists_optimal_prior p ha.1
  obtain ⟨q,hq,mq⟩ := exists_optimal_prior p (show (0:ℝ) < 1 by norm_num)
  have low : ∃ (t : TrialInterval a) (x : TrialPrior),
      (∀ y, trialObjective a p (t,y) ≤ trialObjective a p (t,x)) ∧ trialCost a p (t,x) ≤ 4*D := by
    refine ⟨⟨a,left_mem_Icc.mpr ha.2⟩, ⟨v,hv⟩, ?_, small v hv mv⟩
    exact fun y => isMaxOn_iff.mp mv _ y.property
  have high : ∃ (t : TrialInterval a) (x : TrialPrior),
      (∀ y, trialObjective a p (t,y) ≤ trialObjective a p (t,x)) ∧ 4*D ≤ trialCost a p (t,x) := by
    refine ⟨⟨1,right_mem_Icc.mpr ha.2⟩, ⟨q,hq⟩, ?_, ?_⟩
    · exact fun y => isMaxOn_iff.mp mq _ y.property
    · change 4*D ≤ outerCost p 1 q
      rw [outer_cost_one p hq]
      linarith only [Dh]
  obtain ⟨t,w,mw,budget⟩ := exists_optimal_cost_between
    (trialObjective a p) (trialCost a p) (trialObjective_continuous ha.1 p) (trialCost_continuous ha.1 p)
    (4*D) (trial_optimal_fibre hp ph ha.1) low high
  change outerCost p t.1 w.1 = 4*D at budget
  have strict : t.1 < 1 := lt_of_le_of_ne t.property.2 (by
    intro e
    rw [e, outer_cost_one p w.property] at budget
    linarith only [Dh, budget])
  exact ⟨t.1, ⟨ha.1.trans_le t.property.1, strict⟩, w.1, w.property,
    isMaxOn_iff.mpr (fun y hy => mw ⟨y,hy⟩), budget⟩

end BlockHierarchy.Four
