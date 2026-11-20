import BlockHierarchy.Three.Distortion
import BlockHierarchy.Three.Thresholds

open Set

namespace BlockHierarchy.Three

noncomputable def secondD (p : ℝ) := constantCost p (secondU p)/3

theorem endpoint_costs {p : ℝ} (hp : 0 < p) (half : p < 1/2) :
    middleCost p (firstU p) = 3*criticalD p ∧
    middleCost p (secondU p) = 3*secondD p ∧ constantCost p 1 = 3/2 := by
  obtain ⟨hd,hd',_,hu,_,_,he,hp'⟩ := thresholds hp half
  let t := secondU p
  have ht : 0 < t := by unfold t secondU; positivity
  have eqD : criticalD p=t^2/(1+t^2) := by
    have e := (div_eq_iff (by linarith : 1-criticalD p ≠ 0)).mp
      (show criticalD p/(1-criticalD p)=t^2 from he)
    apply (eq_div_iff (by positivity)).mpr
    linarith only [e]
  change t/(1+t^2)=p at hp'
  change firstU p=t^2 at he
  constructor
  · rw [he,eqD,← hp']
    unfold middleCost
    field_simp
    <;> ring
  constructor
  · change middleCost p t=3*(constantCost p t/3)
    rw [← hp']
    unfold middleCost constantCost
    field_simp
    <;> ring
  · unfold constantCost
    norm_num
    <;> ring

private theorem inverse_on {f : ℝ → ℝ} {a b v : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b)) (hm : StrictMonoOn f (Icc a b))
    (hv : v ∈ Icc (f a) (f b)) : ∃! u, u ∈ Icc a b ∧ f u=v := by
  obtain ⟨u,hu,h⟩ := intermediate_value_Icc hab hc hv
  exact ⟨u,⟨hu,h⟩,fun y hy => hm.injOn hy.1 hu (hy.2.trans h.symm)⟩

theorem middle_inverse {p D : ℝ} (hp : 0 < p) (half : p < 1/2)
    (lower : criticalD p < D) (upper : D < secondD p) :
    ∃! u, u ∈ Ioo (firstU p) (secondU p) ∧ middleCost p u=3*D := by
  obtain ⟨_,_,_,hu,hab,_,_,_⟩ := thresholds hp half
  obtain ⟨e1,e2,_⟩ := endpoint_costs hp half
  have hm : StrictMonoOn (middleCost p) (Icc (firstU p) (secondU p)) :=
    fun _ hx _ _ h => middleCost_strict hp half (hu.le.trans hx.1) h
  have hc : ContinuousOn (middleCost p) (Icc (firstU p) (secondU p)) := by
    intro x hx
    have hx0 := hu.le.trans hx.1
    apply ContinuousAt.continuousWithinAt
    unfold middleCost
    fun_prop (disch := positivity)
  obtain ⟨u,⟨hU,eqU⟩,uniq⟩ := inverse_on hab.le hc hm
    (show 3*D ∈ Icc _ _ from ⟨by linarith,by linarith⟩)
  have lo := lt_of_le_of_ne hU.1 (by intro e; rw [← e,e1] at eqU; linarith)
  have hi := lt_of_le_of_ne hU.2 (by intro e; rw [e,e2] at eqU; linarith)
  exact ⟨u,⟨⟨lo,hi⟩,eqU⟩,fun y hy => uniq y ⟨⟨hy.1.1.le,hy.1.2.le⟩,hy.2⟩⟩

theorem constant_inverse {p D : ℝ} (hp : 0 < p) (half : p < 1/2)
    (lower : secondD p ≤ D) (upper : D < 1/2) :
    ∃! u, u ∈ Ico (secondU p) 1 ∧ constantCost p u=3*D := by
  obtain ⟨_,_,_,hu,hab,h1,_,_⟩ := thresholds hp half
  have hs := hu.trans hab
  obtain ⟨_,_,e2⟩ := endpoint_costs hp half
  have e1 : constantCost p (secondU p)=3*secondD p := by unfold secondD; ring
  have hm : StrictMonoOn (constantCost p) (Icc (secondU p) 1) :=
    fun _ hx _ _ h => constantCost_strict hp half (hs.le.trans hx.1) h
  have hc : ContinuousOn (constantCost p) (Icc (secondU p) 1) := by
    intro x hx
    have hx0 := hs.le.trans hx.1
    apply ContinuousAt.continuousWithinAt
    unfold constantCost
    fun_prop (disch := positivity)
  obtain ⟨u,⟨hU,eqU⟩,uniq⟩ := inverse_on h1.le hc hm
    (show 3*D ∈ Icc _ _ from ⟨by linarith,by linarith⟩)
  have hi := lt_of_le_of_ne hU.2 (by intro e; rw [e,e2] at eqU; linarith)
  exact ⟨u,⟨⟨hU.1,hi⟩,eqU⟩,fun y hy => uniq y ⟨⟨hy.1.1,hy.1.2.le⟩,hy.2⟩⟩

end BlockHierarchy.Three
