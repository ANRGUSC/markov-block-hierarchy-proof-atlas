import BlockHierarchy.Four.WaterClasses

namespace BlockHierarchy.Four.WaterContinuity
open WaterFilling WaterClasses

noncomputable section

def evenCost (u θ : ℝ) := base u θ / kE u
def oddCost (u θ : ℝ) := base u (1-θ) / (kE u/2)
def evenLevel (p u θ : ℝ) :=
  let q := WaterFilling.ratio (evenS p) θ (evenCost u θ)
  max (max (q 1) (q 2)) (max (q 3) (q 4))
def oddLevel (p u θ : ℝ) :=
  let q := WaterFilling.ratio (oddS p) (1-θ) (oddCost u θ)
  max (q 1) (q 2)
def weights (p u θ : ℝ) :=
  join (clipped (evenS p) (evenLevel p u θ) (evenCost u θ))
    (clipped (oddS p) (oddLevel p u θ) (oddCost u θ))
def slope (p u θ : ℝ) :=
  paritySlope u (Four.ratio p u (weights p u θ)) (evenLevel p u θ) (oddLevel p u θ)

theorem canonical_allocation {p u θ : ℝ} (hp : 0<p) (ph : p<1/2) (hu : 0<u)
    (uh : u<1) (hθ : θ ∈ Set.Icc 0 1) :
    PrefixMaximum (evenS p) 4 θ (evenCost u θ) (evenLevel p u θ) ∧
    PrefixMaximum (oddS p) 2 (1-θ) (oddCost u θ) (oddLevel p u θ) ∧
    (∀ i, 0≤weights p u θ i) ∧ evenMass (weights p u θ)=θ ∧
    oddMass (weights p u θ)=1-θ ∧ (∑ i,weights p u θ i)=1 ∧
    ∀ i, let g := coefficient u i*Four.ratio p u (weights p u θ) i
         let η := if evenGroup i then evenLevel p u θ else oddLevel p u θ
         g≤η ∧ (weights p u θ i≠0 → g=η) := by
  obtain ⟨e,o,he,ho,hw⟩ := allocation hp ph hu uh hθ.1 hθ.2
  have ee : evenLevel p u θ = e := by
    obtain ⟨k,hk,h4,eq,best,_⟩ := he
    unfold evenLevel
    dsimp only
    apply le_antisymm
    · exact max_le (max_le (best 1 (by decide) (by decide)) (best 2 (by decide) (by decide)))
        (max_le (best 3 (by decide) (by decide)) (best 4 (by decide) (by decide)))
    · rw [eq]
      have : k=1 ∨ k=2 ∨ k=3 ∨ k=4 := by omega
      rcases this with rfl|rfl|rfl|rfl <;> simp [evenCost,le_max_iff]
  have eo : oddLevel p u θ = o := by
    obtain ⟨k,hk,h2,eq,best,_⟩ := ho
    unfold oddLevel
    dsimp only
    apply le_antisymm
    · exact max_le (best 1 (by decide) (by decide)) (best 2 (by decide) (by decide))
    · rw [eq]
      have : k=1 ∨ k=2 := by omega
      rcases this with rfl|rfl <;> simp [oddCost,le_max_iff]
  unfold weights
  rw [ee,eo]
  exact ⟨he, ho, hw⟩

theorem continuous_allocation {p u : ℝ} (hp : 0<p) (ph : p<1/2) (hu : 0<u) (uh : u<1) :
    ContinuousOn (evenLevel p u) (Set.Icc 0 1) ∧
    ContinuousOn (oddLevel p u) (Set.Icc 0 1) ∧
    (∀ i, ContinuousOn (fun θ => weights p u θ i) (Set.Icc 0 1)) ∧
    ContinuousOn (slope p u) (Set.Icc 0 1) := by
  obtain ⟨_,hgap,hgap',_⟩ := Coefficients.class_order_and_kernel_gaps.2 u hu uh
  have hk : 0 < kE u := sub_pos.mpr (hgap.trans hgap')
  have bp (x : ℝ) (hx : x ≤ 1) : 0 < base u x := by
    unfold base
    have diff : 0 < (u+u^3)/2-u^2 := sub_pos.mpr hgap
    nlinarith only [sq_pos_of_pos hu, mul_nonneg diff.le (sub_nonneg.mpr hx)]
  have hce : Continuous (evenCost u) := by unfold evenCost base; fun_prop
  have hco : Continuous (oddCost u) := by unfold oddCost base; fun_prop
  have prefixCont (s : ℕ → ℝ) (m c : ℝ → ℝ) (hm : Continuous m) (hc : Continuous c)
      (hpos : ∀ x ∈ Set.Icc (0:ℝ) 1, 0≤m x ∧ 0<c x) (j : ℕ) (hj : 0<j) :
      ContinuousOn (fun x => WaterFilling.ratio s (m x) (c x) j) (Set.Icc 0 1) := by
    unfold WaterFilling.ratio
    apply continuousOn_const.div (hm.add (continuous_const.mul hc)).continuousOn
    intro x hx
    obtain ⟨hm',hc'⟩ := hpos x hx
    have cast_pos : 0 < (j : ℝ) := by exact_mod_cast hj
    exact (add_pos_of_nonneg_of_pos hm' (mul_pos cast_pos hc')).ne'
  have pe := prefixCont (evenS p) id (evenCost u) continuous_id hce
    (fun x hx => ⟨hx.1, div_pos (bp x hx.2) hk⟩)
  have po := prefixCont (oddS p) (fun x => 1-x) (oddCost u) (continuous_const.sub continuous_id) hco
    (fun x hx => ⟨sub_nonneg.mpr hx.2, div_pos (bp _ (by linarith [hx.1])) (half_pos hk)⟩)
  have he : ContinuousOn (evenLevel p u) (Set.Icc 0 1) :=
    ContinuousOn.sup (ContinuousOn.sup (pe 1 (by decide)) (pe 2 (by decide)))
      (ContinuousOn.sup (pe 3 (by decide)) (pe 4 (by decide)))
  have ho : ContinuousOn (oddLevel p u) (Set.Icc 0 1) :=
    ContinuousOn.sup (po 1 (by decide)) (po 2 (by decide))
  have levels (x : ℝ) (hx : x ∈ Set.Icc 0 1) : 0<evenLevel p u x ∧ 0<oddLevel p u x := by
    obtain ⟨se,_,so,_⟩ := class_data hp ph
    obtain ⟨⟨k,hk₁,hk₄,ek,_,_⟩,⟨j,hj₁,hj₂,oj,_,_⟩,_⟩ := canonical_allocation hp ph hu uh hx
    rw [ek,oj]
    exact ⟨positive_ratio hk₁ hk₄ hx.1 (div_pos (bp _ hx.2) hk) se,
      positive_ratio hj₁ hj₂ (sub_nonneg.mpr hx.2) (div_pos (bp _ (by linarith [hx.1])) (half_pos hk)) so⟩
  have hw (i : Class) : ContinuousOn (fun θ => weights p u θ i) (Set.Icc 0 1) := by
    unfold weights join clipped
    by_cases hi : evenGroup i
    · simp only [hi, if_true]
      exact ContinuousOn.sup continuousOn_const ((continuousOn_const.div he (fun x hx => (levels x hx).1.ne')).sub hce.continuousOn)
    · simp only [hi, if_false]
      exact ContinuousOn.sup continuousOn_const ((continuousOn_const.div ho (fun x hx => (levels x hx).2.ne')).sub hco.continuousOn)
  refine ⟨he,ho,hw,?_⟩
  have hr (i : Class) : ContinuousOn (fun θ => Four.ratio p u (weights p u θ) i) (Set.Icc 0 1) := by
    unfold Four.ratio
    apply continuousOn_const.div
    · unfold Z classKernel groupMass otherMass
      have e := (((hw 0).add (hw 1)).add (hw 2)).add (hw 3)
      have o := (hw 4).add (hw 5)
      by_cases hi : evenGroup i <;> simp only [hi, if_true, if_false]
      · exact ((continuousOn_const.mul e).add (continuousOn_const.mul o)).add (continuousOn_const.mul (hw i))
      · exact ((continuousOn_const.mul o).add (continuousOn_const.mul e)).add (continuousOn_const.mul (hw i))
    · intro x hx
      obtain ⟨_,_,nonneg,_,_,unit,_⟩ := canonical_allocation hp ph hu uh hx
      have surj : ∀ j : Class, ∃ y : Word, orbit y = j := by decide
      obtain ⟨y, rfl⟩ := surj i
      exact (Z_pos hu _ nonneg unit y).ne'
  unfold slope paritySlope evenMass oddMass
  exact (he.sub ho).add (continuousOn_const.mul
    (((((hr 0).add (hr 1)).add (hr 2)).add (hr 3)).sub ((hr 4).add (hr 5))))

end
end BlockHierarchy.Four.WaterContinuity

#print axioms BlockHierarchy.Four.WaterContinuity.continuous_allocation
