import BlockHierarchy.Four.Assembly
import BlockHierarchy.Four.GroupCertificate

open Set
open scoped BigOperators
namespace BlockHierarchy.Four
open WaterContinuity WaterClasses

theorem paper_allocation {p u θ : ℝ} (hp : 0<p) (ph : p<1/2) (hu : u∈Ioo (0:ℝ) 1)
    (hθ : θ∈Icc (0:ℝ) 1) :
    PaperAllocation p u θ (evenLevel p u θ) (oddLevel p u θ) (weights p u θ) := by
  obtain ⟨e,o,pos,even,odd,total,gains⟩ := canonical_allocation hp ph hu.1 hu.2 hθ
  obtain ⟨es,eo,os,oo⟩ := class_data hp ph
  obtain ⟨χpos,cb,ba,_⟩ := Coefficients.class_order_and_kernel_gaps.2 u hu.1 hu.2
  have kpos : 0<kE u := sub_pos.mpr (cb.trans ba)
  have basepos (m : ℝ) (hm : m≤1) : 0<base u m := by
    change 0<u^2*m+(u+u^3)/2*(1-m)
    have gap : 0<(u+u^3)/2-u^2 := sub_pos.mpr cb
    nlinarith only [sq_pos_of_pos hu.1,mul_nonneg gap.le (sub_nonneg.mpr hm)]
  refine ⟨paper_group_of_max (by decide) hθ.1 (div_pos (basepos _ hθ.2) kpos) es eo e,
    paper_group_of_max (by decide) (sub_nonneg.mpr hθ.2)
      (div_pos (basepos _ (by linarith only [hθ.1])) (half_pos kpos)) os oo o,
    rfl,⟨⟨pos,total⟩,even⟩,odd,affine_Z u _,?_⟩
  intro v hv
  have mass : evenMass v=θ := hv.2
  have h := parity_support hp ph hu.1 (water_simplex hp ph hu hθ) hv.1 _ _ gains
  change objective p u v ≤ objective p u (weights p u θ)
  simpa only [mass,even,sub_self,mul_zero,add_zero] using h

theorem four_symbol_rate_variance : FourSymbolStatement := by
  intro p hp ph
  obtain ⟨_,eo,_,oo⟩ := class_data hp ph
  exact ⟨eo,oo,weights p,evenLevel p,oddLevel p,
    fun _ hu _ hθ => paper_allocation hp ph hu hθ,
    fun _ hu => water_parity hp ph hu,
    fun _ hD => water_paper_point hp ph hD,water_thresholds hp ph⟩

#print axioms four_symbol_rate_variance

end BlockHierarchy.Four
