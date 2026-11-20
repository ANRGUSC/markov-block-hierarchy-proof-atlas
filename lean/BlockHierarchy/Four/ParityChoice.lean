import BlockHierarchy.Four.SupportingParity
import BlockHierarchy.Four.Envelope

open Set
open scoped BigOperators
namespace BlockHierarchy.Four

def ParityChoice (G : ℝ → ℝ) (θ : ℝ) : Prop :=
  (θ=0 ∧ G θ≤0) ∨ (θ=1 ∧ 0≤G θ) ∨ G θ=0

theorem choose_parity (G : ℝ → ℝ) (cg : ContinuousOn G (Icc 0 1)) :
    ∃ θ ∈ Icc (0:ℝ) 1, ParityChoice G θ := by
  by_cases left : G 0 ≤ 0
  · exact ⟨0,⟨le_rfl,zero_le_one⟩,Or.inl ⟨rfl,left⟩⟩
  by_cases right : 0 ≤ G 1
  · exact ⟨1,⟨zero_le_one,le_rfl⟩,Or.inr (Or.inl ⟨rfl,right⟩)⟩
  obtain ⟨θ,hθ,zero⟩ := intermediate_value_Icc' zero_le_one cg
    (show (0:ℝ) ∈ Icc (G 1) (G 0) from ⟨(lt_of_not_ge right).le,(lt_of_not_ge left).le⟩)
  exact ⟨θ,hθ,Or.inr (Or.inr zero)⟩

theorem evenMass_interval {w : Class → ℝ} (hw : w ∈ stdSimplex ℝ Class) :
    evenMass w ∈ Icc (0:ℝ) 1 := by
  have even : 0≤evenMass w := by unfold evenMass; linarith only [hw.1 0,hw.1 1,hw.1 2,hw.1 3]
  have odd : 0≤oddMass w := add_nonneg (hw.1 4) (hw.1 5)
  exact ⟨even,by linarith only [(mass_partition w).symm.trans hw.2,odd]⟩

theorem chosen_maximizes {p u : ℝ} (hp : 0<p) (ph : p<1/2) (hu : 0<u)
    {w : Class → ℝ} (hw : w ∈ stdSimplex ℝ Class) (e o : ℝ)
    (gains : ∀ i, let g := coefficient u i*ratio p u w i; let η := if evenGroup i then e else o
                   g ≤ η ∧ (w i≠0 → g=η))
    (choice : let G := paritySlope u (ratio p u w) e o
      (evenMass w=0 ∧ G≤0) ∨ (evenMass w=1 ∧ 0≤G) ∨ G=0) :
    IsMaxOn (objective p u) (stdSimplex ℝ Class) w := by
  intro v hv
  have h := parity_support hp ph hu hw hv e o gains
  have vbound := evenMass_interval hv
  let G := paritySlope u (ratio p u w) e o
  change objective p u v ≤ objective p u w + G*(evenMass v-evenMass w) at h
  change (evenMass w=0 ∧ G≤0) ∨ (evenMass w=1 ∧ 0≤G) ∨ G=0 at choice
  change objective p u v ≤ objective p u w
  rcases choice with ⟨hw0,sgn⟩|⟨hw1,sgn⟩|zero
  · rw [hw0,sub_zero] at h
    linarith only [h,mul_nonpos_of_nonpos_of_nonneg sgn vbound.1]
  · rw [hw1] at h
    linarith only [h,mul_nonpos_of_nonneg_of_nonpos sgn (sub_nonpos.mpr vbound.2)]
  · simpa [zero] using h

end BlockHierarchy.Four
