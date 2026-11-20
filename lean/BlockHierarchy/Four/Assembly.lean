import BlockHierarchy.Four.WaterContinuity
import BlockHierarchy.Four.PaperStatement
import BlockHierarchy.Four.UniqueMaximizer
import BlockHierarchy.Four.OuterMultiplier
import BlockHierarchy.Four.SupportBoundary

open Set
open scoped BigOperators
namespace BlockHierarchy.Four
open WaterContinuity WaterClasses

theorem water_simplex {p u θ : ℝ} (hp : 0<p) (ph : p<1/2) (hu : u∈Ioo (0:ℝ) 1)
    (hθ : θ∈Icc (0:ℝ) 1) : weights p u θ ∈ stdSimplex ℝ Class := by
  obtain ⟨_,_,pos,_,_,total,_⟩ := canonical_allocation hp ph hu.1 hu.2 hθ
  exact ⟨pos,total⟩

theorem water_parity {p u : ℝ} (hp : 0<p) (ph : p<1/2) (hu : u∈Ioo (0:ℝ) 1) :
    PaperParity p u (weights p u) (evenLevel p u) (oddLevel p u) := by
  let V := fun θ => objective p u (weights p u θ)
  let G := slope p u
  have cont : ContinuousOn G (Icc 0 1) := (continuous_allocation hp ph hu.1 hu.2).2.2.2
  have support (θ : ℝ) (hθ : θ ∈ Icc 0 1) (t : ℝ) (ht : t ∈ Icc 0 1) :
      V t ≤ V θ+G θ*(t-θ) := by
    obtain ⟨_,_,_,wθ,_,_,gains⟩ := canonical_allocation hp ph hu.1 hu.2 hθ
    obtain ⟨_,_,_,wt,_,_,_⟩ := canonical_allocation hp ph hu.1 hu.2 ht
    simpa only [V,G,WaterContinuity.slope,wθ,wt] using parity_support hp ph hu.1 (water_simplex hp ph hu hθ)
      (water_simplex hp ph hu ht) _ _ gains
  refine ⟨fun θ hθ => derivative_of_supports V G cont support hθ,support,choose_parity G cont,?_⟩
  intro θ hθ choice
  obtain ⟨_,_,_,mass,_,_,gains⟩ := canonical_allocation hp ph hu.1 hu.2 hθ
  have hw := water_simplex hp ph hu hθ
  have opt := chosen_maximizes hp ph hu.1 hw _ _ gains (by simpa only [mass,ParityChoice] using choice)
  exact ⟨opt,fun v hv ov => unique_maximizer hp ph hu.1 hu.2 hv hw ov opt⟩

theorem optimal_at_trial {p u : ℝ} (hp : 0<p) (ph : p<1/2) (hu : u∈Ioo (0:ℝ) 1)
    {v : Class → ℝ} (hv : v∈stdSimplex ℝ Class) (ov : IsMaxOn (objective p u) (stdSimplex ℝ Class) v) :
    ∃ θ ∈ Icc (0:ℝ) 1, ParityChoice (slope p u) θ ∧ v=weights p u θ ∧
    ∀ i, Z u (ratio p u v) i ≤ 1 ∧ (v i ≠ 0 → Z u (ratio p u v) i=1) := by
  obtain ⟨_,_,⟨θ,hθ,choice⟩,select⟩ := water_parity hp ph hu
  have eq := (select θ hθ choice).2 v hv ov
  subst v
  obtain ⟨_,_,nn,even,odd,total,gains⟩ := canonical_allocation hp ph hu.1 hu.2 hθ
  refine ⟨θ,hθ,choice,rfl,parity_columns _ _ _ hu.1 nn total gains ?_⟩
  change ParityChoice (slope p u) θ at choice
  change (evenMass _=0 ∧ slope p u θ≤0) ∨ (oddMass _=0 ∧ 0≤slope p u θ) ∨ slope p u θ=0
  rw [even,odd]
  rcases choice with h|⟨h,g⟩|h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨by linarith only [h],g⟩)
  · exact Or.inr (Or.inr h)

theorem water_paper_point {p D : ℝ} (hp : 0<p) (ph : p<1/2) (hD : D∈Ioo (0:ℝ) (1/2)) :
    ∃ u ∈ Ioo (0:ℝ) 1, ∃ θ ∈ Icc (0:ℝ) 1, ParityChoice (slope p u) θ ∧ PaperPoint p D u (weights p u θ) := by
  obtain ⟨u,hu,v,hv,ov,cost⟩ := exists_optimal_multiplier hp ph hD.1 hD.2
  obtain ⟨θ,hθ,choice,eq,dual⟩ := optimal_at_trial hp ph hu hv ov
  refine ⟨u,hu,θ,hθ,choice,eq ▸ ?_⟩
  have budget := (normalized_cost p u v).trans cost
  refine ⟨class_normalizer u v,fun i => ⟨baseline_derivative u v i,coefficient_derivative u i⟩,
    budget.symm.trans (distortion_eq p u v),budget,rate_and_variance hp ph hu.1 hu.2.le v hv.1 hv.2 dual cost⟩

theorem water_thresholds {p : ℝ} (hp : 0<p) (ph : p<1/2) : PaperThresholds p := by
  intro i t ht inactive active
  have closed : IsClosed {x : ℝ × (Class → ℝ) | x.2 i=0} :=
    isClosed_eq ((continuous_apply i).comp continuous_snd) continuous_const
  refine ⟨closure_minimal (fun x h => h.2) closed inactive,?_⟩
  apply boundary_column Prod.fst Prod.snd p i ht continuous_fst.continuousOn continuous_snd.continuousOn
    (fun x hx => hx.1.1) (fun x hx => hx.2.1)
  · intro x hx nonzero
    obtain ⟨_,_,_,_,dual⟩ := optimal_at_trial hp ph hx.1 hx.2.1 hx.2.2
    exact (dual i).2 nonzero
  · apply closure_mono _ active
    intro x h
    exact ⟨h.1,h.2.ne'⟩

end BlockHierarchy.Four
