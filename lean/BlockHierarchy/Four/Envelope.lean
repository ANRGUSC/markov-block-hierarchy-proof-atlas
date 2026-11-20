import BlockHierarchy.Four.ParityOptimality
import Mathlib.Analysis.Calculus.Deriv.Slope

open Filter Set
open scoped BigOperators Topology
namespace BlockHierarchy.Four

/-- A continuous supporting slope differentiates the restricted value even
where several allocation formulas meet. At endpoints this is a one-sided derivative. -/
theorem derivative_of_supports {s : Set ℝ} (V G : ℝ → ℝ)
    (cont : ContinuousOn G s) (support : ∀ x ∈ s, ∀ y ∈ s, V y ≤ V x+G x*(y-x))
    {x : ℝ} (hx : x ∈ s) : HasDerivWithinAt V (G x) s x := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hg : Tendsto G (𝓝[s \ {x}] x) (𝓝 (G x)) := (cont x hx).mono (fun _ h => h.1)
  have bounds : ∀ᶠ y in 𝓝[s \ {x}] x, min (G x) (G y) ≤ slope V x y ∧ slope V x y ≤ max (G x) (G y) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have up := support x hx y hy.1
    have down := support y hy.1 x hx
    have ne : y ≠ x := fun h => hy.2 (by simp [h])
    rw [slope_def_field]
    rcases lt_or_gt_of_ne ne with lt|gt
    · have d := sub_neg.mpr lt
      exact ⟨(min_le_left ..).trans ((le_div_iff_of_neg d).mpr (by linarith only [up])),
        ((div_le_iff_of_neg d).mpr (by linarith only [down])).trans (le_max_right ..)⟩
    · have d := sub_pos.mpr gt
      exact ⟨(min_le_right ..).trans ((le_div_iff₀ d).mpr (by linarith only [down])),
        ((div_le_iff₀ d).mpr (by linarith only [up])).trans (le_max_left ..)⟩
  have lower : Tendsto (fun y => min (G x) (G y)) (𝓝[s \ {x}] x) (𝓝 (G x)) := by
    simpa using (tendsto_const_nhds (x := G x)).min hg
  have upper : Tendsto (fun y => max (G x) (G y)) (𝓝[s \ {x}] x) (𝓝 (G x)) := by
    simpa using (tendsto_const_nhds (x := G x)).max hg
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' lower upper (bounds.mono fun _ h => h.1)
    (bounds.mono fun _ h => h.2)

end BlockHierarchy.Four
