import BlockHierarchy.Four.Maximizer
import BlockHierarchy.Four.ParityOptimality

open Set Filter
open scoped Topology
namespace BlockHierarchy.Four

/-- Support changes impose equality in the column test even at a class of zero mass. -/
theorem boundary_column {T : Type*} [TopologicalSpace T] {S : Set T}
    (u : T → ℝ) (w : T → Class → ℝ) (p : ℝ) (i : Class) {t : T} (ht : t ∈ S)
    (cu : ContinuousOn u S) (cw : ContinuousOn w S)
    (hu : ∀ x ∈ S, 0 < u x) (hw : ∀ x ∈ S, w x ∈ stdSimplex ℝ Class)
    (active : ∀ x ∈ S, w x i ≠ 0 → Z (u x) (ratio p (u x) (w x)) i = 1)
    (contact : t ∈ closure {x | x ∈ S ∧ w x i ≠ 0}) :
    Z (u t) (ratio p (u t) (w t)) i=1 := by
  let A := {x | x ∈ S ∧ w x i ≠ 0}
  have pos (j : Class) : Z (u t) (w t) j ≠ 0 := by
    simpa only [orbit_rep] using
      (Z_pos (hu t ht) (w t) (hw t ht).1 (hw t ht).2 (representative j)).ne'
  have data := (cu t ht).prodMk (cw t ht)
  have entry (j : Class) : ContinuousWithinAt (fun x => ratio p (u x) (w x) j) S t :=
    continuousWithinAt_const.div ((Z_continuous j).continuousAt.comp_continuousWithinAt data) (pos j)
  have cr : ContinuousWithinAt (fun x => ratio p (u x) (w x)) S t := continuousWithinAt_pi.mpr entry
  have str := (Z_continuous i).continuousAt.comp_continuousWithinAt ((cu t ht).prodMk cr)
  have thin := str.mono (show A ⊆ S from fun _ h => h.1)
  haveI : (𝓝[A] t).NeBot := mem_closure_iff_nhdsWithin_neBot.mp contact
  apply isClosed_singleton.mem_of_tendsto thin
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact active x hx.1 hx.2

end BlockHierarchy.Four
