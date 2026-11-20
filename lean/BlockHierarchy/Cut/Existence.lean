import BlockHierarchy.Cut.Optimality
import Mathlib.Analysis.Convex.StdSimplex

open scoped BigOperators
namespace BlockHierarchy.Cut

/-- Every finite nonempty reproduction alphabet admits a global optimizer of the
canonical objective for every finite real multiplier. -/
theorem exists_optimal {X : Type*} [Fintype X] [Nonempty X]
    (P : X → ℝ) (τ : ℝ) (d : X → X → ℕ) : ∃ q, Optimal P τ d q := by
  classical
  let F (q : X → ℝ) := mean P (score τ d q)
  have cont : ContinuousOn F (stdSimplex ℝ X) := by
    intro q hq
    apply ContinuousAt.continuousWithinAt
    have row (x : X) : Continuous (fun r : X → ℝ => Z τ d r x) := by
      unfold Z
      fun_prop
    have entry (x : X) : ContinuousAt (fun r => P x * score τ d r x) q :=
      continuousAt_const.mul ((row x).continuousAt.log (Z_pos τ d hq x).ne').neg
    have part (s : Finset X) : ContinuousAt (fun r => ∑ x ∈ s, P x*score τ d r x) q := by
      induction s using Finset.induction_on with
      | empty => simp only [Finset.sum_empty]; exact continuousAt_const
      | @insert a s ha ih =>
        simp only [Finset.sum_insert ha]
        exact (entry a).add ih
    exact part Finset.univ
  obtain ⟨q, hq, opt⟩ := (isCompact_stdSimplex ℝ X).exists_isMinOn
    ⟨_,single_mem_stdSimplex ℝ (Classical.arbitrary X)⟩ cont
  exact ⟨q, hq, fun r hr => opt hr⟩

#print axioms exists_optimal
end BlockHierarchy.Cut
