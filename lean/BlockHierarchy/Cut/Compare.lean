import BlockHierarchy.Cut.ScoreBound
import BlockHierarchy.Cut.Statement
import BlockHierarchy.Cut.ColumnAverage

open scoped BigOperators
namespace BlockHierarchy.Cut

/-- Compare the optimal scores of two sources using the same finite cost kernel.
The two inequalities can be checked class by class, including zero output weights. -/
theorem compare_normalizers {X : Type*} [Fintype X] (P Q : X → ℝ) (τ : ℝ)
    (d : X → X → ℕ) (q v : X → ℝ) (ρ : ℝ) (hr : 0≤ρ)
    (hp : IsPrior P) (hq : IsPrior q) (hv : IsPrior v)
    (den : ∀ x, P x≤(1+ρ)*Q x)
    (zq : ∀ x, 0<Z τ d q x) (zv : ∀ x, 0<Z τ d v x)
    (a : ∀ y, (∑ x, P x*Real.exp (-τ*(d x y:ℝ))/Z τ d q x)≤1)
    (b : ∀ y, (∑ x, Q x*Real.exp (-τ*(d x y:ℝ))/Z τ d v x)≤1) :
    mean P (fun x => (score τ d q x-score τ d v x)^2) ≤ ρ := by
  let Δ := fun x => score τ d q x-score τ d v x
  have fwd (x : X) : Real.exp (Δ x)=Z τ d v x/Z τ d q x := by
    have e : Δ x=Real.log (Z τ d v x)-Real.log (Z τ d q x) := by unfold Δ score; ring
    rw [e,Real.exp_sub,Real.exp_log (zv x),Real.exp_log (zq x)]
  have rev (x : X) : Real.exp (-Δ x)=Z τ d q x/Z τ d v x := by
    have e : -Δ x=Real.log (Z τ d q x)-Real.log (Z τ d v x) := by unfold Δ score; ring
    rw [e,Real.exp_sub,Real.exp_log (zq x),Real.exp_log (zv x)]
  apply second_moment_of_column_bounds P Q Δ ρ hp.1 hp.2 den _ _ hr
  · simp_rw [fwd]
    exact weighted_column_bound P (Z τ d q) v _ hv.1 hv.2 a
  · simp_rw [rev]
    exact weighted_column_bound Q (Z τ d v) q _ hq.1 hq.2 b

end BlockHierarchy.Cut
