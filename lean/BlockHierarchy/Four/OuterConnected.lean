import BlockHierarchy.Four.Maximizer
import Mathlib.Topology.Order.IntermediateValue

open Set
open scoped BigOperators

namespace BlockHierarchy.Four

/-- A continuous cost crosses every budget between two optimal costs, even when an
optimizer is not unique. Compactness makes the two projections closed; connectedness
of a single fibre fills the possible gap at their intersection. -/
theorem exists_optimal_cost_between
    {T X : Type*} [TopologicalSpace T] [CompactSpace T] [T2Space T] [PreconnectedSpace T]
    [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (F C : T × X → ℝ) (hF : Continuous F) (hC : Continuous C) (d : ℝ)
    (fibres : ∀ t : T, IsPreconnected {x : X | ∀ y : X, F (t,y) ≤ F (t,x)})
    (lo : ∃ (t : T) (x : X), (∀ y, F (t,y) ≤ F (t,x)) ∧ C (t,x) ≤ d)
    (hi : ∃ (t : T) (x : X), (∀ y, F (t,y) ≤ F (t,x)) ∧ d ≤ C (t,x)) :
    ∃ (t : T) (x : X), (∀ y, F (t,y) ≤ F (t,x)) ∧ C (t,x) = d := by
  let graph : Set (T × X) := {z | ∀ y : X, F (z.1,y) ≤ F z}
  have graph_closed : IsClosed graph := by
    change IsClosed {z : T × X | ∀ y : X, F (z.1,y) ≤ F z}
    simp only [ofPred_forall]
    exact isClosed_iInter fun y => isClosed_le
      (hF.comp (continuous_fst.prodMk (continuous_const (y := y)))) hF
  let lower := Prod.fst '' (graph ∩ {z | C z ≤ d})
  let upper := Prod.fst '' (graph ∩ {z | d ≤ C z})
  have lc : IsClosed lower :=
    ((graph_closed.inter (isClosed_le hC continuous_const)).isCompact.image continuous_fst).isClosed
  have uc : IsClosed upper :=
    ((graph_closed.inter (isClosed_le continuous_const hC)).isCompact.image continuous_fst).isClosed
  have cover : (univ : Set T) ⊆ lower ∪ upper := by
    intro t _
    obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMaxOn (univ_nonempty : (univ : Set X).Nonempty)
      ((hF.comp (continuous_const.prodMk continuous_id) : Continuous (fun y => F (t,y))).continuousOn)
    have opt : (t,x) ∈ graph := fun y => hx (mem_univ y)
    rcases le_total (C (t,x)) d with h | h
    · exact Or.inl ⟨(t,x), ⟨opt,h⟩, rfl⟩
    · exact Or.inr ⟨(t,x), ⟨opt,h⟩, rfl⟩
  obtain ⟨t₀,x₀,m₀,c₀⟩ := lo
  obtain ⟨t₁,x₁,m₁,c₁⟩ := hi
  obtain ⟨t,_,⟨⟨s,x⟩,⟨mx,cx⟩,e⟩,⟨⟨r,y⟩,⟨my,cy⟩,e'⟩⟩ :=
    isPreconnected_closed_iff.1 PreconnectedSpace.isPreconnected_univ lower upper lc uc cover
      ⟨t₀, mem_univ _, (show t₀ ∈ lower from ⟨(t₀,x₀),⟨m₀,c₀⟩,rfl⟩)⟩
      ⟨t₁, mem_univ _, (show t₁ ∈ upper from ⟨(t₁,x₁),⟨m₁,c₁⟩,rfl⟩)⟩
  change s = t at e
  change r = t at e'
  subst s
  subst r
  have cont : Continuous (fun w : X => C (t,w)) :=
    hC.comp (continuous_const.prodMk continuous_id)
  obtain ⟨w,hw,hbudget⟩ :=
    (fibres t).intermediate_value mx my cont.continuousOn (show d ∈ Icc (C (t,x)) (C (t,y)) from ⟨cx,cy⟩)
  exact ⟨t,w,hw,hbudget⟩

end BlockHierarchy.Four
