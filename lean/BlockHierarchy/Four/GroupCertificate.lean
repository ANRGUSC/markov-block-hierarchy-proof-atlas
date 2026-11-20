import BlockHierarchy.Four.PaperStatement

open scoped BigOperators
namespace BlockHierarchy.Four
open WaterFilling WaterClasses

theorem paper_group_of_max {s : ℕ → ℝ} {n : ℕ} {m c η : ℝ} (hn : 0<n)
    (hm : 0≤m) (hc : 0<c) (hs : ∀ i<n, 0<s i)
    (sort : ∀ i j, i≤j → j<n → s j≤s i) (maximum : PrefixMaximum s n m c η) :
    PaperGroup s n m c η := by
  obtain ⟨k,hk,hkn,ident,best,first⟩ := maximum
  subst η
  let r := WaterFilling.ratio s m c k
  let w := clipped s r c
  have pos : 0<r := positive_ratio hk hkn hm hc hs
  have empty (e : m=0) : r=s 0/c ∧ ∀ i<n, w i=0 := by
    obtain rfl := first e
    subst m
    obtain ⟨h,_,z⟩ := empty_group hn hc (hs 0 hn) (fun i hi => sort 0 i (Nat.zero_le i) hi)
    exact ⟨h,z⟩
  have total : (∑ i ∈ Finset.range n, w i)=m := by
    rcases eq_or_lt_of_le hm with zero|positive
    · rw [← zero]
      exact Finset.sum_eq_zero (fun i hi => (empty zero.symm).2 i (Finset.mem_range.mp hi))
    · exact clipped_total positive hc hk hkn hs sort best
  refine ⟨⟨k,hk,hkn,rfl,best,first⟩,pos,total,?_,empty⟩
  have cutoff : ∃ j, j≤n ∧ ∀ i<n, 0<w i ↔ i<j := by
    rcases eq_or_lt_of_le hm with zero|positive
    · exact ⟨0,Nat.zero_le _,fun i hi => by rw [(empty zero.symm).2 i hi]; simp⟩
    · obtain ⟨_,j,_,hjn,_,active⟩ := clipped_mass_determines_prefix s n m c r hn positive hc pos hs sort total
      exact ⟨j,hjn,active⟩
  obtain ⟨j,hjn,active⟩ := cutoff
  have filter_eq : (Finset.range n).filter (fun i => 0<w i)=Finset.range j := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_range]
    exact ⟨fun h => (active i h.1).mp h.2,fun h => ⟨h.trans_le hjn,(active i (h.trans_le hjn)).mpr h⟩⟩
  intro i hi
  change 0<w i ↔ i < ((Finset.range n).filter (fun i => 0<w i)).card
  rw [filter_eq,Finset.card_range]
  exact active i hi

#print axioms paper_group_of_max
end BlockHierarchy.Four
