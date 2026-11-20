import PairChannel

open scoped BigOperators

namespace BlockHierarchy.PairChannel

theorem zero_cost_marginals (P t : Word → ℝ) (L : Word → Word → ℝ)
    (hL : ∀ x y, 0 ≤ L x y) (src : ∀ x, ∑ y, L x y = P x)
    (dst : ∀ y, ∑ x, L x y = t y) (budget : jointCost L ≤ 2*0) :
    L = (fun x y => if x = y then P x else 0) ∧ t = P := by
  classical
  let J (x y : Word) := if x = y then P x else 0
  have point (x y : Word) : 0 ≤ L x y * (hamming x y : ℝ) := mul_nonneg (hL x y) (Nat.cast_nonneg _)
  have off (x y : Word) (ne : x ≠ y) : L x y = 0 := by
    have hxy : hamming x y ≠ 0 := by
      obtain ⟨i,j⟩ := x
      obtain ⟨k,l⟩ := y
      cases i <;> cases j <;> cases k <;> cases l <;> simp_all [hamming]
    have hcost : L x y*(hamming x y : ℝ) ≤ jointCost L :=
      (Finset.single_le_sum (fun j _ => point x j) (Finset.mem_univ y)).trans
      (Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => point i j)) (Finset.mem_univ x))
    have z : L x y * (hamming x y : ℝ) = 0 := le_antisymm (by linarith only [hcost,budget]) (point x y)
    exact (mul_eq_zero.mp z).resolve_right (Nat.cast_ne_zero.mpr hxy)
  have ldiag (x : Word) : L x x = P x := by
    rw [← src x, Finset.sum_eq_single x]
    · intro y _ ne
      exact off x y ne.symm
    · simp
  have same : L = J := by
    funext x y
    by_cases e : x = y
    · subst y; simpa [J] using ldiag x
    · simpa [J,e] using off x y e
  have output : t = P := by
    funext y
    rw [← dst y, same]
    simp [J]
  exact ⟨same,output⟩

theorem lossless_optimal (P : Word → ℝ) (hP : ∀ x, 0 ≤ P x) : IsOptimalAt P P 0 := by
  classical
  let J (x y : Word) := if x = y then P x else 0
  have self (x : Word) : hamming x x = 0 := by simp [hamming]
  have diagonal (x : Word) : ∑ y, J x y = P x := by simp [J]
  refine ⟨J, fun x y => by dsimp [J]; split <;> simp [hP], diagonal, ?_, ?_, ?_⟩
  · intro y
    simp [J]
  · simp [jointCost, Channel.cost, J, ite_mul, self]
  · intro t L hL src dst budget
    obtain ⟨same,output⟩ := zero_cost_marginals P t L hL src dst budget
    rw [same,output]

end BlockHierarchy.PairChannel
