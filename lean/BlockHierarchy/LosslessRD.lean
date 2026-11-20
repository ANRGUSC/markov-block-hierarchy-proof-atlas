import BlockHierarchy.FiniteRD

open scoped BigOperators
namespace BlockHierarchy.FiniteRD

theorem lossless {X : Type*} [Fintype X] [Nonempty X] [DecidableEq X] {P : X → ℝ}
    {d : X → X → ℕ} (hP : ∀ x, 0 ≤ P x) (metric : ∀ x y, d x y=0 ↔ x=y) :
    let J := fun x y => if x=y then P x else 0
    Optimal P P d J 0 ∧ Channel.info P P J/Real.log 2= -mean P (fun x => logTwo (P x)) := by
  classical
  let J (x y : X) := if x=y then P x else 0
  have self (x : X) : d x x=0 := (metric x x).mpr rfl
  constructor
  · refine ⟨fun x y => by dsimp; split <;> simp [hP],fun x => by simp,fun y => by simp,?_,?_⟩
    · simp [Channel.cost,ite_mul,self]
    · intro t L hL src dst budget
      have point (x y) : 0 ≤ L x y*(d x y : ℝ) := mul_nonneg (hL x y) (Nat.cast_nonneg _)
      have off (x y) (ne : x ≠ y) : L x y=0 := by
        have bound : L x y*(d x y : ℝ) ≤ Channel.cost (fun x y => (d x y : ℝ)) L :=
          (Finset.single_le_sum (fun j _ => point x j) (Finset.mem_univ y)).trans
          (Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => point i j)) (Finset.mem_univ x))
        exact (mul_eq_zero.mp (le_antisymm (bound.trans budget) (point x y))).resolve_right
          (Nat.cast_ne_zero.mpr (fun h => ne ((metric x y).mp h)))
      have same : L=J := by
        funext x y
        by_cases e : x=y
        · subst y
          simp only [J,if_true]
          rw [← src x, Finset.sum_eq_single x]
          · intro y _ ne; exact off x y ne.symm
          · simp
        · simpa [J,e] using off x y e
      have out : t=P := by funext y; rw [← dst y,same]; simp [J]
      rw [same,out]
  · have info : Channel.info P P J = -mean P (fun x => Real.log (P x)) := by
      unfold Channel.info mean
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_eq_single x]
      · simp [J]
      · intro y _ h; simp [J,Ne.symm h]
      · simp
    change Channel.info P P J / Real.log 2=_
    rw [info]
    simp only [mean,logTwo,div_eq_mul_inv,neg_mul,Finset.sum_mul,mul_assoc]

end BlockHierarchy.FiniteRD
