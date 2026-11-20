import BlockHierarchy.Cut.ColumnAverage
import BlockHierarchy.Cut.Flips
import BlockHierarchy.Cut.Optimality

open scoped BigOperators
namespace BlockHierarchy.Cut

def trialPrior {i j : ℕ} (qL : Word i → ℝ) (qR : Word j → ℝ) (w : Word i × Word j) :=
  qL w.1 * qR w.2

theorem trial_isPrior {i j : ℕ} {qL : Word i → ℝ} {qR : Word j → ℝ}
    (hL : IsPrior qL) (hR : IsPrior qR) : IsPrior (trialPrior qL qR) := by
  refine ⟨fun w => mul_nonneg (hL.1 w.1) (hR.1 w.2), ?_⟩
  simp only [trialPrior,Fintype.sum_prod_type,← Finset.mul_sum,hR.2,mul_one,hL.2]

private theorem joint_exp {i j : ℕ} (τ : ℝ) (x y : Word i × Word j) :
    Real.exp (-τ*(jointDistance i j x y : ℝ)) =
      Real.exp (-τ*(distance i x.1 y.1 : ℝ)) * Real.exp (-τ*(distance j x.2 y.2 : ℝ)) := by
  rw [jointDistance,Nat.cast_add,mul_add,Real.exp_add]

theorem trial_Z {i j : ℕ} (τ : ℝ) (qL : Word i → ℝ) (qR : Word j → ℝ) (w : Word i × Word j) :
    Z τ (jointDistance i j) (trialPrior qL qR) w=
      Z τ (distance i) qL w.1 * Z τ (distance j) qR w.2 := by
  unfold Z
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [joint_exp]
  unfold trialPrior
  ring

theorem trial_column {p τ : ℝ} {i j : ℕ} {qL : Word i → ℝ} {qR : Word j → ℝ}
    (hp : 0<p) (ph : p<1/2) (optL : Optimal (mass p i) τ (distance i) qL)
    (optR : Optimal (mass p j) τ (distance j) qR) (y : Word i × Word j) :
    (∑ w, productMass p i j w * Real.exp (-τ*(jointDistance i j w y : ℝ)) /
      Z τ (jointDistance i j) (trialPrior qL qR) w) ≤ 1 := by
  have ph' : p<1 := by linarith
  let col (n : ℕ) (q : Word n → ℝ) (z x : Word n) :=
    mass p n x * Real.exp (-τ*(distance n x z : ℝ))/Z τ (distance n) q x
  have nonneg (n : ℕ) (q : Word n → ℝ) (hq : IsPrior q) (z : Word n) :
      0 ≤ ∑ x, col n q z x := by
    apply Finset.sum_nonneg
    intro x _
    exact div_nonneg (mul_nonneg (mass_pos hp ph' n x).le (Real.exp_pos _).le) (Z_pos _ _ hq x).le
  have term (w : Word i × Word j) :
      productMass p i j w * Real.exp (-τ*(jointDistance i j w y : ℝ)) /
        Z τ (jointDistance i j) (trialPrior qL qR) w =
      col i qL y.1 w.1 * col j qR y.2 w.2 := by
    rw [joint_exp,trial_Z]
    unfold col productMass
    ring
  simp_rw [term]
  exact product_columns _ _ (nonneg i qL optL.1 _) (nonneg j qR optR.1 _)
    (optimal_column (mass_sum hp ph' i) optL y.1) (optimal_column (mass_sum hp ph' j) optR y.2)

#print axioms trial_column
end BlockHierarchy.Cut