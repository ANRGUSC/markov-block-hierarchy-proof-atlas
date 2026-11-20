import BlockHierarchy.Cut.Product
import BlockHierarchy.Cut.Compare

namespace BlockHierarchy.Cut

theorem trial_score {i j : ℕ} (τ : ℝ) {qL : Word i → ℝ} {qR : Word j → ℝ}
    (hL : IsPrior qL) (hR : IsPrior qR) (w : Word i × Word j) :
    score τ (jointDistance i j) (trialPrior qL qR) w =
      score τ (distance i) qL w.1 + score τ (distance j) qR w.2 := by
  unfold score
  rw [trial_Z,Real.log_mul (Z_pos _ _ hL _).ne' (Z_pos _ _ hR _).ne',neg_add]

theorem one_cut : OneCutStatement := by
  intro p τ hp ph _ i j qL qR qJ optL optR optJ
  have h1 : p<1 := by linarith
  refine ⟨optimal_independent hp h1 qL optR,?_⟩
  have joint : IsPrior (adjacent p i j) :=
    ⟨fun w => (adjacent_pos hp h1 i j w).le,adjacent_sum hp h1 i j⟩
  have density (w : Word i × Word j) :
      adjacent p i j w ≤ (1+(1-2*p))*productMass p i j w := by
    rw [show 1+(1-2*p)=2*(1-p) by ring]
    exact adjacent_le_product hp ph i j w
  have prior := trial_isPrior optL.1 optR.1
  have bound := compare_normalizers (adjacent p i j) (productMass p i j) τ (jointDistance i j)
    qJ (trialPrior qL qR) (1-2*p) (by linarith) joint optJ.1 prior density
    (Z_pos _ _ optJ.1) (Z_pos _ _ prior) (optimal_column joint.2 optJ) (trial_column hp ph optL optR)
  simpa only [trial_score _ optL.1 optR.1,sub_add_eq_sub_sub] using bound

#print axioms one_cut
end BlockHierarchy.Cut