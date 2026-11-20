import BlockHierarchy.Varentropy.Score
import BlockHierarchy.Varentropy.Finite
import BlockHierarchy.Varentropy.Limit

namespace BlockHierarchy.Varentropy

theorem finite_formula (m : BinaryModel) (n : ℕ) : blockVariance m n = finiteFormula m n :=
  finite_from_score m (score_eq m) n

theorem finite_block_varentropy : FiniteBlockVarentropyStatement := by
  intro m
  refine ⟨score_eq m, finite_formula m, backward_variance m, ?_, ?_⟩
  · simp_rw [finite_formula]
    exact finite_limit m
  · intro _ _
    simp_rw [finite_formula]
    exact finite_remainder m

#print axioms finite_block_varentropy
end BlockHierarchy.Varentropy