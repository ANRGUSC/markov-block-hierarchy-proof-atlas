import FirstChange
import ReducedPair.Release
import BlockHierarchy.PairVariance.ThreeRelease
import BlockHierarchy.PairVariance.FourRelease
import BlockHierarchy.RecurrenceRelease
import BlockHierarchy.Varentropy.Release
import BlockHierarchy.Cut.Release
import BlockHierarchy.VarianceLimit.Release
import BlockHierarchy.VarianceLimit.PositiveRelease
import BlockHierarchy.Converse.Release

/-! Recheck the ten numbered paper results together. -/

example : BlockHierarchy.FirstChangeStatement := BlockHierarchy.first_change
#print axioms BlockHierarchy.first_change

example : BlockHierarchy.PersistentPairStatement := BlockHierarchy.persistent_pair
#print axioms BlockHierarchy.persistent_pair

example : BlockHierarchy.PairVariance.ThreeFullStatement := BlockHierarchy.PairVariance.three_full
#print axioms BlockHierarchy.PairVariance.three_full

example : BlockHierarchy.PairVariance.FourFullStatement := BlockHierarchy.PairVariance.four_full
#print axioms BlockHierarchy.PairVariance.four_full

example : BlockHierarchy.Recurrence.RecurrenceStatement := BlockHierarchy.Recurrence.finite_block_recurrence
#print axioms BlockHierarchy.Recurrence.finite_block_recurrence

example : BlockHierarchy.Varentropy.FiniteBlockVarentropyStatement := BlockHierarchy.Varentropy.finite_block_varentropy
#print axioms BlockHierarchy.Varentropy.finite_block_varentropy

example : BlockHierarchy.Cut.OneCutStatement := BlockHierarchy.Cut.one_cut
#print axioms BlockHierarchy.Cut.one_cut

example : BlockHierarchy.VarianceLimit.VarianceLimitStatement := BlockHierarchy.VarianceLimit.variance_limit
#print axioms BlockHierarchy.VarianceLimit.variance_limit

example : BlockHierarchy.VarianceLimit.QuantitativePositivityStatement := BlockHierarchy.VarianceLimit.quantitative_positivity
#print axioms BlockHierarchy.VarianceLimit.quantitative_positivity

example : BlockHierarchy.Converse.LowDistortionConverseStatement := BlockHierarchy.Converse.low_distortion_converse
#print axioms BlockHierarchy.Converse.low_distortion_converse
