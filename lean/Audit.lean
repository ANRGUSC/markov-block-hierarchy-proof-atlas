import Contracts
import FirstSupport
import PositiveThreshold

example : BlockHierarchy.TransitionZeroContract := BlockHierarchy.transition_zero
example : BlockHierarchy.PersistentConstantsContract := by
  intro A B C ρ π₀ π₁ hA hB hρ h₀ h₁ det u
  exact BlockHierarchy.persistent_constants A B C ρ π₀ π₁ u hA hB hρ h₀ h₁ det
#print axioms BlockHierarchy.transition_zero
#print axioms BlockHierarchy.persistent_constants
example : BlockHierarchy.PositiveThresholdContract := BlockHierarchy.positive_first_change
#print axioms BlockHierarchy.positive_first_change
