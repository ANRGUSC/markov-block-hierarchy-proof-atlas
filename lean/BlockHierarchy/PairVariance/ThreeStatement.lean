import BlockHierarchy.Three.PaperStatement
import BlockHierarchy.PairVariance.Statement

namespace BlockHierarchy.PairVariance

/-- The complete numbered theorem together with its displayed pairwise-variance formula. -/
def ThreeFullStatement : Prop := Three.ThreeSymbolStatement ∧ ThreeDisplayStatement

end BlockHierarchy.PairVariance
