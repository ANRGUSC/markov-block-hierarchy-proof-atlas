import BlockHierarchy.Four.PaperStatement
import BlockHierarchy.PairVariance.Statement

namespace BlockHierarchy.PairVariance

/-- The complete numbered theorem together with its displayed pairwise-variance formula. -/
def FourFullStatement : Prop := Four.FourSymbolStatement ∧ FourDisplayStatement

end BlockHierarchy.PairVariance
