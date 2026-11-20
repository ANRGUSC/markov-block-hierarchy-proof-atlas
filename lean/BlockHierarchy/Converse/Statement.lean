import BlockHierarchy.VarianceLimit.Statement
import BlockHierarchy.RecurrenceStatement
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators
namespace BlockHierarchy.Converse
open Cut

/-- Operational code sizes on one uninterrupted path of n+1 symbols. -/
def feasibleSizes (p D ε : ℝ) (n : ℕ) : Set ℕ :=
  {M | 0<M ∧ ∃ (enc : Word n → Fin M) (dec : Fin M → Word n),
    (∑ x : Word n, if ((n:ℝ)+1)*D < (distance n x (dec (enc x)) : ℝ)
      then mass p n x else 0) ≤ ε}

noncomputable def operationalRate (p D ε : ℝ) (n : ℕ) :=
  Real.log (sInf (feasibleSizes p D ε n) : ℕ) / (((n:ℝ)+1)*Real.log 2)

noncomputable def gaussianTail (t : ℝ) := (gaussianReal 0 1).real (Set.Ioi t)
noncomputable def upperQuantile (ε : ℝ) := sInf {t : ℝ | gaussianTail t ≤ ε}

noncomputable def sourceDispersion (p : ℝ) :=
  p*(1-p)*(Real.log ((1-p)/p) / Real.log 2)^2

/-- Proposition 10. The eventual lower-bound formulation is the extended-real
liminf inequality, including the case of an unbounded sequence. The rate is
the operational minimum over codes and R(D) is the constrained source rate. -/
def LowDistortionConverseStatement : Prop :=
  ∀ p D ε : ℝ, 0<p → p<1/2 → 0<D → D≤Recurrence.grayD p → 0<ε → ε<1 →
    ∀ a : ℝ, a<Real.sqrt (sourceDispersion p)*upperQuantile ε →
      ∀ᶠ n : ℕ in atTop, a<Real.sqrt ((n:ℝ)+1)*
        (operationalRate p D ε n-VarianceLimit.rateBits p D)

end BlockHierarchy.Converse
