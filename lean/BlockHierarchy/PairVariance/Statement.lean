import BlockHierarchy.Three.OperatingPoint
import BlockHierarchy.Four.Channel

open scoped BigOperators
namespace BlockHierarchy.PairVariance

/-- Equation (pairvar) in arXiv:2603.07435v4. Each unordered pair of distinct
classes occurs once, with the square of its log-ratio in bits. -/
noncomputable def pairSum {I : Type*} [Fintype I] [LinearOrder I]
    (s Z : I → ℝ) := ∑ i, ∑ j ∈ Finset.univ.filter (i < ·), s i*s j*(logTwo (Z i/Z j))^2

noncomputable def threeWeights (p : ℝ) : Fin 3 → ℝ := ![(1-p)^2,2*p*(1-p),p^2]

def ThreeDisplayStatement : Prop :=
  ∀ (p D u : ℝ) (Z : Fin 3 → ℝ), (∀ i, 0 < Z i) →
    Three.tilted p (3*D) u (Three.classValue (Z 0) (Z 1) (Z 2))=pairSum (threeWeights p) Z

def FourDisplayStatement : Prop :=
  ∀ (p D u : ℝ) (w : Four.Class → ℝ), 0<u → (∀ i, 0≤w i) → (∑ i, w i)=1 →
    variance (Four.source p) (fun x => 4*D*logTwo u-logTwo (Four.Z u w (Four.orbit x))) =
      pairSum (Four.sourceClasses p) (Four.Z u w)

def ThreeFourDisplayStatement : Prop := ThreeDisplayStatement ∧ FourDisplayStatement

end BlockHierarchy.PairVariance
