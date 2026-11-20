import FirstChangeStatement
import ReducedPair.Moments

open scoped BigOperators
namespace BlockHierarchy
open PairChannel

def pointMass (w : Word) (y : Word) : ℝ := if y=w then 1 else 0

noncomputable def majorityWord (m : BinaryModel) : Word := if m.q ≤ m.p then (false,false) else (true,true)

/-- Achievability and the matching converse against arbitrary joint laws.
The budget in this definition need not be saturated at zero rate. -/
def MinimizesAt (P q : Word → ℝ) (J : Word → Word → ℝ) (D : ℝ) : Prop :=
  (∀ x y, 0 ≤ J x y) ∧ (∀ x, ∑ y, J x y = P x) ∧ (∀ y, ∑ x, J x y = q y) ∧
    jointCost J ≤ 2*D ∧ ∀ t L, (∀ x y, 0 ≤ L x y) → (∀ x, ∑ y, L x y = P x) →
      (∀ y, ∑ x, L x y = t y) → jointCost L ≤ 2*D → Channel.info P q J ≤ Channel.info P t L

def RateAt (P : Word → ℝ) (D bits : ℝ) : Prop :=
  ∃ q J, MinimizesAt P q J D ∧ Channel.info P q J / Real.log 2 = bits

/-- At an interior operating point, all active columns realize the selected
Gibbs channel. The normalizer and tilt use this same marginal and multiplier. -/
def GibbsPoint (P q : Word → ℝ) (D u : ℝ) (Z : Word → ℝ) : Prop :=
  (∀ x, Z x = ∑ y, q y*u^hamming x y) ∧
    MinimizesAt P q (fun x y => q y*(P x*u^hamming x y/Z x)) D

noncomputable def tiltedVariance (P : Word → ℝ) (D u : ℝ) (Z : Word → ℝ) :=
  variance P (fun x => 2*D*logTwo u-logTwo (Z x))

end BlockHierarchy
