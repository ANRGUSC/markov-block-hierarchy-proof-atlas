import BlockHierarchy.Three.OperatingPoint
import BlockHierarchy.Three.Inverse
import BlockHierarchy.Three.Entropy
import BlockHierarchy.Three.MiddleWeights
import BlockHierarchy.Three.FullWeights

open scoped BigOperators
namespace BlockHierarchy.Three

/-- A single Markov block, total Hamming cost, and information in bits.
The optimizing joint is compared against every joint law with the given
source marginal and distortion budget. Every optimizing marginal is identified. -/
def PaperPoint (p D u : ℝ) (q z : Word → ℝ) (R V : ℝ) : Prop :=
  let J := FiniteRD.joint (markov p) z q hamming u
  (∀ x, normalizer q u x=z x) ∧
  Channel.cost (fun x y => (hamming x y : ℝ)) J = 3*D ∧
  FiniteRD.Optimal (markov p) q hamming J (3*D) ∧
  (∀ t L, FiniteRD.Optimal (markov p) t hamming L (3*D) → t=q) ∧
  Channel.info (markov p) q J / Real.log 2 = R ∧ tilted p (3*D) u z=V

noncomputable def supportSize (q : Word → ℝ) : ℕ :=
  (Finset.univ.filter (fun y => 0 < q y)).card

/-- Theorem 3 of arXiv:2603.07435v4, from the lossless point up to, but
excluding, distortion one half. The two transition points belong to the
six- and two-word supports respectively. -/
def ThreeSymbolStatement : Prop :=
  ∀ p : ℝ, 0 < p → p < 1/2 →
    let s0 := (1-p)^2
    let s1 := 2*p*(1-p)
    let S := s0+s1
    (0 < criticalD p ∧ criticalD p < secondD p ∧ secondD p < 1/2 ∧
      0 < firstU p ∧ firstU p < secondU p ∧ secondU p < 1) ∧
    (∀ a b : ℝ, 0 ≤ a → a < b →
      middleCost p a < middleCost p b ∧ constantCost p a < constantCost p b) ∧
    (∀ D u : ℝ, 0 ≤ u →
      (3*D=middleCost p u ↔ (3*D-p^2)*(1+u)*(1+u+u^2) =
        u*(1+u+u^2)+(1-p^2)*u*(1+2*u)*(1+u)) ∧
      (3*D=constantCost p u ↔ 3*D*(1+u^3) =
        s0*3*u^3 + (1-s0)*(1+2*u)*(1-u+u^2))) ∧
    (∀ D : ℝ, 0 ≤ D → D ≤ criticalD p →
      let u := D/(1-D)
      let q := fullPrior p D
      (∀ y, 0 < q y ↔ flips y < 2 ∨ D < criticalD p) ∧
      supportSize q = (if D < criticalD p then 8 else 6) ∧
      PaperPoint p D u q (fun x => (1+u)^3*markov p x)
        (1+2*binaryEntropy p-3*binaryEntropy D) (2*nu p)) ∧
    (∀ D : ℝ, criticalD p < D → D < secondD p →
      ∃ u ∈ Set.Ioo (firstU p) (secondU p), middleCost p u=3*D ∧
        (∀ v ∈ Set.Ioo (firstU p) (secondU p), middleCost p v=3*D → v=u) ∧
        let q := sixPrior p u
        let a := s0*middleH u/S
        let b := s1*middleH u/(2*S)
        let c := beta u
        (∀ y, 0 < q y ↔ flips y < 2) ∧ supportSize q=6 ∧
        PaperPoint p D u q (classValue a b c)
          (3*D*logTwo u-classMean p (logTwo a) (logTwo b) (logTwo c))
          (classVariance p (-logTwo a) (-logTwo b) (-logTwo c))) ∧
    (∀ D : ℝ, secondD p ≤ D → D < 1/2 →
      ∃ u ∈ Set.Ico (secondU p) 1, constantCost p u=3*D ∧
        (∀ v ∈ Set.Ico (secondU p) 1, constantCost p v=3*D → v=u) ∧
        let q := prior 1 0 0
        let a := alpha u
        let b := beta u
        (∀ y, q y=(if flips y=0 then 1/2 else 0)) ∧ supportSize q=2 ∧
        PaperPoint p D u q (classValue a b b)
          (3*D*logTwo u-classMean p (logTwo a) (logTwo b) (logTwo b))
          (classVariance p (-logTwo a) (-logTwo b) (-logTwo b)) ∧
        tilted p (3*D) u (classValue a b b)=s0*(1-s0)*logTwo (a/b)^2)

end BlockHierarchy.Three
