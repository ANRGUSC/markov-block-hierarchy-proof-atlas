import BlockHierarchy.Four.Distortion
import BlockHierarchy.Four.WaterClasses
import BlockHierarchy.Four.ParityChoice

open Set
open scoped BigOperators

namespace BlockHierarchy.Four
open WaterClasses

/-- Equations (water) for one parity group. Indices start at zero. The number
of positive masses determines the support without a tie-breaking convention
for a maximizing prefix. At zero mass the first prefix attains the maximum. -/
def PaperGroup (s : ℕ → ℝ) (n : ℕ) (m c η : ℝ) : Prop :=
  let w := WaterFilling.clipped s η c
  PrefixMaximum s n m c η ∧ 0 < η ∧
  (∑ i ∈ Finset.range n, w i)=m ∧
  (∀ i < n, 0 < w i ↔ i < ((Finset.range n).filter (fun j => 0 < w j)).card) ∧
  (m=0 → η=s 0/c ∧ ∀ i < n, w i=0)

/-- One trial (u,θ). The two group totals are fixed. The active classes, the
normalizers, and global optimality among allocations on this parity slice
all concern the same six-component vector. -/
def PaperAllocation (p u θ e o : ℝ) (w : Class → ℝ) : Prop :=
  let cE := base u θ/kE u
  let cO := base u (1-θ)/(kE u/2)
  PaperGroup (evenS p) 4 θ cE e ∧ PaperGroup (oddS p) 2 (1-θ) cO o ∧
  w=join (WaterFilling.clipped (evenS p) e cE) (WaterFilling.clipped (oddS p) o cO) ∧
  w ∈ paritySlice θ ∧ oddMass w=1-θ ∧
  (∀ i, Z u w i=baseline u w i+coefficient u i*w i) ∧
  IsMaxOn (objective p u) (paritySlice θ) w

/-- Equation (G) for the optimized value, including the interior derivative
and the one-sided derivatives at both endpoints. Every endpoint or interior
root selected by the derivative rule is a global maximizer. -/
def PaperParity (p u : ℝ) (w : ℝ → Class → ℝ) (e o : ℝ → ℝ) : Prop :=
  let G := fun θ => paritySlope u (ratio p u (w θ)) (e θ) (o θ)
  let F := fun θ => objective p u (w θ)
  (∀ θ ∈ Icc (0:ℝ) 1, HasDerivWithinAt F (G θ) (Icc 0 1) θ) ∧
  (∀ θ ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, F t ≤ F θ+G θ*(t-θ)) ∧
  (∃ θ ∈ Icc (0:ℝ) 1, ParityChoice G θ) ∧
  (∀ θ ∈ Icc (0:ℝ) 1, ParityChoice G θ →
    IsMaxOn (objective p u) (stdSimplex ℝ Class) (w θ) ∧
    ∀ v ∈ stdSimplex ℝ Class, IsMaxOn (objective p u) (stdSimplex ℝ Class) v → v=w θ)

/-- Equations (fourD) and the four-symbol rate and variance at the same
achieving channel. Optimality is against every joint law on the 16 words.
The two derivatives hold the six reproduction masses fixed. -/
def PaperPoint (p D u : ℝ) (w : Class → ℝ) : Prop :=
  let z := fun x => Z u w (orbit x)
  let J := FiniteRD.joint (source p) z (prior w) distance u
  (∀ x, (∑ y, prior w y*u^distance x y)=z x) ∧
  (∀ i, HasDerivAt (fun t => baseline t w i) (baselineD u w i) u ∧
        HasDerivAt (fun t => coefficient t i) (coefficientD u i) u) ∧
  4*D=u*∑ i, sourceClasses p i*((baselineD u w i+coefficientD u i*w i)/Z u w i) ∧
  Channel.cost (fun x y => (distance x y : ℝ)) J=4*D ∧
  FiniteRD.Optimal (source p) (prior w) distance J (4*D) ∧
  Channel.info (source p) (prior w) J/Real.log 2 =
    4*D*logTwo u - ∑ i, sourceClasses p i*logTwo (Z u w i) ∧
  variance (source p) (fun x => 4*D*logTwo u-logTwo (z x))=classTiltVariance p u w

/-- A support threshold is approached on the optimal graph by active and
inactive allocations. This treats entry and exit symmetrically and allows
either direction as the multiplier increases. -/
def PaperThresholds (p : ℝ) : Prop :=
  let S : Set (ℝ × (Class → ℝ)) := {t | t.1 ∈ Ioo 0 1 ∧ t.2 ∈ stdSimplex ℝ Class ∧
    IsMaxOn (objective p t.1) (stdSimplex ℝ Class) t.2}
  ∀ i : Class, ∀ t ∈ S,
    t ∈ closure {x | x ∈ S ∧ x.2 i=0} →
    t ∈ closure {x | x ∈ S ∧ 0<x.2 i} →
    t.2 i=0 ∧ Z t.1 (ratio p t.1 t.2) i=1

/-- Theorem 4 of arXiv:2603.07435v4. The same allocation and multipliers
serve the parity optimization and the prescribed-distortion calculation. -/
def FourSymbolStatement : Prop :=
  ∀ p : ℝ, 0 < p → p < 1/2 →
    (∀ i j, i≤j → j<4 → evenS p j ≤ evenS p i) ∧
    (∀ i j, i≤j → j<2 → oddS p j ≤ oddS p i) ∧
    ∃ (w : ℝ → ℝ → Class → ℝ) (e o : ℝ → ℝ → ℝ),
      (∀ u ∈ Ioo (0:ℝ) 1, ∀ θ ∈ Icc (0:ℝ) 1,
        PaperAllocation p u θ (e u θ) (o u θ) (w u θ)) ∧
      (∀ u ∈ Ioo (0:ℝ) 1, PaperParity p u (w u) (e u) (o u)) ∧
      (∀ D ∈ Ioo (0:ℝ) (1/2), ∃ u ∈ Ioo (0:ℝ) 1, ∃ θ ∈ Icc (0:ℝ) 1,
        ParityChoice (fun t => paritySlope u (ratio p u (w u t)) (e u t) (o u t)) θ ∧
        PaperPoint p D u (w u θ)) ∧
      PaperThresholds p

end BlockHierarchy.Four
