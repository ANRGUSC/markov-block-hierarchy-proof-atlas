import ReducedPair.RateStatement

open scoped BigOperators
namespace BlockHierarchy
open PairChannel

/-- Theorem 2. The rates are minima over all joint laws and are measured in
bits per pair. Each variance is evaluated with the stated optimal marginal
and the same Hamming kernel used to construct the channel. -/
def PersistentPairStatement : Prop :=
  ∀ m : BinaryModel, 0 < m.persistence →
    let r := (1-Real.sqrt (1-4*m.C))/2
    let d₀ := min m.p m.q
    let S := m.A+m.B
    0 < r ∧ r < d₀ ∧
    (∀ D, 0 ≤ D → D ≤ r →
      let u := D/(1-D)
      let Z := fun x => (1+u)^2*m.source x
      RateAt m.source D ((-mean m.source (fun x => Real.log (m.source x))-2*binaryEntropyNats D)/Real.log 2) ∧
      GibbsPoint m.source (PairChannel.prior m.A m.B m.C u) D u Z ∧
      tiltedVariance m.source D u Z = variance m.source (fun x => -logTwo (m.source x))) ∧
    (∀ D, r ≤ D → D < d₀ →
      let δ := (D-m.C)/S
      let u := Real.sqrt (δ/(1-δ))
      RateAt m.source D (S*(binaryEntropyNats (m.B/S)-binaryEntropyNats δ)/Real.log 2) ∧
      GibbsPoint m.source (ReducedPair.prior m.A m.B u) D u (ReducedPair.Z m.A m.B u) ∧
      (∀ w, 0 < ReducedPair.prior m.A m.B u w ↔ w.1=w.2) ∧
      (∀ t J, MinimizesAt m.source t J D → t=ReducedPair.prior m.A m.B u) ∧
      tiltedVariance m.source D u (ReducedPair.Z m.A m.B u) =
        ReducedPair.classVariance m.A m.B m.C (-logTwo (m.A*(1+u^2)/S)) (-logTwo u)
          (-logTwo (m.B*(1+u^2)/S))) ∧
    (∀ D, d₀ ≤ D → RateAt m.source D 0 ∧
      GibbsPoint m.source (pointMass (majorityWord m)) D 1 (fun _ => 1) ∧
      tiltedVariance m.source D 1 (fun _ => 1) = 0) ∧
    (m.p ≠ m.q → ∀ t L, (∀ x y, 0 ≤ L x y) → (∀ x, ∑ y, L x y=m.source x) →
      (∀ y, ∑ x, L x y=t y) → jointCost L ≤ 2*d₀ → Channel.info m.source t L=0 →
      t=pointMass (majorityWord m))

end BlockHierarchy
