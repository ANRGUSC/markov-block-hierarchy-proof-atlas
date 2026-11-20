import BlockHierarchy.Cut.Statement
import Mathlib.Analysis.Calculus.Deriv.Basic

open Filter Topology
open scoped BigOperators
namespace BlockHierarchy.VarianceLimit
open Cut

/-- A test channel returns a probability law for each source word. -/
def IsChannel {X : Type*} [Fintype X] (W : X → X → ℝ) : Prop := ∀ x, IsPrior (W x)

noncomputable def informationNats {X : Type*} [Fintype X] (P : X → ℝ) (W : X → X → ℝ) :=
  ∑ x, ∑ y, P x * W x y * Real.log (W x y / (∑ u, P u * W u y))

noncomputable def totalDistortion {X : Type*} [Fintype X] (P : X → ℝ)
    (d : X → X → ℕ) (W : X → X → ℝ) :=
  ∑ x, ∑ y, P x * W x y * (d x y : ℝ)

/-- The paper's constrained block rate in bits per symbol. Index n means n+1 symbols. -/
noncomputable def constrainedRate (p : ℝ) (n : ℕ) (D : ℝ) :=
  sInf {r : ℝ | ∃ W : Word n → Word n → ℝ, IsChannel W ∧
    totalDistortion (mass p n) (distance n) W ≤ ((n:ℝ)+1)*D ∧
    r=informationNats (mass p n) W / (((n:ℝ)+1)*Real.log 2)}

/-- A stationary source has the limiting per-symbol rate of its finite blocks. -/
noncomputable def rateBits (p D : ℝ) := limUnder atTop (fun n : ℕ => constrainedRate p n D)

noncomputable def canonicalCost (p : ℝ) (n : ℕ) (τ : ℝ) :=
  sInf {r : ℝ | ∃ q : Word n → ℝ, IsPrior q ∧
    r = mean (mass p n) (score τ (distance n) q) / ((n:ℝ)+1)}

def MaximizingSlope (p D : ℝ) (n : ℕ) (τ : ℝ) : Prop :=
  0≤τ ∧ ∀ t, 0≤t → canonicalCost p n t-t*D ≤ canonicalCost p n τ-τ*D

noncomputable def omegaAt (p τ : ℝ) (n : ℕ) (q : Word n → ℝ) :=
  Real.sqrt (variance (mass p n) (score τ (distance n) q)) / Real.sqrt ((n:ℝ)+1)

/-- Theorem 8 in the manuscript, including positive limiting variance at
differentiability points of the operational constrained rate. -/
def VarianceLimitStatement : Prop :=
  ∀ p : ℝ, 0<p → p<1/2 → ∃ ω : ℝ → ℝ,
    ContinuousOn ω (Set.Ici 0) ∧ ω 0=0 ∧ (∀ τ, 0<τ → 0<ω τ) ∧
    (∀ τ, 0≤τ → ∀ n (q : Word n → ℝ),
      Optimal (mass p n) τ (distance n) q →
      |omegaAt p τ n q-ω τ| ≤ (1+Real.sqrt 2)*Real.sqrt ((1-2*p)/((n:ℝ)+1))) ∧
    ∀ D : ℝ, 0<D → D<1/2 →
      Tendsto (fun n : ℕ => constrainedRate p n D) atTop (𝓝 (rateBits p D)) ∧
      (∀ dR : ℝ, HasDerivAt (rateBits p) dR D →
        let τD := -(Real.log 2)*dR
        0<(ω τD)^2/(Real.log 2)^2 ∧
        (∀ n, ∃ τ, MaximizingSlope p D n τ) ∧
        ∀ (T : ℕ → ℝ) (q : (n : ℕ) → Word n → ℝ),
          (∀ n, MaximizingSlope p D n (T n)) →
          (∀ n, Optimal (mass p n) (T n) (distance n) (q n)) →
          Tendsto (fun n => (omegaAt p (T n) n (q n))^2/(Real.log 2)^2)
            atTop (𝓝 ((ω τD)^2/(Real.log 2)^2)))

end BlockHierarchy.VarianceLimit
