import FirstChangeStatement
import ReducedPair.Moments
import Mathlib.Analysis.Asymptotics.Defs

open scoped BigOperators Topology
open Filter Asymptotics
namespace BlockHierarchy.Varentropy

/-- Binary words of length k, with the oldest symbol first. -/
def Bits : ℕ → Type
  | 0 => Unit
  | k+1 => Bool × Bits k

instance instFintypeBits : (k : ℕ) → Fintype (Bits k)
  | 0 => inferInstanceAs (Fintype Unit)
  | k+1 =>
    letI := instFintypeBits k
    inferInstanceAs (Fintype (Bool × Bits k))

def pi (m : BinaryModel) (x : Bool) := if x then m.q else m.p
def transition (m : BinaryModel) (x y : Bool) : ℝ :=
  match x,y with
  | false,false => 1-m.a
  | false,true => m.a
  | true,false => m.b
  | true,true => 1-m.b

noncomputable def tailLaw (m : BinaryModel) (x : Bool) : (n : ℕ) → Bits n → ℝ
  | 0, _ => 1
  | n+1, ys => transition m x ys.1 * tailLaw m ys.1 n ys.2

noncomputable def pathLaw (m : BinaryModel) (n : ℕ) (ys : Bits (n+1)) :=
  pi m ys.1 * tailLaw m ys.1 n ys.2

noncomputable def B (m : BinaryModel) (x : Bool) := -logTwo (pi m x)
noncomputable def A (m : BinaryModel) (x y : Bool) := -logTwo (transition m x y)

noncomputable def edgeSum (m : BinaryModel) (x : Bool) : (n : ℕ) → Bits n → ℝ
  | 0, _ => 0
  | n+1, ys => A m x ys.1 + edgeSum m ys.1 n ys.2

noncomputable def covariance {X : Type*} [Fintype X] (P f g : X → ℝ) :=
  ∑ x, P x * (f x-mean P f) * (g x-mean P g)

noncomputable def varB (m : BinaryModel) := variance (pi m) (B m)
noncomputable def edgeVar (m : BinaryModel) :=
  variance (pathLaw m 1) (fun w => A m w.1 w.2.1)
noncomputable def gamma (m : BinaryModel) := covariance (pathLaw m 2)
  (fun w => A m w.1 w.2.1) (fun w => A m w.2.1 w.2.2.1)
noncomputable def kappa (m : BinaryModel) := covariance (pathLaw m 1)
  (fun w => B m w.1) (fun w => A m w.1 w.2.1)
noncomputable def blockVariance (m : BinaryModel) (n : ℕ) :=
  variance (pathLaw m n) (fun w => -logTwo (pathLaw m n w))
noncomputable def limitingVariance (m : BinaryModel) := edgeVar m+2*gamma m/(1-m.persistence)
noncomputable def correction (m : BinaryModel) :=
  varB m-edgeVar m+2*kappa m/(1-m.persistence)-
    2*gamma m*(1/(1-m.persistence)+1/(1-m.persistence)^2)

def hamming : (k : ℕ) → Bits k → Bits k → ℕ
  | 0, _, _ => 0
  | k+1, x, y => (if x.1=y.1 then 0 else 1)+hamming k x.2 y.2

noncomputable def normalizer {k : ℕ} (u : ℝ) (q : Bits k → ℝ) (x : Bits k) :=
  ∑ y, q y*u^hamming k x y

/-- On the backward-channel branch, pushing the reproduction prior through the
independent Bernoulli(D) errors gives the Markov source. This also describes
the lossless endpoint. The stated domain uses the paper's nonzero-rate slope
convention and omits its biased zero-rate endpoint. -/
def BackwardPoint (m : BinaryModel) (n : ℕ) (D : ℝ) (q : Bits (n+1) → ℝ) : Prop :=
  0 ≤ D ∧ D < min m.p m.q ∧ (∀ y, 0 ≤ q y) ∧ (∑ y, q y)=1 ∧
  ∀ x, normalizer (D/(1-D)) q x / (1+D/(1-D))^(n+1)=pathLaw m n x

noncomputable def tiltedVariance (m : BinaryModel) (n : ℕ) (D : ℝ) (q : Bits (n+1) → ℝ) :=
  let u := D/(1-D)
  variance (pathLaw m n) (fun x => ((n:ℝ)+1)*D*logTwo u-logTwo (normalizer u q x))

/-- Equation (varent) of arXiv:2603.07435v4. The lag index i represents h-1
for pairs of edges and h for pairs involving the initial state. -/
noncomputable def finiteFormula (m : BinaryModel) (n : ℕ) :=
  varB m + (n:ℝ)*edgeVar m +
    2*gamma m*(∑ i ∈ Finset.range (n-1), ((n:ℝ)-(i:ℝ)-1)*m.persistence^i) +
    2*kappa m*(∑ i ∈ Finset.range n, m.persistence^i)

def FiniteBlockVarentropyStatement : Prop :=
  ∀ m : BinaryModel,
    (∀ n (w : Bits (n+1)), -logTwo (pathLaw m n w)=B m w.1+edgeSum m w.1 n w.2) ∧
    (∀ n, blockVariance m n=finiteFormula m n) ∧
    (∀ n D q, BackwardPoint m n D q → tiltedVariance m n D q=blockVariance m n) ∧
    Tendsto (fun n : ℕ => blockVariance m n/((n:ℝ)+1)) atTop (𝓝 (limitingVariance m)) ∧
    (0 < |m.persistence| → |m.persistence| < 1 →
      (fun n : ℕ => blockVariance m n/((n:ℝ)+1)-limitingVariance m-correction m/((n:ℝ)+1))
        =O[atTop] (fun n : ℕ => |m.persistence|^n/((n:ℝ)+1)))

end BlockHierarchy.Varentropy
