import BlockHierarchy.RecurrenceExtrema

open scoped BigOperators Topology
namespace BlockHierarchy.Recurrence

/-- Sum over all binary words of a specified length, in chronological order. -/
def wordSum : ℕ → (List Bool → ℝ) → ℝ
  | 0, f => f []
  | n+1, f => ∑ b : Bool, wordSum n (fun xs => f (b::xs))

/-- Finite Markov expectation starting at a specified spin. The first argument of the
observable records the visited word; the second is the next spin after that word. -/
noncomputable def expectFrom (p : ℝ) (a : Bool) : ℕ → (List Bool → Bool → ℝ) → ℝ
  | 0, f => f [] a
  | n+1, f => ∑ b : Bool, Three.step p a b * expectFrom p b n (fun xs t => f (a::xs) t)

noncomputable def markovExpect (p : ℝ) (n : ℕ) (f : List Bool → Bool → ℝ) :=
  (∑ a : Bool, expectFrom p a n f)/2

noncomputable def pathLaw (p : ℝ) (x : List Bool) :=
  markovExpect p x.length (fun xs _ => if xs=x then 1 else 0)

noncomputable def invWeight (z : ℝ) (x y : Bool) := (1+spin x*spin y/z)/2
noncomputable def backWeight (D : ℝ) (x y : Bool) := if x=y then 1-D else D

/-- Tensor product of bitwise factors on equally long words. -/
noncomputable def wordWeight (f : Bool → Bool → ℝ) : List Bool → List Bool → ℝ
  | [], [] => 1
  | x::xs, y::ys => f x y * wordWeight f xs ys
  | _, _ => 0

noncomputable def mass (p z : ℝ) (ys : List Bool) :=
  markovExpect p ys.length (fun xs _ => wordWeight (invWeight z) xs ys)

noncomputable def firstMoment (p z : ℝ) (ys : List Bool) :=
  markovExpect p ys.length (fun xs t => spin t * wordWeight (invWeight z) xs ys)

noncomputable def moment (p z : ℝ) (ys : List Bool) := firstMoment p z ys / mass p z ys

def InverseNonnegative (p z : ℝ) (K : ℕ) : Prop :=
  ∀ y : List Bool, y.length=K → 0 ≤ mass p z y

/-- A genuine reproduction probability law pushed through K independent backward
Bernoulli(D) channels has exactly the given K-symbol Markov source marginal. -/
def BackwardFeasible (p D : ℝ) (K : ℕ) : Prop :=
  ∃ q : List Bool → ℝ, (∀ y, y.length=K → 0 ≤ q y) ∧ wordSum K q=1 ∧
    ∀ x, x.length=K → wordSum K (fun y => q y*wordWeight (backWeight D) x y)=pathLaw p x

/-- Index n corresponds to the paper's H_(n+1). -/
def MaximumAt (p z : ℝ) (n : ℕ) (H : ℝ) : Prop :=
  IsGreatest {h | ∃ y : List Bool, y.length=n ∧ 0 < mass p z y ∧ h=|moment p z y|} H

noncomputable def grayD (p : ℝ) :=
  let ρ := 1-2*p
  (1-2*Real.sqrt ρ/(1+ρ))/2

/-- Proposition 5, with a common sequence of upper endpoints for all finite lengths.
The K=1 endpoint is allowed at 1/2. The source and inverse-channel expectations use
the stationary symmetric Markov law on actual binary words. -/
def RecurrenceStatement : Prop :=
  ∀ p : ℝ, 0 < p → p < 1/2 →
    let ρ := 1-2*p
    (∀ D : ℝ, 0 < D → D < 1/2 →
      let z := 1-2*D
      ∃ H : ℕ → ℝ, (∀ n, MaximumAt p z n (H n)) ∧ H 0=0 ∧
        (∀ n, (∀ j ≤ n, H j < z) → H (n+1)=peak ρ z (H n)) ∧
        (∀ n, BackwardFeasible p D (n+1) ↔ InverseNonnegative p z (n+1)) ∧
        (∀ n, BackwardFeasible p D (n+1) ↔ (∀ j<n, H j < z) ∧ H n ≤ z)) ∧
    grayD p=(1-Real.sqrt (1-(p/(1-p))^2))/2 ∧
    ∃ d : ℕ → ℝ, (∀ n, 0 ≤ d n ∧ d n ≤ 1/2) ∧ Antitone d ∧
      (∀ n D, 0 < D → D < 1/2 → (BackwardFeasible p D (n+1) ↔ D ≤ d n)) ∧
      Filter.Tendsto d Filter.atTop (nhds (grayD p))

end BlockHierarchy.Recurrence
