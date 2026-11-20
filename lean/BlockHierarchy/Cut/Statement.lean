import BlockHierarchy.Varentropy.Statement

open scoped BigOperators
namespace BlockHierarchy.Cut
open Varentropy

/-- The index counts the internal transitions in a nonempty word. -/
abbrev Word (n : ℕ) := Bits (n+1)

def step (p : ℝ) (x y : Bool) := if x = y then 1-p else p

def tail (p : ℝ) (x : Bool) : (n : ℕ) → Bits n → ℝ
  | 0, _ => 1
  | n+1, ys => step p x ys.1 * tail p ys.1 n ys.2

def lastBit (x : Bool) : (n : ℕ) → Bits n → Bool
  | 0, _ => x
  | n+1, ys => lastBit ys.1 n ys.2

def last {n : ℕ} (x : Word n) := lastBit x.1 n x.2

/-- The symmetric binary Markov path starts in the uniform distribution. -/
noncomputable def mass (p : ℝ) (n : ℕ) (x : Word n) := (1/2 : ℝ) * tail p x.1 n x.2

/-- Keeping the transition between the two pieces gives their true joint law. -/
noncomputable def adjacent (p : ℝ) (i j : ℕ) (w : Word i × Word j) :=
  mass p i w.1 * step p (last w.1) w.2.1 * tail p w.2.1 j w.2.2

noncomputable def productMass (p : ℝ) (i j : ℕ) (w : Word i × Word j) :=
  mass p i w.1 * mass p j w.2

def distance (n : ℕ) : Word n → Word n → ℕ := hamming (n+1)

def jointDistance (i j : ℕ) (x y : Word i × Word j) :=
  distance i x.1 y.1 + distance j x.2 y.2

def complement : (n : ℕ) → Bits n → Bits n
  | 0, _ => ()
  | n+1, x => (!x.1, complement n x.2)

def IsPrior {X : Type*} [Fintype X] (q : X → ℝ) : Prop := (∀ y, 0 ≤ q y) ∧ (∑ y, q y) = 1

noncomputable def Z {X : Type*} [Fintype X] (τ : ℝ) (d : X → X → ℕ) (q : X → ℝ) (x : X) :=
  ∑ y, q y * Real.exp (-τ * (d x y : ℝ))

noncomputable def score {X : Type*} [Fintype X] (τ : ℝ) (d : X → X → ℕ) (q : X → ℝ) (x : X) :=
  -Real.log (Z τ d q x)

/-- Global minimization of the finite objective in (canon), measured in nats. -/
def Optimal {X : Type*} [Fintype X] (P : X → ℝ) (τ : ℝ) (d : X → X → ℕ) (q : X → ℝ) : Prop :=
  IsPrior q ∧ ∀ r, IsPrior r → mean P (score τ d q) ≤ mean P (score τ d r)

/-- Factorization of the joint expectation against all (finite-support-law) test
functions. Indicator tests give ordinary event independence. -/
def IndependentScores {i j : ℕ} (p : ℝ) (f : Word i → ℝ) (g : Word j → ℝ) : Prop :=
  ∀ a b : ℝ → ℝ, mean (adjacent p i j) (fun w => a (f w.1) * b (g w.2)) =
    mean (mass p i) (fun x => a (f x)) * mean (mass p j) (fun y => b (g y))

/-- Lemma (cut) of arXiv:2603.07435v4. The joined word is represented by its
two adjacent pieces, and joint Hamming distortion is their sum. -/
def OneCutStatement : Prop :=
  ∀ (p τ : ℝ), 0 < p → p < 1/2 → 0 ≤ τ → ∀ (i j : ℕ)
    (qL : Word i → ℝ) (qR : Word j → ℝ) (qJ : Word i × Word j → ℝ),
    Optimal (mass p i) τ (distance i) qL →
    Optimal (mass p j) τ (distance j) qR →
    Optimal (adjacent p i j) τ (jointDistance i j) qJ →
    let L := score τ (distance i) qL
    let R := score τ (distance j) qR
    let J := score τ (jointDistance i j) qJ
    IndependentScores p L R ∧
      mean (adjacent p i j) (fun w => (J w - L w.1 - R w.2)^2) ≤ 1-2*p

end BlockHierarchy.Cut
