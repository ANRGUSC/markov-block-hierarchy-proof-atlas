import FiniteChannel
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace BlockHierarchy.Three

abbrev Word := Bool × Bool × Bool

def flips (x : Word) : ℕ :=
  (if x.1 = x.2.1 then 0 else 1) + (if x.2.1 = x.2.2 then 0 else 1)

def hamming (x y : Word) : ℕ :=
  (if x.1 = y.1 then 0 else 1) + (if x.2.1 = y.2.1 then 0 else 1) +
  (if x.2.2 = y.2.2 then 0 else 1)

/-- A value per word, indexed by the number of adjacent flips. -/
def classValue (a b c : ℝ) (x : Word) : ℝ :=
  if x.1 = x.2.1 then (if x.2.1 = x.2.2 then a else b)
  else (if x.2.1 = x.2.2 then b else c)

def step (p : ℝ) (a b : Bool) := if a = b then 1-p else p

noncomputable def markov (p : ℝ) (x : Word) : ℝ :=
  (1/2) * step p x.1 x.2.1 * step p x.2.1 x.2.2

theorem markov_classes (p : ℝ) (x : Word) :
    markov p x = classValue ((1-p)^2/2) (p*(1-p)/2) (p^2/2) x := by
  obtain ⟨a,b,c⟩ := x
  cases a <;> cases b <;> cases c <;> norm_num [markov,step,classValue] <;> ring

theorem word_sum (f : Word → ℝ) : ∑ x, f x =
    f (false,false,false) + f (false,false,true) + f (false,true,false) +
    f (false,true,true) + f (true,false,false) + f (true,false,true) +
    f (true,true,false) + f (true,true,true) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  ring

theorem class_expectation (p a b c : ℝ) :
    ∑ x, markov p x * classValue a b c x =
      (1-p)^2*a + 2*p*(1-p)*b + p^2*c := by
  rw [word_sum]
  norm_num [markov,step,classValue]
  ring

noncomputable def prior (w0 w1 w2 : ℝ) := classValue (w0/2) (w1/4) (w2/2)

theorem prior_total (w0 w1 w2 : ℝ) : ∑ y, prior w0 w1 w2 y = w0+w1+w2 := by
  rw [word_sum]
  norm_num [prior,classValue]
  ring

noncomputable def alpha (u : ℝ) := (1+u^3)/2
noncomputable def beta (u : ℝ) := (u+u^2)/2

noncomputable def normalizer (q : Word → ℝ) (u : ℝ) (x : Word) : ℝ :=
  ∑ y, q y * u^(hamming x y)

theorem class_normalizer (w0 w1 w2 u : ℝ) (x : Word) :
    normalizer (prior w0 w1 w2) u x =
      beta u*(w0+w1+w2) + (alpha u-beta u)*classValue w0 (w1/2) w2 x := by
  unfold normalizer
  rw [word_sum]
  obtain ⟨a,b,c⟩ := x
  cases a <;> cases b <;> cases c <;>
    norm_num [prior,classValue,hamming,alpha,beta] <;> ring

theorem hamming_comm (x y : Word) : hamming x y = hamming y x := by
  simp only [hamming, eq_comm]

/-- The same complementary-pair calculation supplies every dual column. -/
theorem class_column (a b c u : ℝ) (y : Word) :
    ∑ x, prior a b c x * u^(hamming x y) =
      beta u*(a+b+c) + (alpha u-beta u)*classValue a (b/2) c y := by
  simpa only [normalizer, hamming_comm y] using class_normalizer a b c u y

end BlockHierarchy.Three

