import ChannelOptimizer
import PairPrior
import Mathlib.Tactic.LinearCombination

open scoped BigOperators

namespace BlockHierarchy.PairChannel

abbrev Word := Bool × Bool

def law (A B C : ℝ) : Word → ℝ
  | (false,false) => A
  | (true,true) => B
  | _ => C

def hamming (x y : Word) : ℕ :=
  (if x.1 = y.1 then 0 else 1) + (if x.2 = y.2 then 0 else 1)

noncomputable def backward (u : ℝ) (x y : Word) : ℝ := u^hamming x y/(1+u)^2

noncomputable def prior (A B C u : ℝ) : Word → ℝ :=
  law ((A-2*C*u+B*u^2)/(1-u)^2) ((B-2*C*u+A*u^2)/(1-u)^2)
      ((C*(1+u^2)-(A+B)*u)/(1-u)^2)

theorem word_sum (f : Word → ℝ) : ∑ x, f x =
    f (false,false) + f (false,true) + f (true,false) + f (true,true) := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  ring

theorem prior_total (A B C u : ℝ) (hu : u < 1) (mass : A+2*C+B=1) :
    ∑ y, prior A B C u y = 1 := by
  rw [word_sum]
  simp only [prior,law]
  field_simp [(sub_pos.mpr hu).ne']
  linear_combination (1-u)^2 * mass

theorem inverse (A B C u : ℝ) (h0 : 0 ≤ u) (h1 : u < 1) (x : Word) :
    ∑ y, prior A B C u y * backward u x y = law A B C x := by
  have plus : 1+u ≠ 0 := by linarith
  have minus := (sub_pos.mpr h1).ne'
  rw [word_sum]
  obtain ⟨a,b⟩ := x
  cases a <;> cases b <;> norm_num [prior,backward,law,hamming] <;>
    field_simp [plus,minus] <;> ring

theorem column_sum (u : ℝ) (h0 : 0 ≤ u) (y : Word) : ∑ x, backward u x y = 1 := by
  have plus : 1+u ≠ 0 := by linarith
  rw [word_sum]
  obtain ⟨a,b⟩ := y
  cases a <;> cases b <;> norm_num [backward,hamming] <;> field_simp [plus] <;> ring

theorem column_cost (u : ℝ) (h0 : 0 ≤ u) (y : Word) :
    ∑ x, backward u x y * (hamming x y : ℝ) = 2*u/(1+u) := by
  have plus : 1+u ≠ 0 := by linarith
  rw [word_sum]
  obtain ⟨a,b⟩ := y
  cases a <;> cases b <;> norm_num [backward,hamming] <;> field_simp [plus] <;> ring

theorem joint_cost (u : ℝ) (hu : 0 ≤ u) (q : Word → ℝ) (mass : ∑ y, q y = 1) :
    Channel.cost (fun x y => (hamming x y : ℝ)) (fun x y => q y * backward u x y) =
      2*u/(1+u) := by
  unfold Channel.cost
  rw [Finset.sum_comm]
  simp only [mul_assoc, ← Finset.mul_sum, column_cost u hu, ← Finset.sum_mul, mass, one_mul]

def jointCost := Channel.cost (fun x y : Word => (hamming x y : ℝ))

/-- A reproduction law with a feasible realizing joint, compared directly with
the mutual information of every admissible competing joint at budget 2D. -/
def IsOptimalAt (P q : Word → ℝ) (D : ℝ) : Prop :=
  ∃ J : Word → Word → ℝ, (∀ x y, 0 ≤ J x y) ∧ (∀ x, ∑ y, J x y = P x) ∧
    (∀ y, ∑ x, J x y = q y) ∧ jointCost J = 2*D ∧
    ∀ (t : Word → ℝ) (L : Word → Word → ℝ), (∀ x y, 0 ≤ L x y) →
      (∀ x, ∑ y, L x y = P x) → (∀ y, ∑ x, L x y = t y) → jointCost L ≤ 2*D →
      Channel.info P q J ≤ Channel.info P t L

theorem optimal_prior (A B C D : ℝ) (mass : A+2*C+B=1) (hD : 0 < D) (half : D < 1/2)
    (feasible : ∀ y, 0 ≤ prior A B C (D/(1-D)) y) :
    IsOptimalAt (law A B C) (prior A B C (D/(1-D))) D := by
  let u := D/(1-D)
  let q := prior A B C u
  have hd : 0 < 1-D := by linarith
  have hu : 0 < u := div_pos hD hd
  have hu1 : u < 1 := (div_lt_iff₀ hd).mpr (by linarith)
  have hp : 0 < 1+u := by linarith
  have hcost : 2*u/(1+u) = 2*D := by
    apply (div_eq_iff hp.ne').mpr
    have h : u*(1-D)=D := div_mul_cancel₀ _ hd.ne'
    nlinarith only [h]
  have hK (x y : Word) : 0 < backward u x y := div_pos (pow_pos hu _) (sq_pos_of_pos hp)
  have ker (x y : Word) : Real.log (backward u x y) =
      Real.log u * (hamming x y : ℝ) - 2*Real.log (1+u) := by
    rw [backward, Real.log_div (pow_pos hu _).ne' (sq_pos_of_pos hp).ne',
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have sumP : ∑ x, law A B C x = 1 := by rw [word_sum]; change A+C+C+B=1; linarith
  have rows := inverse A B C u hu.le hu1
  have cols := column_sum u hu.le
  have total := prior_total A B C u hu1 mass
  have attained := (joint_cost u hu.le q total).trans hcost
  refine ⟨fun x y => q y*backward u x y, fun x y => mul_nonneg (feasible y) (hK x y).le,
    rows, ?_, attained, ?_⟩
  · intro y
    rw [← Finset.mul_sum, cols, mul_one]
  · intro t L hL src dst budget
    exact Channel.backward_optimal _ q t _ L _ _ _ (Real.log_nonpos hu.le hu1.le)
      hK hL rows sumP cols ker src dst (budget.trans_eq attained.symm)

end BlockHierarchy.PairChannel
