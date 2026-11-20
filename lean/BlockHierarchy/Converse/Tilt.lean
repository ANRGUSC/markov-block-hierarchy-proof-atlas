import BlockHierarchy.Converse.Finite
import BlockHierarchy.Cut.Optimality

open scoped BigOperators
namespace BlockHierarchy.Converse
open Cut

/-- The column optimality condition bounds the exponential weight in every
distortion ball, for any distortion threshold and nonnegative multiplier. -/
theorem ball_column {X : Type*} [Fintype X] (P : X → ℝ) (d : X → X → ℕ)
    (q : X → ℝ) (D τ : ℝ) (hp : IsPrior P) (hτ : 0≤τ) (opt : Optimal P τ d q)
    (y : X) :
    (∑ x, if (d x y : ℝ)≤D then P x*Real.exp (score τ d q x-τ*D) else 0) ≤ 1 := by
  apply le_trans _ (optimal_column hp.2 opt y)
  apply Finset.sum_le_sum
  intro x _
  by_cases hd : (d x y : ℝ) ≤ D
  · rw [if_pos hd]
    have h := mul_le_mul_of_nonneg_left hd hτ
    have z := Z_pos τ d opt.1 x
    calc
      _ ≤ P x*Real.exp (score τ d q x - τ*(d x y : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (hp.1 x)
        exact Real.exp_le_exp.mpr (by linarith)
      _ = _ := by
        rw [sub_eq_add_neg,Real.exp_add,score,Real.exp_neg,Real.exp_log z]
        ring
  · rw [if_neg hd]
    exact div_nonneg (mul_nonneg (hp.1 x) (Real.exp_pos _).le) (Z_pos _ _ opt.1 _).le

theorem optimal_code_converse {X : Type*} [Fintype X] (P : X → ℝ) (d : X → X → ℕ)
    (q : X → ℝ) (D τ γ : ℝ) (hp : IsPrior P) (hτ : 0≤τ) (opt : Optimal P τ d q)
    {M : ℕ} (hM : 0<M) (enc : X → Fin M) (dec : Fin M → X) :
    (∑ x, if Real.log M + γ ≤ score τ d q x-τ*D then P x else 0) - Real.exp (-γ) ≤
      ∑ x, if D < (d x (dec (enc x)) : ℝ) then P x else 0 :=
  finite_code_converse P _ hp.1 (fun x y => (d x y : ℝ)) D γ hM enc dec
    (ball_column P d q D τ hp hτ opt)

#print axioms optimal_code_converse
end BlockHierarchy.Converse
