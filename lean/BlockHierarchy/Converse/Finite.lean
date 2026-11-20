import BlockHierarchy.Cut.Statement

open scoped BigOperators
namespace BlockHierarchy.Converse

/-- A tilt with mean exponential weight at most one on every distortion ball
gives a converse for every deterministic finite code. Thresholds are in nats. -/
theorem finite_code_converse {X Y : Type*} [Fintype X] (P J : X → ℝ) (hP : ∀ x, 0≤P x)
    (d : X → Y → ℝ) (D γ : ℝ) {M : ℕ} (hM : 0<M)
    (encoder : X → Fin M) (decoder : Fin M → Y)
    (column : ∀ y, (∑ x, if d x y ≤ D then P x * Real.exp (J x) else 0) ≤ 1) :
    (∑ x, if Real.log M + γ ≤ J x then P x else 0) -
      Real.exp (-γ) ≤ ∑ x, if D < d x (decoder (encoder x)) then P x else 0 := by
  classical
  let L := Real.log M+γ
  let A (k : Fin M) (x : X) : ℝ := if d x (decoder k) ≤ D then P x * Real.exp (J x) else 0
  have apos (k : Fin M) (x : X) : 0≤A k x := by
    dsimp [A]
    split_ifs
    · exact mul_nonneg (hP x) (Real.exp_pos _).le
    · exact le_rfl
  have point (x : X) :
      (if L ≤ J x then P x else 0) ≤
      (if D < d x (decoder (encoder x)) then P x else 0) +
      (∑ k, A k x)*Real.exp (-L) := by
    have total := Finset.sum_nonneg (s := Finset.univ) (fun k _ => apos k x)
    by_cases j : L ≤ J x
    · rw [if_pos j]
      by_cases h : D < d x (decoder (encoder x))
      · rw [if_pos h]
        linarith [mul_nonneg total (Real.exp_pos (-L)).le]
      · rw [if_neg h,zero_add]
        have one : 1 ≤ Real.exp (J x)*Real.exp (-L) := by
          rw [← Real.exp_add]
          exact Real.one_le_exp (by linarith)
        have single := Finset.single_le_sum (f := fun k => A k x)
          (fun k _ => apos k x) (Finset.mem_univ (encoder x))
        calc
          P x ≤ P x*(Real.exp (J x)*Real.exp (-L)) := le_mul_of_one_le_right (hP x) one
          _ = A (encoder x) x*Real.exp (-L) := by simp [A,le_of_not_gt h,mul_assoc]
          _ ≤ _ := mul_le_mul_of_nonneg_right single (Real.exp_pos _).le
    · rw [if_neg j]
      exact add_nonneg (by split_ifs <;> first | exact hP x | exact le_rfl)
        (mul_nonneg total (Real.exp_pos _).le)
  have all_cols : (∑ x, ∑ k, A k x) ≤ (M:ℝ) := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _k : Fin M, (1:ℝ) := Finset.sum_le_sum (fun k _ => column (decoder k))
      _ = _ := by simp
  have combine := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => point x)
  rw [Finset.sum_add_distrib,← Finset.sum_mul] at combine
  have scale : (M:ℝ)*Real.exp (-L) = Real.exp (-γ) := by
    have hm : (0:ℝ)<M := by exact_mod_cast hM
    dsimp [L]
    rw [neg_add,Real.exp_add,Real.exp_neg,Real.exp_log hm]
    field_simp
  linarith [mul_le_mul_of_nonneg_right all_cols (Real.exp_pos (-L)).le]

end BlockHierarchy.Converse
