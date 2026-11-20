import BlockHierarchy.Converse.Finite
import BlockHierarchy.VarianceLimit.Uniform

open scoped BigOperators
namespace BlockHierarchy.Converse
open Cut Varentropy

private theorem hamming_symm (n : ℕ) (x y : Bits n) :
    hamming n x y=hamming n y x := by
  induction n with
  | zero => rfl
  | succ n ih => simp [hamming,eq_comm,ih y.2 x.2]

private theorem backward_penalty {D : ℝ} (h : 0<D) (hd : D<1) :
    let τ := Real.log ((1-D)/D)
    Real.log (1+Real.exp (-τ))+τ*D=binaryEntropyNats D := by
  have dp := sub_pos.mpr hd
  dsimp
  rw [Real.exp_neg,Real.exp_log (div_pos dp h)]
  have e : 1+((1-D)/D)⁻¹=(1-D)⁻¹ := by field_simp [h.ne',dp.ne']; ring
  rw [e,Real.log_inv,Real.log_div dp.ne' h.ne']
  unfold binaryEntropyNats
  ring

/-- The size bound on Hamming balls gives the finite converse directly for
the shifted path self-information, including critical distortion. -/
theorem shifted_code_converse {p D : ℝ} (hp : 0<p) (ph : p<1)
    (hd : 0<D) (dh : D<1/2) (n : ℕ) (γ : ℝ) {M : ℕ} (hm : 0<M)
    (enc : Word n → Fin M) (dec : Fin M → Word n) :
    (∑ x : Word n, if Real.log M+γ ≤ -Real.log (mass p n x)-((n:ℝ)+1)*binaryEntropyNats D
      then mass p n x else 0)-Real.exp (-γ) ≤
    ∑ x, if ((n:ℝ)+1)*D < (distance n x (dec (enc x)) : ℝ) then mass p n x else 0 := by
  let τ := Real.log ((1-D)/D)
  let u := Real.exp (-τ)
  have ht : 0≤τ := Real.log_nonneg ((le_div_iff₀ hd).mpr (by linarith))
  have eu : 0<1+u := by dsimp [u]; positivity
  apply finite_code_converse (mass p n) _ (fun x => (mass_pos hp ph n x).le)
    (fun x y => (distance n x y:ℝ)) _ _ hm enc dec
  intro y
  have cols : (∑ x : Word n, u^(distance n x y))=(1+u)^(n+1) := by
    unfold distance
    simp_rw [hamming_symm (n+1) _ y]
    exact VarianceLimit.hamming_row u _ y
  calc
    _ ≤ ∑ x : Word n, u^(distance n x y)/(1+u)^(n+1) := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : (distance n x y:ℝ)≤((n:ℝ)+1)*D
      · rw [if_pos hx,sub_eq_add_neg,Real.exp_add,Real.exp_neg,Real.exp_log (mass_pos hp ph n x)]
        have c : binaryEntropyNats D=Real.log (1+u)+τ*D :=
          (backward_penalty hd (by linarith : D<1)).symm
        have e : -(((n:ℝ)+1)*binaryEntropyNats D) ≤
            -τ*(distance n x y:ℝ) - Real.log ((1+u)^(n+1)) := by
          rw [c,Real.log_pow,Nat.cast_succ]
          nlinarith [mul_le_mul_of_nonneg_left hx ht]
        have ex := Real.exp_le_exp.mpr e
        rw [Real.exp_sub,Real.exp_log (pow_pos eu _)] at ex
        rw [show -τ*(distance n x y:ℝ)=(distance n x y:ℝ)*(-τ) by ring,
          Real.exp_nat_mul] at ex
        calc
          _ = Real.exp (-(((n:ℝ)+1)*binaryEntropyNats D)) := by field_simp [(mass_pos hp ph n x).ne']
          _ ≤ _ := ex
      · rw [if_neg hx]
        exact div_nonneg (pow_nonneg (Real.exp_pos _).le _) (pow_pos eu _).le
    _ = 1 := by simp only [div_eq_mul_inv,← Finset.sum_mul,cols,mul_inv_cancel₀ (pow_pos eu _).ne']

#print axioms shifted_code_converse
end BlockHierarchy.Converse
