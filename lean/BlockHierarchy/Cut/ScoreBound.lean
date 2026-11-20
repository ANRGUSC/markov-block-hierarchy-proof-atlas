import FiniteChannel
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow

open Set
open scoped BigOperators
namespace BlockHierarchy.Cut

theorem exp_square_bound (x : ℝ) : x^2 ≤ Real.exp x+Real.exp (-x)-2 := by
  let g (t : ℝ) := Real.exp t-Real.exp (-t)-2*t
  let f (t : ℝ) := Real.exp t+Real.exp (-t)-2-t^2
  have negexp (t : ℝ) : HasDerivAt (fun z : ℝ => Real.exp (-z)) (-Real.exp (-t)) t := by
    simpa [Function.comp_def] using ((hasDerivAt_id t).neg.exp)
  have dg (t : ℝ) : HasDerivAt g (Real.exp t+Real.exp (-t)-2) t := by
    simpa [g,Pi.sub_def,sub_neg_eq_add] using ((Real.hasDerivAt_exp t).sub (negexp t)).sub ((hasDerivAt_id t).const_mul 2)
  have df (t : ℝ) : HasDerivAt f (g t) t := by
    simpa [f,g,Pi.sub_def,Pi.add_def,sub_eq_add_neg] using (((Real.hasDerivAt_exp t).add (negexp t)).sub_const 2).sub (hasDerivAt_pow 2 t)
  have mono : Monotone g := monotone_of_deriv_nonneg (fun t => (dg t).differentiableAt) (fun t => by
    rw [(dg t).deriv]
    linarith only [Real.add_one_le_exp t,Real.add_one_le_exp (-t)])
  have on : MonotoneOn f (Ici 0) := monotoneOn_of_deriv_nonneg (convex_Ici _) 
    (fun t _ => (df t).continuousAt.continuousWithinAt)
    (fun t _ => (df t).differentiableAt.differentiableWithinAt) (fun t ht => by
      rw [(df t).deriv]
      have gt : 0≤t := interior_subset ht
      have := mono gt
      simpa [g] using this)
  have positive (t : ℝ) (ht : 0≤t) : t^2 ≤ Real.exp t+Real.exp (-t)-2 := by
    have h := on (show (0:ℝ) ∈ Ici (0:ℝ) from le_refl (0:ℝ)) (show t ∈ Ici (0:ℝ) from ht) ht
    simp [f] at h
    linarith only [h]
  rcases le_total 0 x with p|p
  · exact positive x p
  · simpa only [neg_neg,neg_sq,add_comm] using positive (-x) (neg_nonneg.mpr p)

theorem second_moment_of_column_bounds {X : Type*} [Fintype X] (P Q Δ : X → ℝ) (ρ : ℝ)
    (pp : ∀ x,0≤P x) (mass : ∑ x,P x=1) (density : ∀ x,P x≤(1+ρ)*Q x)
    (forward : (∑ x,P x*Real.exp (Δ x))≤1) (reverse : (∑ x,Q x*Real.exp (-Δ x))≤1)
    (r : 0≤ρ) : (∑ x,P x*(Δ x)^2)≤ρ := by
  have b := Finset.sum_le_sum (fun x (_ : x∈Finset.univ) =>
    mul_le_mul_of_nonneg_left (exp_square_bound (Δ x)) (pp x))
  have cmp := Finset.sum_le_sum (fun x (_ : x∈Finset.univ) =>
    mul_le_mul_of_nonneg_right (density x) (Real.exp_pos (-Δ x)).le)
  simp_rw [mul_assoc,← Finset.mul_sum] at cmp
  have rev := cmp.trans (mul_le_mul_of_nonneg_left reverse (by linarith only [r]))
  simp_rw [mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.sum_mul,mass] at b
  linarith only [b,forward,rev]

end BlockHierarchy.Cut
