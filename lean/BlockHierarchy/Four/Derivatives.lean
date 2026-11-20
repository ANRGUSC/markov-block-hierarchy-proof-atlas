import FiniteChannel
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open scoped BigOperators
namespace BlockHierarchy.Four

theorem affine_class_derivative : ∀ {ι : Type} [Fintype ι] (s w : ι → ℝ) (L k : ι → ℝ → ℝ) (l' k' : ι → ℝ) (u : ℝ),
  (∀ i, HasDerivAt (L i) (l' i) u) → (∀ i, HasDerivAt (k i) (k' i) u) →
  (∀ i, 0 < L i u+k i u*w i) →
  HasDerivAt (fun t => ∑ i, s i*Real.log (L i t+k i t*w i))
    (∑ i, s i*((l' i+k' i*w i)/(L i u+k i u*w i))) u := by
  intro ι _ s w L k l' k' u hL hk hz
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.const_mul
  exact ((hL i).add ((hk i).mul_const (w i))).log (hz i).ne'

theorem distortion_log_derivative : ∀ {ι : Type} [Fintype ι] (q : ι → ℝ) (d : ι → ℕ) (u : ℝ), 0 < u →
  0 < ∑ i, q i*u^(d i) →
  HasDerivAt (fun t : ℝ => Real.log (∑ i, q i*t^(d i)))
    ((∑ i, q i*u^(d i)*(d i : ℝ))/(u*(∑ i, q i*u^(d i)))) u := by
  intro ι inst q d u hu hz
  have deriv (i : ι) : HasDerivAt (fun t : ℝ => q i*t^(d i))
      (q i*((d i : ℝ)*u^(d i-1))) u :=
    (hasDerivAt_pow (d i) u).const_mul (q i)
  have D := (HasDerivAt.fun_sum fun i (_ : i ∈ Finset.univ) => deriv i).log hz.ne'
  have term (i : ι) : q i*((d i : ℝ)*u^(d i-1))*u=q i*u^(d i)*(d i : ℝ) := by
    cases h : d i with
    | zero => simp
    | succ n => simp only [Nat.succ_sub_one,pow_succ]; ring
  have e : (∑ i, q i*((d i : ℝ)*u^(d i-1)))*u=∑ i, q i*u^(d i)*(d i : ℝ) := by
    rw [Finset.sum_mul]; simp_rw [term]
  rw [← e]
  convert D using 1
  field_simp [hu.ne',hz.ne']
  <;> ring

theorem interior_transfer_stationary : ∀ (F : ℝ → ℝ) (θ g : ℝ), 0 < θ → θ < 1 → HasDerivAt F g θ →
  (∀ t ∈ Set.Icc (0:ℝ) 1, F t ≤ F θ) → g=0 := by
  intro F θ g hθ h1 hF hmax
  have localMax : IsLocalMax F θ :=
    Filter.mem_of_superset (Icc_mem_nhds hθ h1) (fun t ht => hmax t ht)
  exact localMax.hasDerivAt_eq_zero hF

end BlockHierarchy.Four
