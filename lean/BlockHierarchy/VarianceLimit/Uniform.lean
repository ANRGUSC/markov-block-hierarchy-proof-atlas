import BlockHierarchy.VarianceLimit.Redundancy
import BlockHierarchy.VarianceLimit.PositiveStatement

open scoped BigOperators
namespace BlockHierarchy.VarianceLimit
open Cut Varentropy

theorem hamming_row (u : ℝ) (n : ℕ) (x : Bits n) :
    (∑ y : Bits n, u^(hamming n x y)) = (1+u)^n := by
  induction n with
  | zero => simp [hamming,show Fintype.card (Bits 0)=1 from rfl]
  | succ n ih =>
    obtain ⟨b,x⟩ := x
    rw [sum_next]
    cases b <;> simp [hamming,pow_add,← Finset.mul_sum,ih,pow_succ] <;> ring

private theorem word_card : ∀ n, Fintype.card (Bits n)=2^n
  | 0 => rfl
  | n+1 => by
    change Fintype.card (Bool × Bits n)=_
    rw [Fintype.card_prod,word_card]
    simp [pow_succ,Nat.mul_comm]

private theorem uniform_Z (τ : ℝ) (n : ℕ) (x : Word n) :
    Z τ (distance n) (fun _ => (1/2:ℝ)^(n+1)) x =
      ((1+Real.exp (-τ))/2)^(n+1) := by
  have e (y : Word n) : Real.exp (-τ*(distance n x y:ℝ))=Real.exp (-τ)^(distance n x y) := by
    rw [mul_comm,Real.exp_nat_mul]
  unfold Z
  simp_rw [e]
  rw [← Finset.mul_sum]
  change (1/2:ℝ)^(n+1)*(∑ y, Real.exp (-τ)^hamming (n+1) x y) = _
  rw [hamming_row,← mul_pow]
  congr 1
  ring

/-- The uniform reproduction prior works at every physical block length,
independently of the source correlations. -/
theorem totalCost_uniform {p : ℝ} (hp : 0<p) (ph : p<1/2) (τ : ℝ) (k : ℕ) :
    totalCost p τ k ≤ (k:ℝ)*(τ/2-Real.log (Real.cosh (τ/2))) := by
  cases k with
  | zero => simp [totalCost]
  | succ n =>
    let U : Word n → ℝ := fun _ => (1/2:ℝ)^(n+1)
    have prior : IsPrior U := by
      refine ⟨fun _ => by dsimp [U]; positivity,?_⟩
      simp only [U,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      change (Fintype.card (Bits (n+1)):ℝ)*(1/2:ℝ)^(n+1)=1
      rw [word_card,Nat.cast_pow,Nat.cast_ofNat,← mul_pow]
      norm_num
    have h1 : p<1 := by linarith
    have eqn : (1+Real.exp (-τ))/2 = Real.exp (-(τ/2))*Real.cosh (τ/2) := by
      rw [Real.cosh_eq]
      have e : Real.exp (-(τ/2))*Real.exp (τ/2)=1 := by rw [← Real.exp_add]; simp
      have g : Real.exp (-(τ/2))*Real.exp (-(τ/2))=Real.exp (-τ) := by
        rw [← Real.exp_add]; congr 1; ring
      linarith
    have sc (x : Word n) : score τ (distance n) U x =
        ((n:ℝ)+1)*(τ/2-Real.log (Real.cosh (τ/2))) := by
      unfold score U
      rw [uniform_Z,Real.log_pow,eqn,Real.log_mul (Real.exp_pos _).ne' (Real.cosh_pos _).ne',Real.log_exp]
      push_cast
      ring
    have opt := (canonical_optimal p τ n).2 U prior
    change mean (mass p n) (blockScore p τ n) ≤ _
    apply opt.trans
    unfold mean
    simp_rw [sc]
    rw [← Finset.sum_mul,mass_sum hp h1 n,one_mul,Nat.cast_succ]

/-- Summing the one-site deletion inequalities gives a positive average
endpoint correlation, including the physical length-one term. -/
theorem mean_endpoint_lower {p τ : ℝ} (hp : 0<p) (ph : p<1/2) (hτ : 0<τ)
    (b : ℕ → ℝ) (del : ∀ k, τ * (1-b (k+1))/2 ≤ totalCost p τ (k+1)-totalCost p τ k)
    (N : ℕ) : (N:ℝ)*endpointLower τ ≤ ∑ k ∈ Finset.range N, b (k+1) := by
  have telesc (n : ℕ) :
      τ*((n:ℝ) - ∑ k ∈ Finset.range n, b (k+1))/2 ≤ totalCost p τ n := by
    induction n with
    | zero => simp [totalCost]
    | succ n ih =>
      rw [Nat.cast_succ,Finset.sum_range_succ]
      linarith [del n]
  unfold endpointLower
  have div : (N:ℝ)*(2*Real.log (Real.cosh (τ/2))/τ) =
      ((N:ℝ)*2*Real.log (Real.cosh (τ/2)))/τ := by ring
  rw [div,div_le_iff₀ hτ]
  linarith [telesc N,totalCost_uniform hp ph τ N]

#print axioms mean_endpoint_lower
end BlockHierarchy.VarianceLimit
