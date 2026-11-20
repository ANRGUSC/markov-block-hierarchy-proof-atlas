import BlockHierarchy.VarianceLimit.GainLower
import BlockHierarchy.VarianceLimit.Redundancy
import BlockHierarchy.Varentropy.Marginal

open scoped BigOperators
namespace BlockHierarchy.VarianceLimit
open Cut Varentropy

noncomputable def deleteFirstPrior (n : ℕ) (q : Word n → ℝ) (y : Bits n) := ∑ a : Bool, q (a,y)

private theorem delete_prior (n : ℕ) {q : Word n → ℝ} (hq : IsPrior q) : IsPrior (deleteFirstPrior n q) := by
  refine ⟨fun _ => Finset.sum_nonneg (fun _ _ => hq.1 _),?_⟩
  unfold deleteFirstPrior
  rw [Finset.sum_comm,←sum_next]
  exact hq.2

/-- Removing the first bit removes its mismatch from Hamming distortion. Under
the full Gibbs law, the exponential moment of that mismatch is the ratio of
the short and long normalizers. -/
private theorem delete_exp (n : ℕ) (τ : ℝ) (q : Word n → ℝ) (x : Word n) :
    mean (gibbsChannel τ (distance n) q x) (fun y => Real.exp (τ * (if x.1=y.1 then 0 else 1))) =
      Z τ (hamming n) (deleteFirstPrior n q) x.2 / Z τ (distance n) q x := by
  have factor (y : Word n) : Real.exp (-τ*(distance n x y : ℝ)) *
      Real.exp (τ*(if x.1=y.1 then 0 else 1)) = Real.exp (-τ*(hamming n x.2 y.2 : ℝ)) := by
    rw [←Real.exp_add]
    congr 1
    by_cases e : x.1=y.1 <;> simp [distance,hamming,e] <;> ring
  have term (y : Word n) : gibbsChannel τ (distance n) q x y*Real.exp (τ*(if x.1=y.1 then 0 else 1)) =
      q y*Real.exp (-τ*(hamming n x.2 y.2 : ℝ)) / Z τ (distance n) q x := by
    rw [←factor]
    unfold gibbsChannel
    ring
  unfold mean
  simp only [term,div_eq_mul_inv,←Finset.sum_mul]
  apply congrArg (· * (Z τ (distance n) q x)⁻¹)
  unfold Z deleteFirstPrior
  rw [sum_next]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]

theorem deletion_gain {p τ : ℝ} (hp : 0<p) (ph : p<1) (n : ℕ)
    {q : Word n → ℝ} (hq : IsPrior q) :
    τ*(1-endpointCorrelation p τ n q (firstSpin n))/2 ≤
      mean (mass p n) (score τ (distance n) q) -
      mean (mass p n) (fun x => score τ (hamming n) (deleteFirstPrior n q) x.2) := by
  let W := gibbsChannel τ (distance n) q
  let a := firstSpin n
  let P := mass p n
  let L := score τ (distance n) q
  let S (x : Word n) := score τ (hamming n) (deleteFirstPrior n q) x.2
  have row := gibbs_isChannel τ (distance n) hq
  have point (x : Word n) : τ/2-(τ/2)*(a x*mean (W x) a) ≤ L x - S x := by
    have e := mean_exp_lower (W x) (fun y => τ*(if x.1=y.1 then 0 else 1)) (row x)
    rw [delete_exp] at e
    have lg := Real.log_le_log (Real.exp_pos _) e
    rw [Real.log_exp,Real.log_div (Z_pos _ _ (delete_prior n hq) x.2).ne' (Z_pos _ _ hq x).ne'] at lg
    have term (y : Word n) : W x y*(τ*(if x.1=y.1 then 0 else 1)) =
        W x y*(τ/2)-((τ/2)*a x)*(W x y*a y) := by
      change W x y*(τ*(if x.1=y.1 then 0 else 1))=
        W x y*(τ/2)-(τ/2*bitSpin x.1)*(W x y*bitSpin y.1)
      cases x.1 <;> cases y.1 <;> norm_num [bitSpin] <;> ring
    unfold mean at lg
    simp only [term,Finset.sum_sub_distrib,←Finset.sum_mul,←Finset.mul_sum,W,(row x).2,one_mul] at lg
    change τ/2-(τ/2*a x)*mean (W x) a ≤ _ at lg
    unfold L S score
    linarith only [lg,mul_assoc (τ/2) (a x) (mean (W x) a)]
  have avg := Finset.sum_le_sum (fun x (_ : x∈Finset.univ) => mul_le_mul_of_nonneg_left (point x) (mass_pos hp ph n x).le)
  simp only [mul_sub,Finset.sum_sub_distrib,mul_left_comm (mass p n _) (τ/2),←Finset.sum_mul,←Finset.mul_sum,mass_sum hp ph,one_mul] at avg
  calc
    _ = τ/2-τ/2*endpointCorrelation p τ n q (firstSpin n) := by ring
    _ ≤ _ := avg


theorem totalCost_optimal {p τ : ℝ} (n : ℕ) {q : Word n → ℝ} (opt : Optimal (mass p n) τ (distance n) q) :
    mean (mass p n) (score τ (distance n) q)=totalCost p τ (n+1) := by
  have canon := canonical_optimal p τ n
  exact (opt.2 _ canon.1).antisymm (canon.2 _ opt.1)

/-- Each nonempty physical block, including length one, pays at least the
multiplier times its first-bit Gibbs distortion when that coordinate is removed. -/
theorem endpoint_increment {p τ : ℝ} (hp : 0<p) (ph : p<1) (n : ℕ)
    {q : Word n → ℝ} (opt : Optimal (mass p n) τ (distance n) q) :
    τ*(1-endpointCorrelation p τ n q (firstSpin n))/2 ≤
      totalCost p τ (n+1)-totalCost p τ n := by
  have bound := deletion_gain (τ:=τ) hp ph n opt.1
  rw [totalCost_optimal n opt] at bound
  suffices short : totalCost p τ n ≤ mean (mass p n) (fun x => score τ (hamming n) (deleteFirstPrior n q) x.2) by
    linarith only [bound,short]
  cases n with
  | zero =>
    have z (y : Bits 0) : Z τ (hamming 0) (deleteFirstPrior 0 q) y=1 := by
      simp only [Z,hamming,Nat.cast_zero,mul_zero,Real.exp_zero,mul_one,(delete_prior 0 opt.1).2]
    simp only [score,z,Real.log_one,neg_zero,mean,mul_zero,Finset.sum_const_zero,totalCost,le_refl]
  | succ n =>
    let f := score τ (distance n) (deleteFirstPrior (n+1) q)
    have marg : mean (mass p (n+1)) (fun x => f x.2)=mean (mass p n) f := by
      have same (k : ℕ) : mass p k = pathLaw (symmetricModel p hp ph) k :=
        funext (mass_eq_pathLaw hp ph k)
      rw [same (n+1),same n]
      exact left_mean _ n f
    change totalCost p τ (n+1) ≤ mean (mass p (n+1)) (fun x => f x.2)
    rw [marg]
    exact (canonical_optimal p τ n).2 _ (delete_prior (n+1) opt.1)

#print axioms endpoint_increment
end BlockHierarchy.VarianceLimit
