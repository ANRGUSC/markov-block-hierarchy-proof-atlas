import BlockHierarchy.Cut.Statement

open scoped BigOperators
namespace BlockHierarchy.VarianceLimit
open Cut

private theorem mean_square_nonneg {X : Type*} [Fintype X] (P f : X → ℝ) (hp : IsPrior P) :
    0 ≤ mean P (fun x => (f x)^2) :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (hp.1 x) (sq_nonneg _))

private theorem center_contract {X : Type*} [Fintype X] (P f : X → ℝ) (hp : IsPrior P) :
    variance P f ≤ mean P (fun x => f x^2) := by
  have e : variance P f = mean P (fun x => f x^2) - (mean P f)^2 := by
    unfold variance
    calc
      _ = ∑ x, (P x*f x^2 - 2*(P x*f x)*mean P f + P x*(mean P f)^2) := by
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.sum_mul,← Finset.mul_sum,hp.2,one_mul]
        unfold mean
        ring
  rw [e]
  linarith [sq_nonneg (mean P f)]

private theorem rms_diff {X : Type*} [Fintype X] (P f g : X → ℝ) (hp : IsPrior P) :
    |Real.sqrt (mean P (fun x => f x^2))-Real.sqrt (mean P (fun x => g x^2))| ≤
      Real.sqrt (mean P (fun x => (f x-g x)^2)) := by
  let A := mean P (fun x => f x^2)
  let B := mean P (fun x => g x^2)
  let C := mean P (fun x => f x*g x)
  let E := mean P (fun x => (f x-g x)^2)
  have lift_sq (u : X → ℝ) : (∑ x, (Real.sqrt (P x)*u x)^2)=mean P (fun x => u x^2) := by
    unfold mean
    apply Finset.sum_congr rfl
    intro x _
    rw [mul_pow,Real.sq_sqrt (hp.1 x)]
  have prod : (∑ x, (Real.sqrt (P x)*f x)*(Real.sqrt (P x)*g x))=C := by
    apply Finset.sum_congr rfl
    intro x _
    calc
      _ = Real.sqrt (P x)^2*(f x*g x) := by ring
      _ = _ := by rw [Real.sq_sqrt (hp.1 x)]
  have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => Real.sqrt (P x)*f x) (fun x => Real.sqrt (P x)*g x)
  rw [prod,lift_sq,lift_sq] at cs
  have ha : (Real.sqrt A)^2=A := Real.sq_sqrt (mean_square_nonneg P f hp)
  have hb : (Real.sqrt B)^2=B := Real.sq_sqrt (mean_square_nonneg P g hp)
  have hc : C ≤ Real.sqrt A*Real.sqrt B := by
    apply le_of_sq_le_sq _ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    rw [mul_pow,ha,hb]
    exact cs
  have expan : E = A+B-2*C := by
    unfold E A B C mean
    rw [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  change |Real.sqrt A-Real.sqrt B| ≤ Real.sqrt E
  apply le_of_sq_le_sq _ (Real.sqrt_nonneg _)
  have hE : 0 ≤ E := mean_square_nonneg P (fun x => f x-g x) hp
  rw [sq_abs,Real.sq_sqrt hE,expan]
  nlinarith

/-- Standard deviations under one probability law differ by at most the
root-mean-square discrepancy of the two observations. -/
theorem sd_diff {X : Type*} [Fintype X] (P f g : X → ℝ) (hp : IsPrior P) :
    |Real.sqrt (variance P f)-Real.sqrt (variance P g)| ≤
      Real.sqrt (mean P (fun x => (f x-g x)^2)) := by
  let F := fun x => f x-mean P f
  let G := fun x => g x-mean P g
  have m : mean P (fun x => f x-g x)=mean P f-mean P g := by
    simp [mean,mul_sub,Finset.sum_sub_distrib]
  have center : mean P (fun x => (F x-G x)^2) = variance P (fun x => f x-g x) := by
    unfold mean variance
    rw [m]
    apply Finset.sum_congr rfl
    intro x _
    dsimp [F,G]
    ring
  apply (rms_diff P F G hp).trans
  rw [center]
  exact Real.sqrt_le_sqrt (center_contract P (fun x => f x-g x) hp)

#print axioms sd_diff
end BlockHierarchy.VarianceLimit
