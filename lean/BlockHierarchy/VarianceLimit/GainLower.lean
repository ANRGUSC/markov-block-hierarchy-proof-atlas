import BlockHierarchy.VarianceLimit.Gibbs
import BlockHierarchy.Cut.Paper
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

open scoped BigOperators
namespace BlockHierarchy.VarianceLimit
open Cut

variable {X : Type*} [Fintype X]

theorem mean_exp_lower (Q f : X → ℝ) (hQ : IsPrior Q) :
    Real.exp (mean Q f) ≤ mean Q (fun y => Real.exp (f y)) := by
  let m := mean Q f
  have row (y : X) : Q y*(f y-m+1) ≤ Q y*(Real.exp (f y) * Real.exp (-m)) := by
    apply mul_le_mul_of_nonneg_left _ (hQ.1 y)
    simpa only [sub_eq_add_neg,Real.exp_add] using Real.add_one_le_exp (f y-m)
  have hb := Finset.sum_le_sum (fun y (_ : y∈ Finset.univ) => row y)
  have lhs : (∑ y, Q y*(f y-m+1))=1 := by
    simp only [mul_add,mul_sub,mul_one,Finset.sum_add_distrib,Finset.sum_sub_distrib,
      ←Finset.sum_mul,hQ.2,one_mul,m,mean,sub_self,zero_add]
  rw [lhs] at hb
  simp only [←mul_assoc,←Finset.sum_mul,Real.exp_neg] at hb
  change 1 ≤ mean Q (fun y => Real.exp (f y)) / Real.exp m at hb
  simpa using (le_div_iff₀ (Real.exp_pos m)).mp hb

/-- Exponentially tilting a centered fair spin leaves total prior mass one. -/
private theorem tilted_prior (q h : X → ℝ) (hq : IsPrior q)
    (spin : ∀ y, h y = 1 ∨ h y = -1) (zero : mean q h=0) (r : ℝ) :
    IsPrior (fun y => q y*(Real.exp (r*h y)/Real.cosh r)) := by
  have line (y : X) : Real.exp (r*h y)=Real.cosh r+h y*Real.sinh r := by
    rcases spin y with e | e <;> rw [e] <;> simp [Real.cosh_eq,Real.sinh_eq] <;> ring
  refine ⟨fun y => mul_nonneg (hq.1 y) (div_pos (Real.exp_pos _) (Real.cosh_pos r)).le,?_⟩
  simp only [line,div_eq_mul_inv,←mul_assoc,←Finset.sum_mul]
  simp only [mul_add,Finset.sum_add_distrib,←mul_assoc,←Finset.sum_mul,hq.2,one_mul]
  change (Real.cosh r+mean q h*Real.sinh r)*(Real.cosh r)⁻¹=1
  rw [zero,zero_mul,add_zero,mul_inv_cancel₀ (Real.cosh_pos r).ne']

/-- A fair-spin tilt of a trial prior gives a gain of at least half the squared
mean of its conditional reproduction spin under the true source. -/
theorem spin_gain {P q qStar : X → ℝ} {τ : ℝ} {d : X → X → ℕ}
    (hp : IsPrior P) (hq : IsPrior q) (opt : Optimal P τ d qStar)
    (h : X → ℝ) (spin : ∀ y, h y=1 ∨ h y= -1) (zero : mean q h=0) :
    let r := mean P (fun x => mean (gibbsChannel τ d q x) h)
    r^2/2 ≤ mean P (score τ d q)-mean P (score τ d qStar) := by
  let W := gibbsChannel τ d q
  let b (x : X) := mean (W x) h
  let r := mean P b
  let trial (y : X) := q y*(Real.exp (r*h y)/Real.cosh r)
  have feasible := tilted_prior q h hq spin zero r
  have law := gibbs_isChannel τ d hq
  have hr (x : X) : mean (W x) (fun y => r*h y)=r*b x := by
    unfold b mean
    simp_rw [mul_left_comm (W x _) r,←Finset.mul_sum]
  have split (x : X) : mean (W x) (fun y => Real.exp (r*h y)) =
      Z τ d trial x*Real.cosh r / Z τ d q x := by
    unfold mean Z
    simp only [div_eq_mul_inv,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    dsimp [trial,W,gibbsChannel,Z]
    field_simp [(Real.cosh_pos r).ne']
  have point (x : X) : r*b x-Real.log (Real.cosh r) ≤ score τ d q x-score τ d trial x := by
    have bound := mean_exp_lower (W x) (fun y => r*h y) (law x)
    rw [hr,split] at bound
    have logs := Real.log_le_log (Real.exp_pos _) bound
    rw [Real.log_exp,Real.log_div (mul_pos (Z_pos _ _ feasible x) (Real.cosh_pos r)).ne' (Z_pos _ _ hq x).ne',
      Real.log_mul (Z_pos _ _ feasible x).ne' (Real.cosh_pos r).ne'] at logs
    unfold score
    linarith
  have avg := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => mul_le_mul_of_nonneg_left (point x) (hp.1 x))
  simp only [mul_sub,Finset.sum_sub_distrib,mul_left_comm (P _) r,←Finset.mul_sum,←Finset.sum_mul,hp.2,one_mul] at avg
  change r*r-Real.log (Real.cosh r) ≤ mean P (score τ d q)-mean P (score τ d trial) at avg
  have gauss := Real.log_le_log (Real.cosh_pos r) (Real.cosh_le_exp_half_sq r)
  rw [Real.log_exp] at gauss
  have optimal := opt.2 trial feasible
  change r^2/2 ≤ _
  linarith only [avg,gauss,optimal,sq r]


def bitSpin (b : Bool) : ℝ := if b then -1 else 1

def endSpin (n : ℕ) (x : Word n) : ℝ := bitSpin (last x)
def firstSpin (n : ℕ) (x : Word n) : ℝ := bitSpin x.1

private theorem prod_sum {A B : Type*} [Fintype A] [Fintype B] (f : A → ℝ) (g : B → ℝ) :
    (∑ w : A × B, f w.1*g w.2)=(∑ a,f a)*(∑ b,g b) := by
  simp only [Fintype.sum_prod_type,←Finset.mul_sum,←Finset.sum_mul]

private theorem prod_mean {A B : Type*} [Fintype A] [Fintype B] (P f : A → ℝ) (Q g : B → ℝ) :
    mean (fun w : A × B => P w.1*Q w.2) (fun w => f w.1*g w.2)=mean P f*mean Q g := by
  unfold mean
  convert prod_sum (fun a => P a*f a) (fun b => Q b*g b) using 1
  apply Finset.sum_congr rfl
  intro w _
  ring

private theorem adj_factor (p : ℝ) (i j : ℕ) (w : Word i × Word j) :
    adjacent p i j w=mass p i w.1*mass p j w.2*(1+(1-2*p)*endSpin i w.1*firstSpin j w.2) := by
  rw [adjacent_density]
  unfold productMass endSpin firstSpin
  apply congrArg (fun t : ℝ => mass p i w.1*mass p j w.2*t)
  cases last w.1 <;> cases w.2.1 <;> norm_num [Cut.step,bitSpin] <;> ring

theorem adjacent_spin_product (p : ℝ) (i j : ℕ) (f : Word i → ℝ) (g : Word j → ℝ) :
    mean (adjacent p i j) (fun w => f w.1*g w.2)=mean (mass p i) f*mean (mass p j) g+
      (1-2*p)*mean (mass p i) (fun x => endSpin i x*f x)*mean (mass p j) (fun x => firstSpin j x*g x) := by
  have term (w : Word i × Word j) : adjacent p i j w*(f w.1*g w.2)=
      (mass p i w.1*f w.1)*(mass p j w.2*g w.2) +
      (1-2*p)*((mass p i w.1*(endSpin i w.1*f w.1))*(mass p j w.2*(firstSpin j w.2*g w.2))) := by
    rw [adj_factor]; ring
  unfold mean
  simp_rw [term,Finset.sum_add_distrib,←Finset.mul_sum]
  rw [prod_sum (fun x => mass p i x*f x) (fun x => mass p j x*g x),
    prod_sum (fun x => mass p i x*(endSpin i x*f x)) (fun x => mass p j x*(firstSpin j x*g x))]
  ring

private theorem gibbs_push {τ : ℝ} {d : X → X → ℕ} {P q : X → ℝ}
    (hp : IsPrior P) (opt : Optimal P τ d q) (f : X → ℝ) :
    mean P (fun x => mean (gibbsChannel τ d q x) f)=mean q f := by
  unfold mean
  simp only [Finset.mul_sum,←mul_assoc]
  rw [Finset.sum_comm]
  simp only [←Finset.sum_mul,gibbs_marginal hp opt]

private theorem gibbs_prod {i j : ℕ} (τ : ℝ) (q : Word i → ℝ) (v : Word j → ℝ)
    (w y : Word i × Word j) :
    gibbsChannel τ (jointDistance i j) (trialPrior q v) w y=
      gibbsChannel τ (distance i) q w.1 y.1*gibbsChannel τ (distance j) v w.2 y.2 := by
  simp only [gibbsChannel,jointDistance,Nat.cast_add,mul_add,Real.exp_add,trialPrior]
  rw [trial_Z]
  ring

/-- The endpoint Gibbs correlation for either boundary observable on a single word. -/
noncomputable def endpointCorrelation (p τ : ℝ) (n : ℕ) (q a : Word n → ℝ) :=
  mean (mass p n) (fun x => a x*mean (gibbsChannel τ (distance n) q x) a)


/-- Actual lower gain across one Markov cut from the correlations between each
source endpoint and its local Gibbs reproduction. -/
theorem gain_lower_adjacent {p τ : ℝ} (hp : 0<p) (ph : p<1) {i j : ℕ}
    {q : Word i → ℝ} {v : Word j → ℝ} {joint : Word i × Word j → ℝ}
    (L : Optimal (mass p i) τ (distance i) q) (R : Optimal (mass p j) τ (distance j) v)
    (J : Optimal (adjacent p i j) τ (jointDistance i j) joint)
    (lc : mean q (endSpin i)=0) (rcen : mean v (firstSpin j)=0) :
    ((1-2*p)*endpointCorrelation p τ i q (endSpin i)*endpointCorrelation p τ j v (firstSpin j))^2/2 ≤
      mean (mass p i) (score τ (distance i) q) + mean (mass p j) (score τ (distance j) v) -
        mean (adjacent p i j) (score τ (jointDistance i j) joint) := by
  let S (w : Word i × Word j) := endSpin i w.1*firstSpin j w.2
  let Q := trialPrior q v
  let P := adjacent p i j
  let d := jointDistance i j
  let A (x : Word i) := mean (gibbsChannel τ (distance i) q x) (endSpin i)
  let B (x : Word j) := mean (gibbsChannel τ (distance j) v x) (firstSpin j)
  have unit : IsPrior P := ⟨fun w => (adjacent_pos hp ph i j w).le,adjacent_sum hp ph i j⟩
  have spins (w : Word i × Word j) : S w=1 ∨ S w= -1 := by
    unfold S endSpin firstSpin bitSpin; split <;> split <;> norm_num
  have center : mean Q S=0 := (prod_mean q (endSpin i) v (firstSpin j)).trans (by rw [lc,zero_mul])
  have tilt := spin_gain unit (trial_isPrior L.1 R.1) J S spins center
  have factor (w : Word i × Word j) : mean (gibbsChannel τ d Q w) S=A w.1*B w.2 := by
    change mean (gibbsChannel τ (jointDistance i j) (trialPrior q v) w) S=_
    simp_rw [show gibbsChannel τ (jointDistance i j) (trialPrior q v) w =
      (fun y => gibbsChannel τ (distance i) q w.1 y.1*gibbsChannel τ (distance j) v w.2 y.2) from funext (gibbs_prod τ q v w)]
    exact prod_mean _ (endSpin i) _ (firstSpin j)
  have a0 : mean (mass p i) A=0 := (gibbs_push ⟨fun x => (mass_pos hp ph i x).le,mass_sum hp ph i⟩ L _).trans lc
  have b0 : mean (mass p j) B=0 := (gibbs_push ⟨fun x => (mass_pos hp ph j x).le,mass_sum hp ph j⟩ R _).trans rcen
  have corr : mean P (fun w => mean (gibbsChannel τ d Q w) S) =
      (1-2*p)*endpointCorrelation p τ i q (endSpin i)*endpointCorrelation p τ j v (firstSpin j) := by
    simp_rw [factor]
    rw [show mean P (fun w => A w.1*B w.2)=_ from adjacent_spin_product p i j A B,a0,zero_mul,zero_add]
    rfl
  have ind := optimal_independent hp ph q R
  have ml := ind id (fun _ => 1)
  have mr := ind (fun _ => 1) id
  simp [mean,mass_sum hp ph] at ml mr
  have base : mean P (score τ d Q) =
      mean (mass p i) (score τ (distance i) q) + mean (mass p j) (score τ (distance j) v) := by
    unfold mean
    simp_rw [show score τ d Q = _ from funext (trial_score τ L.1 R.1),mul_add,Finset.sum_add_distrib]
    exact congrArg₂ (·+·) ml mr
  change (mean P (fun w => mean (gibbsChannel τ d Q w) S))^2/2≤mean P (score τ d Q)-_ at tilt
  rwa [corr,base] at tilt

#print axioms spin_gain
#print axioms gain_lower_adjacent
end BlockHierarchy.VarianceLimit
