import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Distributions.Bernoulli

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
namespace BlockHierarchy.Converse

noncomputable def coin (p : Set.Icc (0:ℝ) 1) : Measure Bool := bernoulliMeasure true false p

instance (p : Set.Icc (0:ℝ) 1) : IsProbabilityMeasure (coin p) := by
  unfold coin
  infer_instance

noncomputable def flipsLaw (p : Set.Icc (0:ℝ) 1) : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ => coin p)

instance (p : Set.Icc (0:ℝ) 1) : IsProbabilityMeasure (flipsLaw p) := by
  unfold flipsLaw
  infer_instance

noncomputable def scaledFlip (p : ℝ) (b : Bool) : ℝ :=
  ((if b then 1 else 0)-p) / Real.sqrt (p*(1-p))

private theorem eval_law (p : Set.Icc (0:ℝ) 1) (i : ℕ) :
    HasLaw (fun w : ℕ → Bool => w i) (coin p) (flipsLaw p) :=
  (measurePreserving_eval_infinitePi (fun _ : ℕ => coin p) i).hasLaw

private theorem coordinate_integral (p : Set.Icc (0:ℝ) 1) (i : ℕ) (f : Bool → ℝ) :
    ∫ w, f (w i) ∂flipsLaw p = ∫ b, f b ∂coin p := by
  have h := eval_law p i
  have hf : Measurable f := measurable_of_countable f
  calc
    _ = ∫ b, f b ∂(flipsLaw p).map (fun w : ℕ → Bool => w i) :=
      (integral_map h.aemeasurable hf.aestronglyMeasurable).symm
    _ = _ := by rw [h.map_eq]

/-- CLT for the actual independent Bernoulli flip stream, standardized at
its true mean and variance. -/
theorem flips_clt (p : Set.Icc (0:ℝ) 1) (hp : 0<(p:ℝ)) (h1 : (p:ℝ)<1) :
    TendstoInDistribution
      (fun (n : ℕ) (w : ℕ → Bool) => (Real.sqrt n)⁻¹ *
        ∑ k ∈ Finset.range n, scaledFlip p (w k))
      atTop (id : ℝ → ℝ) (fun _ => flipsLaw p) (gaussianReal 0 1) := by
  let X := fun (i : ℕ) (w : ℕ → Bool) => scaledFlip p (w i)
  have hm : Measurable (scaledFlip p) := measurable_of_countable _
  have hind : iIndepFun X (flipsLaw p) := iIndepFun_infinitePi (fun _ : ℕ => hm)
  have same (i : ℕ) : IdentDistrib (X i) (X 0) (flipsLaw p) (flipsLaw p) :=
    ((eval_law p i).identDistrib (eval_law p 0)).comp hm
  have z : ∫ w, X 0 w ∂flipsLaw p = 0 := by
    rw [show (fun w => X 0 w) = (fun w => scaledFlip p (w 0)) from rfl,
      coordinate_integral p 0 (scaledFlip p),coin,integral_bernoulliMeasure]
    simp [scaledFlip,smul_eq_mul]
    ring
  have v : ∫ w, (X 0 w)^2 ∂flipsLaw p = 1 := by
    rw [show (fun w => (X 0 w)^2) = (fun w => (fun b => (scaledFlip p b)^2) (w 0)) from rfl,
      coordinate_integral p 0 (fun b => (scaledFlip p b)^2),coin,integral_bernoulliMeasure]
    have hpos : 0 < (p:ℝ)*(1-p) := mul_pos hp (by linarith)
    simp only [scaledFlip,ite_true,Bool.false_eq_true,ite_false,zero_sub,smul_eq_mul,div_pow,
      Real.sq_sqrt hpos.le]
    field_simp [hp.ne', (sub_pos.mpr h1).ne'] <;> ring
  have normal : HasLaw (id : ℝ → ℝ) (gaussianReal 0 1) (gaussianReal 0 1) :=
    HasLaw.id
  exact tendstoInDistribution_inv_sqrt_mul_sum (X := X) normal z v hind same

#print axioms flips_clt
end BlockHierarchy.Converse
