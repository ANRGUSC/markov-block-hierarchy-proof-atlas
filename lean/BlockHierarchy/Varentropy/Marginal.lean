import BlockHierarchy.Varentropy.Covariance

open scoped BigOperators
namespace BlockHierarchy.Varentropy

/-- Drop the final bit while preserving chronological order. -/
def dropLast : (k : ℕ) → Bits (k+1) → Bits k
  | 0, _ => ()
  | k+1, w => (w.1,dropLast k w.2)

theorem stationary_bit (m : BinaryModel) (y : Bool) :
    ∑ x, pi m x*transition m x y=pi m y := by
  cases y <;> simp [pi,transition] <;> nlinarith only [m.balanced]

theorem left_mean (m : BinaryModel) (n : ℕ) (f : Bits (n+1) → ℝ) :
    mean (pathLaw m (n+1)) (fun w => f w.2)=mean (pathLaw m n) f := by
  unfold mean
  rw [sum_next,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ys _
  calc
    _ = (∑ x, pi m x*transition m x ys.1)*(tailLaw m ys.1 n ys.2*f ys) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      change (pi m x*(transition m x ys.1*tailLaw m ys.1 n ys.2))*f ys=_
      ring
    _ = _ := by rw [stationary_bit]; unfold pathLaw; ring

theorem left_cov (m : BinaryModel) (n : ℕ) (f g : Bits (n+1) → ℝ) :
    covariance (pathLaw m (n+1)) (fun w => f w.2) (fun w => g w.2)=covariance (pathLaw m n) f g := by
  unfold covariance
  rw [left_mean,left_mean]
  have h := left_mean m n (fun w => (f w-mean (pathLaw m n) f)*(g w-mean (pathLaw m n) g))
  simpa only [mean,mul_assoc] using h

theorem tail_drop (m : BinaryModel) (n : ℕ) (x : Bool) (f : Bits n → ℝ) :
    (∑ w, tailLaw m x (n+1) w*f (dropLast n w))=∑ y, tailLaw m x n y*f y := by
  induction n generalizing x with
  | zero =>
    change (∑ w, tailLaw m x 1 w*f ())=∑ y : Unit, 1*f y
    rw [←Finset.sum_mul,tail_mass]
    rw [Fintype.sum_unique]
  | succ n ih =>
    rw [sum_next (n+1),sum_next n (fun y => tailLaw m x (n+1) y*f y)]
    apply Finset.sum_congr rfl
    intro b _
    change (∑ w, (transition m x b*tailLaw m b (n+1) w)*f (b,dropLast n w))=
      ∑ w, (transition m x b*tailLaw m b n w)*f (b,w)
    simp only [mul_assoc,←Finset.mul_sum]
    rw [ih b (fun w => f (b,w))]

theorem right_mean (m : BinaryModel) (n : ℕ) (f : Bits (n+1) → ℝ) :
    mean (pathLaw m (n+1)) (fun w => f (dropLast (n+1) w))=mean (pathLaw m n) f := by
  unfold mean
  rw [sum_next,sum_next n]
  apply Finset.sum_congr rfl
  intro b _
  change (∑ w, (pi m b*tailLaw m b (n+1) w)*f (b,dropLast n w))=
    ∑ w, (pi m b*tailLaw m b n w)*f (b,w)
  simp only [mul_assoc,←Finset.mul_sum]
  rw [tail_drop m n b (fun w => f (b,w))]

theorem right_cov (m : BinaryModel) (n : ℕ) (f g : Bits (n+1) → ℝ) :
    covariance (pathLaw m (n+1)) (fun w => f (dropLast (n+1) w)) (fun w => g (dropLast (n+1) w))=
      covariance (pathLaw m n) f g := by
  unfold covariance
  rw [right_mean,right_mean]
  have h := right_mean m n (fun w => (f w-mean (pathLaw m n) f)*(g w-mean (pathLaw m n) g))
  simpa only [mean,mul_assoc] using h

#print axioms right_cov
#print axioms left_cov
end BlockHierarchy.Varentropy
