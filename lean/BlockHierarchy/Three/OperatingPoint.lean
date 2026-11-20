import BlockHierarchy.FiniteRD
import BlockHierarchy.Three.ConstantColumns

open scoped BigOperators
namespace BlockHierarchy.Three

theorem source_pos {p : ℝ} (hp : 0 < p) (half : p < 1/2) (x : Word) : 0 < markov p x := by
  have : 0 < 1-p := by linarith
  obtain ⟨i,j,k⟩ := x
  cases i <;> cases j <;> cases k <;> norm_num [markov,step] <;> positivity

theorem class_map (f : ℝ → ℝ) (a b c : ℝ) (x : Word) :
    f (classValue a b c x) = classValue (f a) (f b) (f c) x := by
  unfold classValue
  split <;> split <;> rfl

noncomputable def weightedDistance (q : Word → ℝ) (u : ℝ) (x : Word) :=
  ∑ y, q y*u^hamming x y*(hamming x y : ℝ)

noncomputable def alphaCost (u : ℝ) := 3*u^3/2
noncomputable def betaCost (u : ℝ) := (u+2*u^2)/2

theorem class_distance (w0 w1 w2 u : ℝ) (x : Word) :
    weightedDistance (prior w0 w1 w2) u x =
      betaCost u*(w0+w1+w2)+(alphaCost u-betaCost u)*classValue w0 (w1/2) w2 x := by
  unfold weightedDistance
  rw [word_sum]
  obtain ⟨i,j,k⟩ := x
  cases i <;> cases j <;> cases k <;>
    norm_num [alphaCost,betaCost,prior,hamming,classValue] <;> ring

theorem operating_cost (p u : ℝ) (q z : Word → ℝ) :
    Channel.cost (fun x y => (hamming x y : ℝ)) (FiniteRD.joint (markov p) z q hamming u) =
    ∑ x, markov p x*(weightedDistance q u x/z x) := by
  unfold Channel.cost FiniteRD.joint FiniteRD.kernel weightedDistance
  apply Finset.sum_congr rfl
  intro x _
  simp only [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

noncomputable def classMean (p a b c : ℝ) :=
  (1-p)^2*a + 2*p*(1-p)*b+p^2*c

noncomputable def classVariance (p a b c : ℝ) :=
  let m := classMean p a b c
  classMean p ((a-m)^2) ((b-m)^2) ((c-m)^2)

theorem class_var (p a b c : ℝ) :
    variance (markov p) (classValue a b c) = classVariance p a b c := by
  unfold variance mean
  rw [class_expectation]
  let m := classMean p a b c
  calc
    _ = ∑ x, markov p x * classValue ((a-m)^2) ((b-m)^2) ((c-m)^2) x := by
      apply Finset.sum_congr rfl
      intro x _
      exact congrArg (markov p x * ·) (class_map (fun v => (v-m)^2) a b c x)
    _ = _ := class_expectation _ _ _ _

noncomputable def tilted (p b u : ℝ) (z : Word → ℝ) :=
  variance (markov p) (fun x => b*logTwo u-logTwo (z x))

theorem class_tilt (p b u a v c : ℝ) :
    tilted p b u (classValue a v c) = classVariance p (-logTwo a) (-logTwo v) (-logTwo c) := by
  have mass : ∑ x, markov p x = 1 := by
    rw [word_sum]
    norm_num [markov,step]
    ring
  unfold tilted
  simp only [sub_eq_add_neg]
  rw [variance_shift _ _ mass]
  have m := funext (class_map (fun t => -logTwo t) a v c)
  rw [m,class_var]

theorem class_log_mean (p a b c : ℝ) :
    mean (markov p) (fun x => logTwo (classValue a b c x)) =
      classMean p (logTwo a) (logTwo b) (logTwo c) := by
  unfold mean
  simp_rw [class_map logTwo]
  exact class_expectation _ _ _ _

end BlockHierarchy.Three
