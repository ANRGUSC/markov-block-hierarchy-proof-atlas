import BlockHierarchy.Varentropy.Statement
import Mathlib.Tactic.LinearCombination

open scoped BigOperators
namespace BlockHierarchy.Varentropy

noncomputable def step (m : BinaryModel) (f : Bool → ℝ) (x : Bool) :=
  ∑ y, transition m x y*f y

noncomputable def iterate (m : BinaryModel) (f : Bool → ℝ) : ℕ → Bool → ℝ
  | 0 => f
  | h+1 => step m (iterate m f h)

noncomputable def rowReward (m : BinaryModel) (x : Bool) :=
  ∑ y, transition m x y*A m x y

theorem step_const (m : BinaryModel) (c : ℝ) (x : Bool) : step m (fun _ => c) x=c := by
  cases x <;> simp [step,transition] <;> ring

theorem pi_mass (m : BinaryModel) : ∑ x, pi m x=1 := by
  simpa [pi,add_comm] using m.normalized

theorem spectral_step (m : BinaryModel) (f : Bool → ℝ) (x : Bool) :
    step m f x=mean (pi m) f+m.persistence*(f x-mean (pi m) f) := by
  have hA : m.a=m.q*(m.a+m.b) := by
    nlinarith only [m.balanced,congrArg (fun r : ℝ => r*m.a) m.normalized]
  have hB : m.b=m.p*(m.a+m.b) := by
    nlinarith only [m.balanced,congrArg (fun r : ℝ => r*m.b) m.normalized]
  have hq : 1-m.p=m.q := by linarith only [m.normalized]
  have hp : 1-m.q=m.p := by linarith only [m.normalized]
  have centered (b : Bool) : f b-mean (pi m) f=
      if b then m.p*(f true-f false) else m.q*(f false-f true) := by
    cases b <;> simp [mean,pi] <;>
      first | linear_combination (f false)*m.normalized.symm | linear_combination (f true)*m.normalized.symm
  rw [centered]
  cases x <;> simp [step,transition,BinaryModel.persistence,mean,pi]
  · linear_combination (f false)*(m.normalized.symm) + (f true-f false)*hA
  · linear_combination (f true)*(m.normalized.symm) + (f false-f true)*hB

theorem iterate_formula (m : BinaryModel) (f : Bool → ℝ) (h : ℕ) (x : Bool) :
    iterate m f h x=mean (pi m) f+m.persistence^h*(f x-mean (pi m) f) := by
  induction h generalizing x with
  | zero => simp [iterate]
  | succ n ih =>
    change (∑ y, transition m x y * iterate m f n y)=_
    simp_rw [ih]
    let M := mean (pi m) f
    calc
      _ = step m (fun _ => M) x+m.persistence^n*(step m f x-step m (fun _ => M) x) := by
        unfold step
        simp only [Fintype.sum_bool]; dsimp [M]; ring
      _ = _ := by rw [step_const,spectral_step,pow_succ]; dsimp [M]; ring

/-- Last edge of a suffix with h intervening transitions. -/
noncomputable def lastEdge (m : BinaryModel) (x : Bool) : (h : ℕ) → Bits ((h+1)) → ℝ
  | 0, ys => A m x ys.1
  | h+1, ys => lastEdge m ys.1 h ys.2

theorem sum_next (n : ℕ) (f : Bits (n+1) → ℝ) :
    (∑ ys, f ys)=∑ x : Bool, ∑ ys : Bits n, f (x,ys) := Fintype.sum_prod_type ..

theorem tail_mass (m : BinaryModel) (n : ℕ) (x : Bool) :
    (∑ ys, tailLaw m x n ys)=1 := by
  induction n generalizing x with
  | zero =>
    change (∑ _ : Unit, (1:ℝ))=1
    simp
  | succ n ih =>
    rw [sum_next]; simp only [tailLaw,← Finset.mul_sum,ih,mul_one]
    simpa only [step,mul_one] using step_const m 1 x

theorem path_mass (m : BinaryModel) (n : ℕ) : ∑ w, pathLaw m n w=1 := by
  rw [sum_next]
  simp only [pathLaw,← Finset.mul_sum,tail_mass,mul_one,pi_mass]

theorem last_edge_conditional (m : BinaryModel) (x : Bool) (h : ℕ) :
    (∑ ys, tailLaw m x (h+1) ys*lastEdge m x h ys)=iterate m (rowReward m) h x := by
  induction h generalizing x with
  | zero =>
    rw [sum_next]
    change (∑ y : Bool, ∑ _ : Unit, (transition m x y*1)*A m x y)=_
    simp [iterate,rowReward]
  | succ h ih =>
    rw [sum_next]
    change (∑ y : Bool, ∑ w : Bits (h+1), (transition m x y*tailLaw m y (h+1) w)*lastEdge m y h w)=_
    simp only [mul_assoc,← Finset.mul_sum,ih,iterate,step]

#print axioms iterate_formula
#print axioms last_edge_conditional
end BlockHierarchy.Varentropy
