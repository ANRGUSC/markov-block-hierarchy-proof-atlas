import BlockHierarchy.Varentropy.Lag
import BlockHierarchy.Varentropy.Marginal

open scoped BigOperators
namespace BlockHierarchy.Varentropy

private theorem mean_add {X : Type*} [Fintype X] (P f g : X → ℝ) :
    mean P (f+g) = mean P f+mean P g := by
  simp [mean, mul_add, Finset.sum_add_distrib]

private theorem cov_add {X : Type*} [Fintype X] (P f g h : X → ℝ) :
    covariance P (f+g) h = covariance P f h + covariance P g h := by
  unfold covariance
  rw [mean_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Pi.add_apply]
  ring

private theorem var_sum {X : Type*} [Fintype X] (P f g : X → ℝ) :
    variance P (f+g)=variance P f+variance P g+2*covariance P f g := by
  unfold variance covariance
  rw [mean_add, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Pi.add_apply]
  ring

private theorem self_cov {X : Type*} [Fintype X] (P f : X → ℝ) :
    covariance P f f=variance P f := by
  unfold covariance variance
  simp only [pow_two,mul_assoc]

private theorem formula_step (m : BinaryModel) (n : ℕ) :
    finiteFormula m (n+1)=finiteFormula m n+edgeVar m+
      2*(m.persistence^n*kappa m + (∑ i ∈ Finset.range n, m.persistence^i)*gamma m) := by
  have extend : (∑ i ∈ Finset.range (n-1), ((n:ℝ)-(i:ℝ)-1)*m.persistence^i) =
      ∑ i ∈ Finset.range n, ((n:ℝ)-(i:ℝ)-1)*m.persistence^i := by
    cases n with
    | zero => simp
    | succ k => simp [Finset.sum_range_succ]
  have change_sum : (∑ i ∈ Finset.range n, (((n:ℝ)+1)-(i:ℝ)-1)*m.persistence^i) =
      (∑ i ∈ Finset.range n, ((n:ℝ)-(i:ℝ)-1)*m.persistence^i)+
        ∑ i ∈ Finset.range n, m.persistence^i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold finiteFormula
  rw [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,change_sum,extend,Finset.sum_range_succ]
  ring

private noncomputable def totalScore (m : BinaryModel) (n : ℕ) (w : Bits (n+1)) :=
  B m w.1+edgeSum m w.1 n w.2

private theorem base_variance (m : BinaryModel) :
    variance (pathLaw m 0) (totalScore m 0)=varB m := by
  unfold varB variance mean
  simp only [sum_next,pathLaw,tailLaw,totalScore,edgeSum,mul_one,add_zero]
  simp [show Fintype.card (Bits 0)=1 from rfl]

section
variable (m : BinaryModel)
variable (cut : (k : ℕ) → Bits (k+1) → Bits k)
variable (cut_succ : ∀ k (w : Bits (k+2)), cut (k+1) w = (w.1,cut k w.2))
variable (left : ∀ n (f g : Bits (n+1) → ℝ),
    covariance (pathLaw m (n+1)) (fun w => f w.2) (fun w => g w.2)=covariance (pathLaw m n) f g)
variable (right : ∀ n (f g : Bits (n+1) → ℝ),
    covariance (pathLaw m (n+1)) (fun w => f (cut (n+1) w)) (fun w => g (cut (n+1) w))=covariance (pathLaw m n) f g)
variable (initial : ∀ n, covariance (pathLaw m (n+1)) (fun w => B m w.1)
    (fun w => lastEdge m w.1 n w.2)=m.persistence^n*kappa m)
variable (edge : ∀ n, covariance (pathLaw m (n+2)) (fun w => A m w.1 w.2.1)
    (fun w => lastEdge m w.2.1 n w.2.2)=m.persistence^n*gamma m)

private noncomputable def oldEdges (n : ℕ) (w : Bits (n+2)) := edgeSum m w.1 n (cut n w.2)
private noncomputable def finalEdge (n : ℕ) (w : Bits (n+2)) := lastEdge m w.1 n w.2

include cut_succ in
private theorem append_score (n : ℕ) (x : Bool) (w : Bits (n+1)) :
    edgeSum m x (n+1) w = edgeSum m x n (cut n w)+lastEdge m x n w := by
  induction n generalizing x with
  | zero => simp [edgeSum,lastEdge]
  | succ n ih =>
    rw [cut_succ]
    change A m x w.1 + edgeSum m w.1 (n+1) w.2 = (A m x w.1+edgeSum m w.1 n (cut n w.2))+lastEdge m w.1 n w.2
    rw [ih]
    ring

include left in
private theorem final_var (n : ℕ) : variance (pathLaw m (n+1)) (finalEdge m n)=edgeVar m := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← self_cov, ← ih, ← self_cov]
    exact left (n+1) (finalEdge m n) (finalEdge m n)

include left edge cut_succ in
private theorem old_final_cov (n : ℕ) :
    covariance (pathLaw m (n+1)) (oldEdges m cut n) (finalEdge m n)=
      (∑ i ∈ Finset.range n,m.persistence^i)*gamma m := by
  induction n with
  | zero =>
    simp [oldEdges,edgeSum,covariance,mean]
  | succ n ih =>
    have split : oldEdges m cut (n+1) = (fun w : Bits (n+3) => A m w.1 w.2.1) +
        (fun w => oldEdges m cut n w.2) := by
      funext w
      simp only [oldEdges,cut_succ,edgeSum,Pi.add_apply]
    rw [split,cov_add,Finset.sum_range_succ,add_mul]
    change covariance (pathLaw m (n+2)) (fun w => A m w.1 w.2.1) (fun w => lastEdge m w.2.1 n w.2.2) +
      covariance (pathLaw m (n+2)) (fun w => oldEdges m cut n w.2) (fun w => finalEdge m n w.2) = _
    rw [edge,left,ih,add_comm]

include cut_succ left right initial edge in
private theorem score_variance (n : ℕ) : variance (pathLaw m n) (totalScore m n)=finiteFormula m n := by
  induction n with
  | zero => simpa [finiteFormula] using base_variance m
  | succ n ih =>
    let f := fun w : Bits (n+2) => totalScore m n (cut (n+1) w)
    let g := finalEdge m n
    have decomposition : totalScore m (n+1)=f+g := by
      funext w
      simp only [f,g,totalScore,cut_succ,Pi.add_apply,finalEdge,append_score m cut cut_succ]
      ring
    have vf : variance (pathLaw m (n+1)) f=finiteFormula m n := by
      rw [← ih, ← self_cov, ← self_cov]
      exact right n _ _
    have fc : f=(fun w : Bits (n+2) => B m w.1)+oldEdges m cut n := by
      funext w
      simp only [f,totalScore,cut_succ,oldEdges,Pi.add_apply]
    rw [decomposition,var_sum,vf,final_var m left n,fc,cov_add,old_final_cov m cut cut_succ left edge n]
    change _ + 2*(covariance (pathLaw m (n+1)) (fun w => B m w.1) (fun w => lastEdge m w.1 n w.2) + _) = _
    rw [initial,formula_step]
end
theorem finite_from_score (m : BinaryModel)
    (score : ∀ n (w : Bits (n+1)), -logTwo (pathLaw m n w) = B m w.1 + edgeSum m w.1 n w.2)
    (n : ℕ) : blockVariance m n = finiteFormula m n :=
  by
    unfold blockVariance
    simp_rw [score]
    exact score_variance m dropLast (fun _ _ => rfl) (left_cov m) (right_cov m)
      (initial_lag m) (edge_lag m) n

#print axioms finite_from_score
end BlockHierarchy.Varentropy