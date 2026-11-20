import BlockHierarchy.PairVariance.Statement

open scoped BigOperators
namespace BlockHierarchy.PairVariance

variable {I : Type*} [Fintype I] [LinearOrder I]

/-- For a normalized distribution, the variance of any common shifted
negative logarithm has the paper's pair-sum form. -/
theorem shifted_log_variance (s Z : I → ℝ) (total : ∑ i,s i=1) (pos : ∀ i,0<Z i) (c : ℝ) :
    variance s (fun i => c-logTwo (Z i))=pairSum s Z := by
  let f (i : I) := c-logTwo (Z i)
  let a (i : I) := f i-mean s f
  let V := variance s f
  let T (i j : I) := s i*s j*(a i-a j)^2
  have centered : ∑ i, s i*a i=0 := by
    simp only [a,mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,total,one_mul,mean,sub_self]
  have term (i j : I) : T i j=(s i*(a i)^2)*s j+s i*(s j*(a j)^2)-
      2*((s i*a i)*(s j*a j)) := by dsimp only [T]; ring
  have twice : (∑ i, ∑ j,T i j)=2*V := by
    simp only [term,Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum]
    change (∑ i, (s i*(a i)^2)*(∑ j, s j)) + (∑ i, s i*V) - 2*(∑ i, (s i*a i)*(∑ j,s j*a j)) = _
    rw [total,centered]
    simp only [mul_one,mul_zero,Finset.sum_const_zero,sub_zero,←Finset.sum_mul,total,one_mul]
    change V+V=2*V
    ring
  have same (i j : I) : T i j=T j i := by dsimp only [T]; ring
  let A (i j : I) := if i<j then T i j else 0
  have both (i j : I) : T i j=A i j+A j i := by
    rcases lt_trichotomy i j with h|rfl|h
    · simp [A,h,not_lt_of_gt h]
    · simp [A,T]
    · simp [A,h,not_lt_of_gt h,same i j]
  have split : (∑ i, ∑ j,T i j)=2*(∑ i,∑ j,A i j) := by
    calc
      _ = ∑ i, ∑ j, (A i j+A j i) := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        exact both i j
      _ = _ := by
        simp only [Finset.sum_add_distrib]
        rw [Finset.sum_comm (f := fun i j => A j i)]
        ring
  have ratio (i j : I) : a i-a j= -logTwo (Z i/Z j) := by
    dsimp only [a,f,logTwo]
    rw [Real.log_div (pos i).ne' (pos j).ne']
    ring
  have pairs : (∑ i,∑ j,A i j)=pairSum s Z := by
    unfold pairSum
    simp only [Finset.sum_filter,A,T,ratio,even_two.neg_pow]
  change V=_
  linarith only [twice,split,pairs]

end BlockHierarchy.PairVariance
