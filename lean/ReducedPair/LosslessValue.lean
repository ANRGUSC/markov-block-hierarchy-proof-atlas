import ReducedPair.RateStatement
import FirstChange

open scoped BigOperators
namespace BlockHierarchy
open PairChannel

theorem lossless_value (P : Word → ℝ) (hP : ∀ x, 0 ≤ P x) :
    RateAt P 0 ((-mean P (fun x => Real.log (P x)))/Real.log 2) := by
  obtain ⟨J,hJ,src,dst,cost,optimal⟩ := lossless_optimal P hP
  obtain ⟨same,_⟩ := zero_cost_marginals P P J hJ src dst cost.le
  refine ⟨P,J,⟨hJ,src,dst,cost.le,optimal⟩,?_⟩
  apply congrArg (fun v : ℝ => v / Real.log 2)
  rw [same]
  unfold Channel.info mean
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy; simp [Ne.symm hy]
  · simp

theorem zero_kernel (x y : Word) : (0 : ℝ)^hamming x y = if x=y then 1 else 0 := by
  obtain ⟨a,b⟩ := x
  obtain ⟨i,j⟩ := y
  cases a <;> cases b <;> cases i <;> cases j <;> norm_num [hamming]

theorem lossless_point (m : BinaryModel) : GibbsPoint m.source m.source 0 0 m.source := by
  obtain ⟨J,nonneg,src,dst,cap,minimal⟩ := lossless_optimal m.source (fun x => (m.positive_source x).le)
  obtain ⟨shape,_⟩ := zero_cost_marginals _ _ _ nonneg src dst cap.le
  have joint : (fun x y => m.source y*(m.source x*(0 : ℝ)^hamming x y / m.source x)) = J := by
    rw [shape]
    funext x y
    by_cases h : x=y
    · subst y; simp [zero_kernel,(m.positive_source x).ne']
    · simp [zero_kernel,h]
  refine ⟨?_,?_⟩
  · intro x
    simp only [zero_kernel,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true]
  · rw [joint]
    exact ⟨nonneg,src,dst,cap.le,minimal⟩

end BlockHierarchy
