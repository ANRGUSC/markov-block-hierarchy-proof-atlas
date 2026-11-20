import BlockHierarchy.Converse.BSCFacts
import BlockHierarchy.Converse.BackwardRate
import BlockHierarchy.Converse.MarkovEntropy

open Filter Topology
open scoped BigOperators
namespace BlockHierarchy.Converse
open Cut Varentropy VarianceLimit

/-- Exact finite constrained rate at a normalized backward Bernoulli point. -/
theorem rate_backward {p D : ℝ} (hp : 0<p) (ph : p<1) (hd : 0<D) (dh : D<1/2)
    (n : ℕ) {q : Word n → ℝ} (hq : IsPrior q)
    (src : ∀ x, (∑ y, q y*bsc D (n+1) x y)=mass p n x) :
    constrainedRate p n D =
      (Real.log 2+n*binaryEntropyNats p-((n:ℝ)+1)*binaryEntropyNats D)/(((n:ℝ)+1)*Real.log 2) := by
  have d1 : D<1 := by linarith
  have pp : 0<1-D := by linarith
  let k : ℝ := n+1
  let s := Real.log D-Real.log (1-D)
  let z := -k*Real.log (1-D)
  have hs : s≤0 := sub_nonpos.mpr (Real.log_le_log hd (by linarith))
  have logs (x y : Word n) : Real.log (bsc D (n+1) x y)=s*(distance n x y:ℝ)-z := by
    rw [bsc_log hd d1]
    simp [s,z,k,distance]
  have cost (y : Word n) : ∑ x, bsc D (n+1) x y*(distance n x y:ℝ)=k*D := by
    simpa [k,distance] using bsc_cost D (n+1) y
  obtain ⟨lower,W,hw,cw,iw⟩ := backward_rate_pair (mass p n) q (distance n) (bsc D (n+1)) s z (k*D)
    ⟨fun x => (mass_pos hp ph n x).le,mass_sum hp ph n⟩ (mass_pos hp ph n) hq
    (bsc_positive hd d1 (n+1)) (bsc_normal D (n+1)) src logs cost hs
  have val : -mean (mass p n) (fun x => Real.log (mass p n x))+s*(k*D)-z =
      Real.log 2+n*binaryEntropyNats p-k*binaryEntropyNats D := by
    rw [markov_entropy hp ph]; unfold s z binaryEntropyNats; ring
  rw [val] at iw
  have den : 0 < k*Real.log 2 := mul_pos (by dsimp [k]; positivity) (Real.log_pos (by norm_num))
  unfold constrainedRate
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨W,hw,cw.le,congrArg (·/(k*Real.log 2)) iw.symm⟩
  · rintro a ⟨V,hV,cv,rfl⟩
    have h := lower V hV cv
    rw [val] at h
    exact div_le_div_of_nonneg_right h den.le

#print axioms rate_backward
end BlockHierarchy.Converse
