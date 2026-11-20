import BlockHierarchy.Three.OperatingPoint
import BlockHierarchy.Three.Inverse

open scoped BigOperators
namespace BlockHierarchy.Three

theorem constant_cost {u : ℝ} (p : ℝ) (hu : 0 < u) :
    Channel.cost (fun x y => (hamming x y : ℝ))
      (FiniteRD.joint (markov p) (twoNormal u) (prior 1 0 0) hamming u) = constantCost p u := by
  have per (x : Word) : weightedDistance (prior 1 0 0) u x/twoNormal u x =
      classValue (3*u^3/(1+u^3)) (1+u/(1+u)) (1+u/(1+u)) x := by
    rw [class_distance]
    obtain ⟨i,j,k⟩ := x
    cases i <;> cases j <;> cases k <;>
      norm_num [alphaCost,betaCost,twoNormal,alpha,beta,classValue] <;>
      field_simp [show 0 < 1+u^3 by positivity, show 0 < u+u^2 by positivity,
        show 0 < 1+u by positivity] <;> ring
  rw [operating_cost]
  simp_rw [per]
  rw [class_expectation]
  unfold constantCost
  ring

theorem two_class_var {u : ℝ} (p : ℝ) (hu : 0 < u) (b : ℝ) :
    tilted p b u (twoNormal u) =
      (1-p)^2*(1-(1-p)^2)*logTwo (alpha u/beta u)^2 := by
  have ha : 0 < alpha u := by unfold alpha; positivity
  have hb : 0 < beta u := by unfold beta; positivity
  have eq : logTwo (alpha u/beta u)=logTwo (alpha u)-logTwo (beta u) := by
    unfold logTwo
    rw [Real.log_div ha.ne' hb.ne',sub_div]
  rw [twoNormal,class_tilt,eq]
  unfold classVariance classMean
  ring

/-- Two active words, exact distortion, optimality against every feasible joint law,
and the attained information and tilted variance in the units of the manuscript. -/
theorem constant_branch {p D : ℝ} (hp : 0 < p) (half : p < 1/2)
    (lower : secondD p ≤ D) (upper : D < 1/2) :
    ∃ u, u ∈ Set.Ico (secondU p) 1 ∧ constantCost p u=3*D ∧
      let q := prior 1 0 0
      let z := twoNormal u
      let J := FiniteRD.joint (markov p) z q hamming u
      (∀ x, normalizer q u x=z x) ∧ FiniteRD.Optimal (markov p) q hamming J (3*D) ∧
      Channel.info (markov p) q J/Real.log 2 =
        3*D*logTwo u-classMean p (logTwo (alpha u)) (logTwo (beta u)) (logTwo (beta u)) ∧
      tilted p (3*D) u z = (1-p)^2*(1-(1-p)^2)*logTwo (alpha u/beta u)^2 := by
  obtain ⟨u,⟨hu,eq⟩,_⟩ := constant_inverse hp half lower upper
  obtain ⟨_,_,_,hf,h12,_,_,_⟩ := thresholds hp half
  have up := ((hf.trans h12).trans_le hu.1)
  have ha : 0 < alpha u := by unfold alpha; positivity
  have hb : 0 < beta u := by unfold beta; positivity
  have hz (x : Word) : 0 < twoNormal u x := by
    unfold twoNormal classValue
    split <;> split <;> assumption
  have hq (y : Word) : 0 ≤ prior 1 0 0 y := by
    unfold prior classValue
    split <;> split <;> norm_num
  have cert := FiniteRD.certificate (d := hamming) (source_pos hp half) hz hq up hu.2.le
    (constant_normalizer u) (constant_columns hp half hu.1 hu.2) ((constant_cost p up).trans eq)
  exact ⟨u,hu,eq,constant_normalizer u,cert.1,
    cert.2.trans (by rw [twoNormal,class_log_mean]),two_class_var p up _⟩

end BlockHierarchy.Three
