import BlockHierarchy.Three.OperatingPoint

open scoped BigOperators
namespace BlockHierarchy.Three

noncomputable def binaryEntropy (p : ℝ) := -(p*logTwo p+(1-p)*logTwo (1-p))
noncomputable def nu (p : ℝ) := p*(1-p)*logTwo ((1-p)/p)^2

theorem markov_mass (p : ℝ) : ∑ x, markov p x = 1 := by
  rw [word_sum]
  norm_num [markov,step]
  ring

theorem log_source {p : ℝ} (hp : 0 < p) (ph : p < 1/2) (x : Word) :
    logTwo (markov p x) = classValue (2*logTwo (1-p)-1)
      (logTwo p+logTwo (1-p)-1) (2*logTwo p-1) x := by
  have m : 0 < 1-p := by linarith
  have two := (Real.log_pos (show (1:ℝ)<2 by norm_num)).ne'
  rw [markov_classes]
  obtain ⟨i,j,k⟩ := x
  cases i <;> cases j <;> cases k <;>
    simp only [classValue,reduceCtorEq,↓reduceIte,logTwo,
      Real.log_div (sq_pos_of_pos m).ne' (by norm_num : (2:ℝ)≠0),
      Real.log_div (sq_pos_of_pos hp).ne' (by norm_num : (2:ℝ)≠0),
      Real.log_div (mul_pos hp m).ne' (by norm_num : (2:ℝ)≠0),
      Real.log_pow,Real.log_mul hp.ne' m.ne'] <;> push_cast <;>
    field_simp [two] <;> ring

theorem source_moments {p : ℝ} (hp : 0 < p) (ph : p < 1/2) :
    -mean (markov p) (fun x => logTwo (markov p x))=1+2*binaryEntropy p ∧
    variance (markov p) (fun x => -logTwo (markov p x))=2*nu p := by
  have m : 0 < 1-p := by linarith
  have rat : logTwo ((1-p)/p)=logTwo (1-p)-logTwo p := by
    unfold logTwo
    rw [Real.log_div m.ne' hp.ne',sub_div]
  simp_rw [log_source hp ph]
  constructor
  · unfold mean binaryEntropy
    rw [class_expectation]
    ring
  · have e := funext (class_map (fun x => -x) (2*logTwo (1-p)-1)
        (logTwo p+logTwo (1-p)-1) (2*logTwo p-1))
    rw [e,class_var,nu,rat]
    unfold classVariance classMean
    ring

theorem entropy_tilt_values {p D : ℝ} (hp : 0 < p) (ph : p < 1/2)
    (hd : 0 ≤ D) (dh : D < 1/2) :
    let u := D/(1-D)
    let z := fun x => (1+u)^3*markov p x
    3*D*logTwo u - mean (markov p) (fun x => logTwo (z x)) =
      1+2*binaryEntropy p-3*binaryEntropy D ∧ tilted p (3*D) u z=2*nu p := by
  let u := D/(1-D)
  have dm : 0 < 1-D := by linarith
  have u0 : 0 ≤ u := div_nonneg hd dm.le
  have u1 : 0 < 1+u := by linarith
  have lz (x : Word) : logTwo ((1+u)^3*markov p x) =
      3*logTwo (1+u)+logTwo (markov p x) := by
    unfold logTwo
    rw [Real.log_mul (pow_pos u1 _).ne' (source_pos hp ph x).ne',Real.log_pow]
    push_cast
    ring
  have add : 1+u = 1/(1-D) := by dsimp [u]; field_simp [dm.ne']; ring
  have lplus : logTwo (1+u) = -logTwo (1-D) := by
    unfold logTwo
    rw [add,Real.log_div one_ne_zero dm.ne',Real.log_one]
    ring
  obtain ⟨avg,var⟩ := source_moments hp ph
  have factor : D*logTwo u-logTwo (1+u) = -binaryEntropy D := by
    rcases eq_or_lt_of_le hd with e|h
    · subst D; simp [u,logTwo,binaryEntropy]
    · have lu : logTwo u=logTwo D-logTwo (1-D) := by
        unfold u logTwo; rw [Real.log_div h.ne' dm.ne',sub_div]
      rw [lu,lplus]; unfold binaryEntropy; ring
  change 3*D*logTwo u-mean (markov p) (fun x => logTwo ((1+u)^3*markov p x))=_ ∧ _
  constructor
  · have a : mean (markov p) (fun x => logTwo ((1+u)^3*markov p x)) =
        3*logTwo (1+u)+mean (markov p) (fun x => logTwo (markov p x)) := by
      simp [mean,lz,mul_add,Finset.sum_add_distrib,←Finset.sum_mul,markov_mass]
    rw [a]
    linarith only [avg,factor]
  · change variance (markov p) (fun x => 3*D*logTwo u-logTwo ((1+u)^3*markov p x))=_
    have f (x : Word) : 3*D*logTwo u-logTwo ((1+u)^3*markov p x) =
        (3*D*logTwo u-3*logTwo (1+u))+(-logTwo (markov p x)) := by rw [lz]; ring
    simp_rw [f]
    rw [variance_shift _ _ (markov_mass p),var]

end BlockHierarchy.Three
