import BlockHierarchy.Three.ConstantColumns

namespace BlockHierarchy.Three

noncomputable def middleH (u : ℝ) := (1+u)*(1+u+u^2)/2
noncomputable def pairWeight (p u : ℝ) := (p*middleH u/(1+p)-beta u)/(alpha u-beta u)
noncomputable def sixPrior (p u : ℝ) := prior (1-2*pairWeight p u) (2*pairWeight p u) 0
noncomputable def sixNormal (p u : ℝ) :=
  classValue ((1-p)*middleH u/(1+p)) (p*middleH u/(1+p)) (beta u)

theorem middleH_eq (u : ℝ) : middleH u = alpha u+2*beta u := by
  unfold middleH alpha beta
  ring

theorem six_weights {p u : ℝ} (hp : 0 < p) (half : p < 1/2)
    (hu : 0 ≤ u) (hs : u < secondU p) :
    0 < pairWeight p u ∧ pairWeight p u < 1-2*pairWeight p u := by
  obtain ⟨_,_,_,hf,h12,h1,_,eq⟩ := thresholds hp half
  let t := secondU p
  have ht : 0 < t := hf.trans h12
  have lt : u < t := hs
  have mulsmall : t*u < 1 := by
    have a := mul_lt_mul_of_pos_left (hs.trans h1) ht
    linarith only [a,h1]
  have diff := mul_pos (sub_pos.mpr lt) (sub_pos.mpr mulsmall)
  have comp : u < p*(1+u^2) := by
    rw [← eq]
    change u < t/(1+t^2)*(1+u^2)
    rw [div_mul_eq_mul_div,lt_div_iff₀ (by positivity)]
    nlinarith only [diff]
  have g := sub_pos.mpr (alpha_gt_beta hu (hs.trans h1))
  have pos : 0 < 1+p := by positivity
  have hpH : 0 < middleH u := by unfold middleH; positivity
  have em : pairWeight p u*(alpha u-beta u)=p*middleH u/(1+p)-beta u :=
    div_mul_cancel₀ _ g.ne'
  constructor
  · apply div_pos _ g
    apply sub_pos.mpr
    apply (lt_div_iff₀ pos).mpr
    unfold beta middleH
    nlinarith only [mul_pos (sub_pos.mpr comp) (show 0 < 1+u by positivity)]
  · apply (lt_of_mul_lt_mul_right (a := alpha u-beta u) ?_ g.le)
    have ab := middleH_eq u
    have ee := congrArg (fun v : ℝ => v*(1+p)) em
    rw [sub_mul,div_mul_cancel₀ _ pos.ne'] at ee
    have benefit := mul_pos (show 0 < 1-2*p by linarith) hpH
    apply (lt_of_mul_lt_mul_right (a := 1+p) ?_ pos.le)
    nlinarith only [ee,ab,congrArg (fun v : ℝ => v*p) ab,benefit]

theorem six_normalizer {p u : ℝ} (hp : 0 < p) (hu : 0 ≤ u) (h1 : u < 1) (x : Word) :
    normalizer (sixPrior p u) u x = sixNormal p u x := by
  have g := sub_pos.mpr (alpha_gt_beta hu h1)
  have pos : 0 < 1+p := by positivity
  have em : (alpha u-beta u)*pairWeight p u=p*middleH u/(1+p)-beta u :=
    (mul_comm _ _).trans (div_mul_cancel₀ _ g.ne')
  have e0 : beta u+(alpha u-beta u)*(1-2*pairWeight p u)=(1-p)*middleH u/(1+p) := by
    calc
      _ = middleH u-2*(p*middleH u/(1+p)) := by
        nlinarith only [em,middleH_eq u]
      _ = _ := by field_simp [pos.ne']; ring
  have norm : (1-2*pairWeight p u)+2*pairWeight p u+0=1 := by ring
  rw [sixPrior,class_normalizer,norm,mul_one]
  obtain ⟨i,j,k⟩ := x
  cases i <;> cases j <;> cases k <;>
    simp [sixNormal,classValue,e0,em]

end BlockHierarchy.Three
