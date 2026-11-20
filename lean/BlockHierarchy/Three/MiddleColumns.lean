import BlockHierarchy.Three.MiddleWeights

open scoped BigOperators
namespace BlockHierarchy.Three

theorem alternating_test {p u : ℝ} (hp : 0 < p) (half : p < 1/2)
    (lo : firstU p ≤ u) (hi : u < 1) : p^2*middleH u ≤ (1-p^2)*beta u := by
  obtain ⟨hd,hd',hroot,hf,_,_,_,_⟩ := thresholds hp half
  let t := firstU p
  have ht : 0 < t := hf
  have l : t ≤ u := lo
  have hu := ht.trans_le l
  have odds : t*(1-criticalD p)=criticalD p := div_mul_cancel₀ _ (by linarith)
  have eD : criticalD p*(1+t)=t := by linarith only [odds]
  have et : p^2*(1+t)^2=t := by
    calc
      _ = (criticalD p*(1+t))*((1-criticalD p)*(1+t)) := by rw [← hroot]; ring
      _ = t := by rw [eD,show (1-criticalD p)*(1+t)=1 by linarith only [eD]]; ring
  have small : t*u < 1 := by
    have := mul_lt_mul_of_pos_left hi ht
    linarith
  have incr := mul_nonneg (sub_nonneg.mpr l) (sub_nonneg.mpr small.le)
  have unc : p^2*(1+u)^2 ≤ u := by
    apply le_of_mul_le_mul_right (a := (1+t)^2) _ (by positivity)
    calc
      _ = (p^2*(1+t)^2)*(1+u)^2 := by ring
      _ ≤ _ := by rw [et]; nlinarith only [incr]
  have product := mul_nonneg (sub_nonneg.mpr unc) (show 0 ≤ 1+u by linarith)
  unfold middleH beta
  nlinarith only [product]

theorem middle_columns {p u : ℝ} (hp : 0 < p) (half : p < 1/2) (lo : firstU p ≤ u)
    (hi : u < 1) (y : Word) : dualColumn p u (sixNormal p u) y ≤ 1 ∧
      (sixPrior p u y ≠ 0 → dualColumn p u (sixNormal p u) y=1) := by
  obtain ⟨_,_,_,hf,_,_,_,_⟩ := thresholds hp half
  have hu := hf.trans_le lo
  have hH : 0 < middleH u := by unfold middleH; positivity
  have hb : 0 < beta u := by unfold beta; positivity
  have hpos : 0 < 1+p := by positivity
  have hm : 0 < 1-p := by linarith
  let A := (1-p^2)/middleH u
  let C := p^2/beta u
  have law (x : Word) : markov p x/sixNormal p u x=prior A (2*A) C x := by
    rw [markov_classes]
    obtain ⟨i,j,k⟩ := x
    cases i <;> cases j <;> cases k <;>
      norm_num [sixNormal,prior,classValue,A,C] <;>
      field_simp [hH.ne',hp.ne',hm.ne',hb.ne',hpos.ne'] <;> ring
  have test : C ≤ A := (div_le_div_iff₀ hb hH).mpr (alternating_test hp half lo hi)
  have total : beta u*(A+2*A+C)+(alpha u-beta u)*A=1 := by
    calc
      _ = middleH u*A+beta u*C := by rw [middleH_eq]; ring
      _ = 1 := by dsimp [A,C]; field_simp [hH.ne',hb.ne']; ring
  have smaller : classValue A (2*A/2) C y ≤ A := by
    obtain ⟨i,j,k⟩ := y
    cases i <;> cases j <;> cases k <;> simp [classValue,test]
  unfold dualColumn
  simp_rw [law]
  rw [class_column]
  constructor
  · rw [← total]
    exact add_le_add_right (mul_le_mul_of_nonneg_left smaller (sub_nonneg.mpr (alpha_gt_beta hu.le hi).le)) _
  · intro active
    have e : classValue A (2*A/2) C y=A := by
      obtain ⟨i,j,k⟩ := y
      cases i <;> cases j <;> cases k <;> simp [sixPrior,prior,classValue] at active ⊢
    rwa [e]

end BlockHierarchy.Three
