import BlockHierarchy.Three.Thresholds

open scoped BigOperators

namespace BlockHierarchy.Three

theorem alpha_gt_beta {u : ℝ} (hu : 0 ≤ u) (h1 : u < 1) : beta u < alpha u := by
  have h := mul_pos (sq_pos_of_pos (sub_pos.mpr h1)) (show 0 < 1+u by linarith)
  unfold alpha beta
  nlinarith only [h]

theorem two_word_test {p u : ℝ} (hp : 0 < p) (half : p < 1/2) (hs : secondU p ≤ u)
    (h1 : u < 1) : p*alpha u ≤ (1-p)*beta u := by
  obtain ⟨_,_,_,hf,h12,_,_,eq⟩ := thresholds hp half
  let t := secondU p
  have ht : 0 < t := hf.trans h12
  have order : t ≤ u := hs
  have hu := ht.trans_le order
  have mulsmall : t*u < 1 := by
    have a := mul_lt_mul_of_pos_left h1 ht
    nlinarith only [a,order,h1]
  have diff := mul_nonneg (sub_nonneg.mpr order) (sub_nonneg.mpr mulsmall.le)
  have den : 0 < 1+t^2 := by positivity
  have comp : p*(1+u^2) ≤ u := by
    rw [← eq]
    change t/(1+t^2)*(1+u^2) ≤ u
    rw [div_mul_eq_mul_div,div_le_iff₀ den]
    nlinarith only [diff]
  have diff' := mul_nonneg (sub_nonneg.mpr comp) (show 0 ≤ 1+u by linarith)
  unfold alpha beta
  nlinarith only [diff']

noncomputable def twoNormal (u : ℝ) := classValue (alpha u) (beta u) (beta u)

theorem constant_normalizer (u : ℝ) (x : Word) :
    normalizer (prior 1 0 0) u x = twoNormal u x := by
  rw [class_normalizer]
  obtain ⟨a,b,c⟩ := x
  cases a <;> cases b <;> cases c <;> simp [classValue, twoNormal] <;> ring

noncomputable def dualColumn (p u : ℝ) (z : Word → ℝ) (y : Word) :=
  ∑ x, markov p x / z x * u^(hamming x y)

theorem constant_columns {p u : ℝ} (hp : 0 < p) (half : p < 1/2)
    (hs : secondU p ≤ u) (h1 : u < 1) (y : Word) :
    dualColumn p u (twoNormal u) y ≤ 1 ∧
    (prior 1 0 0 y ≠ 0 → dualColumn p u (twoNormal u) y = 1) := by
  obtain ⟨_,_,_,hf,h12,_,_,_⟩ := thresholds hp half
  have hu := (hf.trans h12).trans_le hs
  have ha : 0 < alpha u := by unfold alpha; positivity
  have hb : 0 < beta u := by unfold beta; positivity
  have hgap := alpha_gt_beta hu.le h1
  let A := (1-p)^2 / alpha u
  let B := p*(1-p) / beta u
  let C := p^2 / beta u
  have law (x : Word) : markov p x/twoNormal u x = prior A (2*B) C x := by
    rw [markov_classes]
    obtain ⟨i,j,k⟩ := x
    cases i <;> cases j <;> cases k <;>
      norm_num [twoNormal,prior,classValue,A,B,C] <;> ring
  have bound : B ≤ A := by
    apply (div_le_div_iff₀ hb ha).mpr
    have test := mul_le_mul_of_nonneg_left (two_word_test hp half hs h1) (show 0 ≤ 1-p by linarith)
    nlinarith only [test]
  have small : C ≤ B := by
    apply div_le_div_of_nonneg_right _ hb.le
    nlinarith only [mul_nonneg hp.le (show 0 ≤ 1-2*p by linarith)]
  have total : beta u*(A+2*B+C)+(alpha u-beta u)*A=1 := by
    dsimp [A,B,C]
    field_simp [ha.ne',hb.ne']
    <;> ring
  unfold dualColumn
  simp_rw [law]
  rw [class_column]
  have val : classValue A (2*B/2) C y ≤ A := by
    obtain ⟨i,j,k⟩ := y
    cases i <;> cases j <;> cases k <;> simp [classValue] <;> first | exact bound | exact small.trans bound
  constructor
  · rw [← total]
    exact add_le_add_right (mul_le_mul_of_nonneg_left val (sub_nonneg.mpr hgap.le)) _
  · intro active
    have e : classValue A (2*B/2) C y=A := by
      obtain ⟨i,j,k⟩ := y
      cases i <;> cases j <;> cases k <;> simp [prior,classValue] at active ⊢
    rwa [e]

end BlockHierarchy.Three
