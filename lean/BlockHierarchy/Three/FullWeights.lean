import BlockHierarchy.Three.OperatingPoint

open scoped BigOperators
namespace BlockHierarchy.Three

noncomputable def fullWeight (D s : ℝ) := (s-D*(1-D))/(1-2*D)^2
noncomputable def fullPrior (p D : ℝ) :=
  prior (fullWeight D ((1-p)^2)) (2*fullWeight D (p*(1-p))) (fullWeight D (p^2))

theorem full_total {p D : ℝ} (half : D < 1/2) :
    fullWeight D ((1-p)^2)+2*fullWeight D (p*(1-p))+fullWeight D (p^2)=1 := by
  have nz : (1-2*D)^2 ≠ 0 := (sq_pos_of_pos (show 0 < 1-2*D by linarith)).ne'
  apply (mul_left_inj' nz).mp
  simp only [add_mul,mul_assoc,fullWeight,div_mul_cancel₀ _ nz,one_mul]
  ring

theorem full_support {p D : ℝ} (hp : 0 < p) (ph : p < 1/2) (bound : D ≤ criticalD p) :
    (∀ y, 0 ≤ fullPrior p D y) ∧
    (∀ y, 0 < fullPrior p D y ↔ flips y < 2 ∨ D < criticalD p) := by
  obtain ⟨hd,dh,eq,_,_,_,_,_⟩ := thresholds hp ph
  have hh := bound.trans_lt dh
  have gap : 0 < 1-D-criticalD p := by linarith
  have prod (h : D < criticalD p) : D*(1-D) < p^2 := by
    nlinarith only [eq,mul_pos (sub_pos.mpr h) gap]
  have le : D*(1-D) ≤ p^2 := by
    nlinarith only [eq,mul_nonneg (sub_nonneg.mpr bound) gap.le]
  have pos : 0 < (1-2*D)^2 := sq_pos_of_pos (by linarith)
  have m : p^2 < p*(1-p) := by nlinarith only [mul_pos hp (show 0 < 1-2*p by linarith)]
  have c : p*(1-p) < (1-p)^2 := by nlinarith only [mul_pos (show 0 < 1-p by linarith) (show 0 < 1-2*p by linarith)]
  have x0 : 0 < fullWeight D ((1-p)^2) := div_pos (sub_pos.mpr (le.trans_lt (m.trans c))) pos
  have x1 : 0 < fullWeight D (p*(1-p)) := div_pos (sub_pos.mpr (le.trans_lt m)) pos
  have x2 : 0 ≤ fullWeight D (p^2) := div_nonneg (sub_nonneg.mpr le) pos.le
  have iff2 : 0 < fullWeight D (p^2) ↔ D < criticalD p := by
    constructor
    · intro positive
      apply lt_of_le_of_ne bound
      intro e
      rw [fullWeight,e,eq,sub_self,zero_div] at positive
      exact lt_irrefl _ positive
    · intro h
      exact div_pos (sub_pos.mpr (prod h)) pos
  constructor <;> intro y <;> obtain ⟨i,j,k⟩ := y
  all_goals cases i <;> cases j <;> cases k <;>
    norm_num [fullPrior,prior,classValue,flips] <;>
    first | exact iff2 | linarith | positivity

theorem full_normalizer {p D : ℝ} (half : D < 1/2) (x : Word) :
    normalizer (fullPrior p D) (D/(1-D)) x=(1+D/(1-D))^3*markov p x := by
  let u := D/(1-D)
  have d : 0 < 1-D := by linarith
  have dd : 0 < 1-2*D := by linarith
  have id (s : ℝ) : beta u+(alpha u-beta u)*fullWeight D s=(1+u)^3*(s/2) := by
    have nz := (sq_pos_of_pos dd).ne'
    apply (mul_left_inj' nz).mp
    rw [add_mul,mul_assoc,fullWeight,div_mul_cancel₀ _ nz]
    dsimp [u,alpha,beta]
    field_simp [d.ne']
    ring
  rw [fullPrior,class_normalizer,full_total half,mul_one,markov_classes]
  obtain ⟨i,j,k⟩ := x
  cases i <;> cases j <;> cases k <;>
    simpa only [classValue,reduceCtorEq,↓reduceIte,mul_div_cancel_left₀ _ (by norm_num : (2:ℝ)≠0)]
      using id _

end BlockHierarchy.Three
