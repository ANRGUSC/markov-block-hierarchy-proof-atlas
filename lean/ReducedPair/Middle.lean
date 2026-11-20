import ReducedPair.Optimal
import ReducedPair.GibbsValue

open scoped BigOperators
namespace BlockHierarchy.ReducedPair
open PairChannel

theorem three_class_variance (A B C D u : ℝ) (mass : A+2*C+B=1) :
    tiltedVariance (law A B C) D u (Z A B u) =
      classVariance A B C (-logTwo (A*(1+u^2)/(A+B))) (-logTwo u)
        (-logTwo (B*(1+u^2)/(A+B))) := by
  have total : ∑ x, law A B C x = 1 := by rw [word_sum]; change A+C+C+B=1; linarith
  unfold tiltedVariance
  simp only [sub_eq_add_neg]
  rw [variance_shift _ (fun x => -logTwo (Z A B u x)) total]
  unfold variance mean classVariance
  simp_rw [word_sum]
  simp only [Z,law]
  ring

theorem middle_branch {A B C r D : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (mass : A+2*C+B=1) (hr : 0 < r) (hr1 : r < 1/2) (root : r*(1-r)=C)
    (first : r ≤ D) (last : D < C+min A B) :
    let δ := (D-C)/(A+B)
    let u := Real.sqrt (δ/(1-δ))
    RateAt (law A B C) D (((A+B)*(binaryEntropyNats (B/(A+B))-binaryEntropyNats δ))/Real.log 2) ∧
    GibbsPoint (law A B C) (prior A B u) D u (Z A B u) ∧
    (∀ w, 0 < prior A B u w ↔ w.1=w.2) ∧
    tiltedVariance (law A B C) D u (Z A B u) =
      classVariance A B C (-logTwo (A*(1+u^2)/(A+B))) (-logTwo u)
        (-logTwo (B*(1+u^2)/(A+B))) := by
  let δ := (D-C)/(A+B)
  let u := Real.sqrt (δ/(1-δ))
  obtain ⟨hd,half,hu,hlt,ca,cb,_,_⟩ := branch_parameters hA hB hC mass hr hr1 root first last
  obtain ⟨point,cost⟩ := second_optimal hA hB hC mass hr hr1 root first last
  have pos : 0 < u := hu
  have small : u < 1 := hlt
  have hs := add_pos hA hB
  have h2 : 0 < 1+u^2 := by nlinarith only [sq_nonneg u]
  have hm : 0 < 1-u^2 := by nlinarith only [mul_pos (sub_pos.mpr small) (show 0 < 1+u by linarith)]
  have hp (w : Word) : 0 < law A B C w := by
    obtain ⟨i,j⟩ := w
    cases i <;> cases j <;> first | exact hA | exact hB | exact hC
  have hz (w : Word) : 0 < Z A B u w := by
    obtain ⟨i,j⟩ := w
    cases i <;> cases j <;> first | exact div_pos (mul_pos hA h2) hs
                                   | exact div_pos (mul_pos hB h2) hs | exact pos
  have value := gibbs_rate point pos hp hz cost
  have upper : δ < 1 := by change δ < 1/2 at half; linarith
  have scale : D-C = (A+B)*δ := by dsimp [δ]; field_simp [hs.ne']
  have square : u^2 = δ/(1-δ) := Real.sq_sqrt (div_nonneg hd.le (sub_nonneg.mpr upper.le))
  rw [reduced_value hA hB δ u hd upper scale square] at value
  refine ⟨value,point,?_,three_class_variance _ _ _ _ _ mass⟩
  rintro ⟨i,j⟩
  cases i <;> cases j
  · exact iff_of_true (div_pos ca (mul_pos hs hm)) rfl
  · simp [prior,law]
  · simp [prior,law]
  · exact iff_of_true (div_pos cb (mul_pos hs hm)) rfl

#print axioms middle_branch
end BlockHierarchy.ReducedPair
