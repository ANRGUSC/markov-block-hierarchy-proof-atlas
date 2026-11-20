import PairChannel

open scoped BigOperators

namespace BlockHierarchy.ReducedPair
open PairChannel

/-- Reproduction probabilities with only the constant words active. -/
noncomputable def prior (A B u : ℝ) : Word → ℝ :=
  law ((A-B*u^2)/((A+B)*(1-u^2))) ((B-A*u^2)/((A+B)*(1-u^2))) 0

noncomputable def Z (A B u : ℝ) := law (A*(1+u^2)/(A+B)) (B*(1+u^2)/(A+B)) u

theorem normalizers (A B u : ℝ) (hA : 0 < A) (hB : 0 < B) (hu : 0 < u) (hlt : u < 1)
    (x : Word) : ∑ y, prior A B u y*u^hamming x y = Z A B u x := by
  have hs := (add_pos hA hB).ne'
  have hd : 1-u^2 ≠ 0 := by
    have h := mul_pos (sub_pos.mpr hlt) (show 0 < 1+u by linarith)
    intro he; nlinarith only [h,he]
  rw [word_sum]
  obtain ⟨i,j⟩ := x
  cases i <;> cases j <;> norm_num [prior,Z,law,hamming] <;> field_simp [hs,hd] <;> ring

/-- The inactive column inequality factors into the two roots in the paper. -/
theorem inactive_column_test {S C x : ℝ} (spos : 0 < S) (mass : S+2*C=1)
    (hx : 0 < x) (first : C/S ≤ x) (last : x ≤ 1/2) : 2*S*x+C/x ≤ 1 := by
  have hf : 2*S*x^2-x+C = (2*x-1)*(S*x-C) := by
    nlinarith only [congrArg (fun a : ℝ => a*x) mass]
  have f : (2*x-1)*(S*x-C) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith)
    (by have h := (div_le_iff₀ spos).mp first; linarith [mul_comm x S])
  have h := div_mul_cancel₀ C hx.ne'
  by_contra! neg
  nlinarith only [hf,f,h,mul_pos (sub_pos.mpr neg) hx]

theorem columns (A B C u : ℝ) (hA : 0 < A) (hB : 0 < B) (hu : 0 < u)
    (mass : A+2*C+B=1) (y : Word) :
    ∑ x, law A B C x * u^hamming x y / Z A B u x =
      (if y.1 = y.2 then 1 else 2*(A+B)*(u/(1+u^2))+C/(u/(1+u^2))) := by
  have hs := (add_pos hA hB).ne'
  have h2 : 1+u^2 ≠ 0 := by nlinarith only [sq_nonneg u]
  rw [word_sum]
  obtain ⟨i,j⟩ := y
  cases i <;> cases j <;> norm_num [Z,law,hamming] <;>
    field_simp [hs,h2,hA.ne',hB.ne',hu.ne'] <;> nlinarith only [mass]

end BlockHierarchy.ReducedPair
