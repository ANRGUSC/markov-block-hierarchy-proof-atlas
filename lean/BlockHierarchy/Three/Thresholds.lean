import BlockHierarchy.Three.Classes
import Mathlib.Tactic.LinearCombination

namespace BlockHierarchy.Three

noncomputable def criticalD (p : ℝ) := (1-Real.sqrt (1-4*p^2))/2
noncomputable def firstU (p : ℝ) := criticalD p / (1-criticalD p)
noncomputable def secondU (p : ℝ) := 2*p/(1+Real.sqrt (1-4*p^2))

theorem thresholds {p : ℝ} (hp : 0 < p) (half : p < 1/2) :
    0 < criticalD p ∧ criticalD p < 1/2 ∧
    criticalD p*(1-criticalD p)=p^2 ∧
    0 < firstU p ∧ firstU p < secondU p ∧ secondU p < 1 ∧
    firstU p=(secondU p)^2 ∧ secondU p/(1+(secondU p)^2)=p := by
  let r := Real.sqrt (1-4*p^2)
  have rad : 0 < 1-4*p^2 := by
    nlinarith only [mul_pos (show 0 < 1-2*p by linarith) (show 0 < 1+2*p by linarith)]
  have rpos : 0 < r := Real.sqrt_pos.mpr rad
  have rsq : r^2 = 1-4*p^2 := Real.sq_sqrt rad.le
  have rlt : r < 1 := by nlinarith only [rsq, sq_pos_of_pos hp, sq_nonneg (r-1)]
  have D : criticalD p = (1-r)/2 := rfl
  have Dpos : 0 < criticalD p := by rw [D]; linarith
  have Dlt : criticalD p < 1/2 := by rw [D]; linarith
  have Dprod : criticalD p*(1-criticalD p)=p^2 := by rw [D]; nlinarith only [rsq]
  have nonzero : 1+r ≠ 0 := by linarith
  have first : firstU p=(1-r)/(1+r) := by
    unfold firstU
    rw [D]
    field_simp [nonzero,show (2:ℝ)-(1-r) ≠ 0 by linarith]
    <;> ring
  have second : secondU p = 2*p/(1+r) := rfl
  have upos : 0 < secondU p := by rw [second]; positivity
  have ult : secondU p < 1 := by rw [second,div_lt_one (by linarith)]; linarith
  have identity : firstU p=(secondU p)^2 := by
    rw [first,second,div_pow]
    field_simp [nonzero]
    <;> nlinarith only [rsq]
  have sep : firstU p < secondU p := by
    rw [identity]
    nlinarith only [mul_pos upos (sub_pos.mpr ult)]
  refine ⟨Dpos,Dlt,Dprod,identity.symm ▸ sq_pos_of_pos upos,sep,ult,identity,?_⟩
  apply (div_eq_iff (by positivity : 1+(secondU p)^2 ≠ 0)).mpr
  rw [← identity,first,second]
  field_simp [nonzero]
  <;> ring

end BlockHierarchy.Three

