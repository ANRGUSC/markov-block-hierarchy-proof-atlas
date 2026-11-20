import ChannelEquality
import Lossless

open scoped BigOperators

namespace BlockHierarchy.PairChannel

/-- Applying the signed inverse to an arbitrary convolved four-word law recovers it. -/
theorem recover (u : ℝ) (h0 : 0 ≤ u) (h1 : u < 1) (t : Word → ℝ) (y : Word) :
    ∑ x, (∑ w, t w * backward u x w) * ((-u)^hamming x y) / (1-u)^2 = t y := by
  have plus : 1+u ≠ 0 := by linarith
  have minus := (sub_pos.mpr h1).ne'
  simp_rw [word_sum]
  obtain ⟨a,b⟩ := y
  cases a <;> cases b <;> norm_num [backward,hamming] <;>
    field_simp [plus,minus] <;> ring

theorem unique_positive (A B C D : ℝ) (mass : A+2*C+B=1) (hD : 0 < D) (half : D < 1/2)
    (feasible : ∀ y, 0 ≤ prior A B C (D/(1-D)) y)
    (t : Word → ℝ) (opt : IsOptimalAt (law A B C) t D) :
    t = prior A B C (D/(1-D)) := by
  let u := D/(1-D)
  let q := prior A B C u
  have hd : 0 < 1-D := by linarith
  have hu : 0 < u := div_pos hD hd
  have hu1 : u < 1 := (div_lt_iff₀ hd).mpr (by linarith)
  have plus : 0 < 1+u := by linarith
  have hcost : 2*u/(1+u) = 2*D := by
    apply (div_eq_iff plus.ne').mpr
    have h : u*(1-D)=D := div_mul_cancel₀ _ hd.ne'
    nlinarith only [h]
  have hK (x y : Word) : 0 < backward u x y := div_pos (pow_pos hu _) (sq_pos_of_pos plus)
  have ker (x y : Word) : Real.log (backward u x y) =
      Real.log u * (hamming x y : ℝ) - 2*Real.log (1+u) := by
    rw [backward,Real.log_div (pow_pos hu _).ne' (sq_pos_of_pos plus).ne',Real.log_pow,Real.log_pow]
    push_cast
    ring
  have sumP : ∑ x, law A B C x = 1 := by rw [word_sum]; change A+C+C+B=1; linarith
  have rows := inverse A B C u hu.le hu1
  have cols := column_sum u hu.le
  have total := prior_total A B C u hu1 mass
  have attained := (joint_cost u hu.le q total).trans hcost
  obtain ⟨J,hJ,src,dst,cost,minimal⟩ := opt
  have cmp := minimal q (fun x y => q y*backward u x y)
    (fun x y => mul_nonneg (feasible y) (hK x y).le) rows
    (fun y => by rw [←Finset.mul_sum,cols,mul_one]) attained.le
  have factor := Channel.optimal_joint_factors _ q t _ J _ _ _ (Real.log_nonpos hu.le hu1.le)
    hK hJ rows sumP cols ker src dst (cost.trans attained.symm).le cmp
  funext y
  calc t y = _ := (recover u hu.le hu1 t y).symm
       _ = q y := by
         simp_rw [← factor, src, ← rows]
         exact recover u hu.le hu1 q y

end BlockHierarchy.PairChannel
