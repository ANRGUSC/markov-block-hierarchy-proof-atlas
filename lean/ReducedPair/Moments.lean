import ReducedPair

open scoped BigOperators
namespace BlockHierarchy

noncomputable def binaryEntropyNats (p : ℝ) := -(p*Real.log p+(1-p)*Real.log (1-p))

noncomputable def logTwo (p : ℝ) := Real.log p / Real.log 2

noncomputable def mean {X : Type*} [Fintype X] (P f : X → ℝ) := ∑ x, P x*f x

noncomputable def variance {X : Type*} [Fintype X] (P f : X → ℝ) :=
  ∑ x, P x*(f x-mean P f)^2

theorem variance_shift {X : Type*} [Fintype X] (P f : X → ℝ) (mass : ∑ x, P x = 1) (a : ℝ) :
    variance P (fun x => a+f x) = variance P f := by
  have avg : mean P (fun x => a+f x) = a+mean P f := by
    simp [mean,mul_add,Finset.sum_add_distrib,←Finset.sum_mul,mass]
  unfold variance
  rw [avg]
  apply Finset.sum_congr rfl
  intro x _
  ring

namespace ReducedPair
open PairChannel

def classVariance (A B C l₀ lₜ l₁ : ℝ) :=
  let mean := A*l₀+2*C*lₜ+B*l₁
  A*(l₀-mean)^2+2*C*(lₜ-mean)^2+B*(l₁-mean)^2

theorem reduced_value {A B C D : ℝ} (hA : 0 < A) (hB : 0 < B)
    (δ u : ℝ) (hd : 0 < δ) (hl : δ < 1)
    (scale : D-C = (A+B)*δ) (square : u^2 = δ/(1-δ)) :
    2*D*Real.log u - mean (law A B C) (fun x => Real.log (Z A B u x)) =
      (A+B)*(binaryEntropyNats (B/(A+B))-binaryEntropyNats δ) := by
  have hs := add_pos hA hB
  have ht := sub_pos.mpr hl
  have inv : 1+u^2 = 1/(1-δ) := by rw [square]; field_simp [ht.ne']; ring
  have logu : 2*Real.log u = Real.log δ-Real.log (1-δ) := by
    have h := congrArg Real.log square
    simpa [Real.log_pow,Real.log_div hd.ne' ht.ne'] using h
  have logx : Real.log (1+u^2) = -Real.log (1-δ) := by rw [inv,Real.log_div one_ne_zero ht.ne',Real.log_one,zero_sub]
  have complement : 1-B/(A+B)=A/(A+B) := by field_simp [hs.ne']; ring
  have norm (v : ℝ) (hv : 0<v) : Real.log (v*(1+u^2)/(A+B)) =
      Real.log (v/(A+B))-Real.log (1-δ) := by
    have h2 : 0 < 1+u^2 := by nlinarith only [sq_nonneg u]
    rw [Real.log_div (mul_pos hv h2).ne' hs.ne',Real.log_mul hv.ne' h2.ne',logx,
      Real.log_div hv.ne' hs.ne']
    ring
  unfold mean binaryEntropyNats
  rw [word_sum]
  simp only [Z,law,norm A hA,norm B hB,complement]
  have ha := div_mul_cancel₀ A hs.ne'
  have hb := div_mul_cancel₀ B hs.ne'
  calc
    _ = (D-C)*(2*Real.log u) + (A+B)*Real.log (1-δ) -
        A*Real.log (A/(A+B))-B*Real.log (B/(A+B)) := by ring
    _ = _ := by
      rw [scale,logu]
      nlinarith only [congrArg (fun v : ℝ => v*Real.log (A/(A+B))) ha,
        congrArg (fun v : ℝ => v*Real.log (B/(A+B))) hb]

end ReducedPair
end BlockHierarchy
