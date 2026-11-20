import FiniteChannel
import Mathlib.Tactic.FinCases

noncomputable section
namespace BlockHierarchy.Four

namespace Coefficients

def α (u : ℝ) := (1+u^4)/2
def β₄ (u : ℝ) := (u+u^3)/2
def χ (u : ℝ) := u^2

/-- Four-symbol source order and Hamming coefficients. -/
theorem class_order_and_kernel_gaps : (∀ p : ℝ, 0 < p → p < 1/2 →
  (1-p)^3 > p*(1-p)^2 ∧ p*(1-p)^2 > p^2*(1-p) ∧ p^2*(1-p) > p^3 ∧
    2*p*(1-p)^2 > 2*p^2*(1-p)) ∧ (∀ u : ℝ, 0 < u → u < 1 →
  0 < χ u ∧ χ u < β₄ u ∧ β₄ u < α u ∧ α u-χ u=(1-u^2)^2/2) := by
  constructor
  · intro p hp h
    have a : 0 < 1-p := by linarith
    have b : 0 < 1-2*p := by linarith
    have x := mul_pos (sq_pos_of_pos a) b
    have y := mul_pos (mul_pos hp a) b
    have z := mul_pos (sq_pos_of_pos hp) b
    exact ⟨by nlinarith only [x],by nlinarith only [y],by nlinarith only [z],by nlinarith only [y]⟩
  · intro u hu h
    have a := sub_pos.mpr h
    have b := mul_pos hu (sq_pos_of_pos a)
    have c := mul_pos (sq_pos_of_pos a) (show 0 < 1+u+u^2 by positivity)
    unfold χ β₄ α
    exact ⟨by positivity,by nlinarith only [b],by nlinarith only [c],by ring⟩

end Coefficients

namespace ConstantPair

abbrev Weight := Fin 5
def complementAverage (u : ℝ) (n : Weight) := (u^n.val+u^(4-n.val))/2
def errorMean (u : ℝ) (n : Weight) :=
  ((n.val:ℝ)*u^n.val+((4-n.val:ℕ):ℝ)*u^(4-n.val))/(u^n.val+u^(4-n.val))

/-- Four-symbol Hamming normalizers and conditional costs. -/
theorem normalizer_and_cost : (∀ (u : ℝ) (n : Weight), complementAverage u n =
  if n.val=0 ∨ n.val=4 then (1+u^4)/2 else if n.val=2 then u^2 else (u+u^3)/2) ∧ (∀ (u : ℝ), 0 < u → ∀ n : Weight, errorMean u n =
  if n.val=0 ∨ n.val=4 then 4*u^4/(1+u^4)
  else if n.val=2 then 2 else 1+2*u^2/(1+u^2)) := by
  constructor
  · intro u ⟨n, hn⟩
    have cases : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 := by omega
    rcases cases with h|h|h|h|h <;> subst n <;> norm_num [complementAverage] <;> ring
  · intro u hu ⟨n, hn⟩
    have cases : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 := by omega
    rcases cases with h|h|h|h|h <;> subst n <;> norm_num [errorMean] <;>
      field_simp [show 0 < u+u^3 by positivity, show 0 < u^3+u by positivity,
        show 0 < u^2+u^2 by positivity, show 0 < 1+u^2 by positivity,
        show 0 < 1+u^4 by positivity, show 0 < u^4+1 by positivity, hu.ne'] <;> ring

end ConstantPair

namespace OddAllocation

def η (s t m c : ℝ) := max (s/(m+c)) ((s+t)/(m+2*c))
def w (v l c : ℝ) := max 0 (v/l-c)

/-- Water-filling transition for the two odd classes. -/
theorem water_filling : (∀ s t m c : ℝ, 0 < t → t ≤ s → 0 ≤ m → 0 < c → t*(m+c) ≤ s*c →
  η s t m c = s/(m+c) ∧ w s (η s t m c) c = m ∧ w t (η s t m c) c=0) ∧ (∀ s t m c : ℝ, 0 < t → t ≤ s → 0 ≤ m → 0 < c → s*c < t*(m+c) →
  η s t m c=(s+t)/(m+2*c) ∧ 0 < w t (η s t m c) c ∧
    w s (η s t m c) c + w t (η s t m c) c=m) := by
  constructor
  · intro s t m c ht hts hm hc cut
    have hs := ht.trans_le hts
    have a : 0 < m+c := by linarith
    have b : 0 < m+2*c := by linarith
    have ed : η s t m c = s/(m+c) := by
      apply max_eq_left
      apply (div_le_div_iff₀ b a).mpr
      nlinarith only [cut]
    have ep := div_pos hs a
    have val : s/(s/(m+c))-c=m := by field_simp [hs.ne',a.ne']; ring
    have small : t/(s/(m+c))-c ≤ 0 := by
      apply sub_nonpos.mpr
      apply (div_le_iff₀ ep).mpr
      rw [← mul_div_assoc]
      apply (le_div_iff₀ a).mpr
      linarith only [cut]
    exact ⟨ed,by rw [ed,w,val,max_eq_right hm],by rw [ed,w,max_eq_left small]⟩
  · intro s t m c ht hts hm hc cut
    have hs := ht.trans_le hts
    have a : 0 < m+c := by linarith
    have b : 0 < m+2*c := by linarith
    have ab := add_pos hs ht
    have ed : η s t m c = (s+t)/(m+2*c) := by
      apply max_eq_right
      apply (div_le_div_iff₀ a b).mpr
      nlinarith only [cut]
    let l := (s+t)/(m+2*c)
    have ep : 0 < l := div_pos ab b
    have pos : 0 < t/l-c := by
      apply sub_pos.mpr
      apply (lt_div_iff₀ ep).mpr
      dsimp [l]
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ b).mpr
      nlinarith only [cut]
    have pos' : 0 ≤ s/l-c := by
      have := div_le_div_of_nonneg_right hts ep.le
      linarith
    refine ⟨ed,?_,?_⟩
    · rw [ed]; change 0 < max 0 (t/l-c)
      rwa [max_eq_right pos.le]
    · rw [ed]; change max 0 (s/l-c)+max 0 (t/l-c)=m
      rw [max_eq_right pos',max_eq_right pos.le]
      dsimp [l]
      field_simp [ab.ne',b.ne']
      <;> ring

end OddAllocation

end BlockHierarchy.Four
