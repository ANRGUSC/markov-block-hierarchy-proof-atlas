import ReducedPair.Branch
import Variational
import ReducedPair.RateStatement

open scoped BigOperators
namespace BlockHierarchy.ReducedPair
open PairChannel

noncomputable def kernel (A B C u : ℝ) (x y : Word) :=
  law A B C x * u^hamming x y / Z A B u x

theorem second_optimal {A B C r D : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (mass : A+2*C+B=1) (hr : 0 < r) (hr1 : r < 1/2) (root : r*(1-r)=C)
    (first : r ≤ D) (last : D < C+min A B) :
    let δ := (D-C)/(A+B)
    let u := Real.sqrt (δ/(1-δ))
    GibbsPoint (law A B C) (prior A B u) D u (Z A B u) ∧
      jointCost (fun x y => prior A B u y * kernel A B C u x y) = 2*D := by
  let δ := (D-C)/(A+B)
  let u := Real.sqrt (δ/(1-δ))
  let q := prior A B u
  let K := kernel A B C u
  obtain ⟨hd,half,hu,ult,ca,cb,lo,hi⟩ := branch_parameters hA hB hC mass hr hr1 root first last
  have pos : 0 < u := hu
  have small : u < 1 := ult
  have hs := add_pos hA hB
  have h2 : 0 < 1+u^2 := by nlinarith only [sq_nonneg u]
  have hm : 0 < 1-u^2 := by nlinarith only [mul_pos (sub_pos.mpr small) (show 0 < 1+u by linarith)]
  have hq (y : Word) : 0 ≤ q y := by
    obtain ⟨i,j⟩ := y
    cases i <;> cases j <;> first | exact (div_pos ca (mul_pos hs hm)).le
                                   | exact (div_pos cb (mul_pos hs hm)).le | exact le_refl 0
  have hz (x : Word) : 0 < Z A B u x := by
    obtain ⟨i,j⟩ := x
    cases i <;> cases j <;> first | exact div_pos (mul_pos hA h2) hs
                                   | exact div_pos (mul_pos hB h2) hs | exact pos
  have hp (x : Word) : 0 < law A B C x := by
    obtain ⟨i,j⟩ := x
    cases i <;> cases j <;> first | exact hA | exact hB | exact hC
  have hk (x y : Word) : 0 < K x y := div_pos (mul_pos (hp x) (pow_pos pos _)) (hz x)
  have row (x : Word) : ∑ y, q y*K x y = law A B C x := by
    have term (y : Word) : q y*K x y = (q y*u^hamming x y)*(law A B C x / Z A B u x) := by
      dsimp [K,kernel]; ring
    simp_rw [term]
    rw [←Finset.sum_mul, normalizers A B u hA hB pos small]
    field_simp [(hz x).ne']
  have test (y : Word) : ∑ x, K x y ≤ 1 := by
    rw [show (∑ x, K x y) = _ from columns A B C u hA hB pos mass y]
    split
    · exact le_rfl
    · exact inactive_column_test hs (by linarith only [mass]) (div_pos pos h2) lo hi
  have out (y : Word) : ∑ x, q y*K x y = q y := by
    rw [←Finset.mul_sum, show (∑ x, K x y) = _ from columns A B C u hA hB pos mass y]
    obtain ⟨i,j⟩ := y
    cases i <;> cases j <;> simp [q,prior,law]
  have den : 0 < 1-δ := by change (D-C)/(A+B) < 1/2 at half; dsimp [δ]; linarith
  have eq : u^2*(1-δ)=δ := (eq_div_iff den.ne').mp (Real.sq_sqrt (div_nonneg hd.le den.le))
  have budget : jointCost (fun x y => q y*K x y) = 2*D := by
    have cost_u : jointCost (fun x y => q y*K x y) = 2*C+2*(A+B)*u^2/(1+u^2) := by
      unfold jointCost Channel.cost
      simp_rw [word_sum]
      norm_num [q,K,prior,kernel,Z,law,hamming]
      field_simp [hA.ne',hB.ne',hs.ne',hm.ne',h2.ne',pos.ne']
      ring
    rw [cost_u]
    have hscale : δ*(A+B) = D-C := div_mul_cancel₀ _ hs.ne'
    have cross : u^2/(1+u^2) = δ := (div_eq_iff h2.ne').mpr (by nlinarith only [eq])
    rw [show 2*(A+B)*u^2/(1+u^2) = 2*(A+B)*(u^2/(1+u^2)) by ring,cross]
    linarith only [hscale,mul_comm δ (A+B),mul_assoc 2 (A+B) δ]
  refine ⟨⟨fun x => (normalizers A B u hA hB pos small x).symm,
    fun x y => mul_nonneg (hq y) (hk x y).le,row,out,budget.le,?_⟩,budget⟩
  intro t L hL src dst bound
  apply Channel.column_optimal _ q t K L _ (Real.log u)
    (fun x => Real.log (law A B C x)-Real.log (Z A B u x))
    (Real.log_nonpos pos.le small.le) hk hL row dst src test _ (bound.trans_eq budget.symm)
  intro x y
  dsimp only [K,kernel]
  rw [Real.log_div (mul_pos (hp x) (pow_pos pos _)).ne' (hz x).ne',
    Real.log_mul (hp x).ne' (pow_pos pos _).ne',Real.log_pow]
  ring

end BlockHierarchy.ReducedPair
