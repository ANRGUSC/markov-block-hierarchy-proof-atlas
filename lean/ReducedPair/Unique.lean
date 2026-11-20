import ReducedPair.ColumnEquality
import ReducedPair.Optimal
import PairUniqueness

open scoped BigOperators
namespace BlockHierarchy.ReducedPair
open PairChannel

theorem middle_unique {A B C r D : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (mass : A+2*C+B=1) (hr : 0 < r) (hr1 : r < 1/2) (root : r*(1-r)=C)
    (first : r ≤ D) (last : D < C+min A B) (t : Word → ℝ) (J : Word → Word → ℝ)
    (opt : MinimizesAt (law A B C) t J D) :
    let δ := (D-C)/(A+B)
    t=prior A B (Real.sqrt (δ/(1-δ))) := by
  let δ := (D-C)/(A+B)
  let u := Real.sqrt (δ/(1-δ))
  let K := kernel A B C u
  let q := prior A B u
  let c (y : Word) := ∑ x, K x y
  obtain ⟨_,_,hu,hlt,_,_,lo,hi⟩ := branch_parameters hA hB hC mass hr hr1 root first last
  have pos : 0 < u := hu
  have small : u<1 := hlt
  have hs := add_pos hA hB
  have h2 : 0 < 1+u^2 := by nlinarith only [sq_nonneg u]
  have hp (x : Word) : 0 < law A B C x := by
    obtain ⟨a,b⟩ := x
    cases a <;> cases b <;> first | exact hA | exact hB | exact hC
  have hz (x : Word) : 0 < Z A B u x := by
    obtain ⟨a,b⟩ := x
    cases a <;> cases b <;> first | exact div_pos (mul_pos hA h2) hs
                                   | exact div_pos (mul_pos hB h2) hs | exact pos
  have hk (x y : Word) : 0 < K x y := div_pos (mul_pos (hp x) (pow_pos pos _)) (hz x)
  have pc (y : Word) : 0 < c y := Finset.sum_pos (fun x _ => hk x y) Finset.univ_nonempty
  obtain ⟨candidate,cap⟩ := second_optimal hA hB hC mass hr hr1 root first last
  obtain ⟨hj,src,dst,budget,minimal⟩ := opt
  obtain ⟨h0,rows,outputs,valid,_⟩ := candidate.2
  have cmp := minimal q (fun x y => q y*K x y) h0 rows outputs valid
  have sumP : ∑ x, law A B C x=1 := by rw [word_sum]; change A+C+C+B=1; linarith only [mass]
  have test (y : Word) : c y ≤ 1 := by
    rw [show c y = _ from columns A B C u hA hB pos mass y]
    split
    · exact le_rfl
    · exact inactive_column_test hs (by linarith only [mass]) (div_pos pos h2) lo hi
  have kernelLog (x y : Word) : Real.log (K x y) = Real.log u*(hamming x y : ℝ)+
      (Real.log (law A B C x)-Real.log (Z A B u x)) := by
    dsimp only [K,kernel]
    rw [Real.log_div (mul_pos (hp x) (pow_pos pos _)).ne' (hz x).ne',Real.log_mul (hp x).ne'
      (pow_pos pos _).ne',Real.log_pow]
    ring
  have form := Channel.column_equality _ q t K J (fun x y => (hamming x y : ℝ)) _ _
    (Real.log_nonpos pos.le small.le) hk hj sumP rows outputs src dst test kernelLog (budget.trans_eq cap.symm) cmp
  let v (y : Word) := t y/c y
  have vrow (x : Word) : ∑ y, v y*K x y = law A B C x := by
    change (∑ y, t y/(∑ i, K i y)*K x y) = _
    simp_rw [←form]; exact src x
  have conv (a : Word → ℝ) (x : Word) : (∑ y, a y*backward u x y) =
      (∑ y, a y*K x y) * (Z A B u x/(law A B C x*(1+u)^2)) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    dsimp only [backward,K,kernel]
    field_simp [(hp x).ne',(hz x).ne',show 1+u ≠ 0 by linarith]
  have same (x : Word) : (∑ y, v y*backward u x y) = ∑ y, q y*backward u x y := by
    rw [conv,conv,vrow,show (∑ y, q y*K x y)=_ from rows x]
  funext y
  have eq : v y=q y := by
    calc v y = _ := (recover u pos.le small v y).symm
         _ = q y := by simp_rw [same]; exact recover u pos.le small q y
  have active := outputs y
  change (∑ x, q y*K x y) = q y at active
  rw [←Finset.mul_sum] at active
  exact ((div_eq_iff (pc y).ne').mp eq).trans active

end BlockHierarchy.ReducedPair
