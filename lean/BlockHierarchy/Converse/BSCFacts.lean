import BlockHierarchy.Converse.Bernoulli

open scoped BigOperators
namespace BlockHierarchy.Converse
open Varentropy

theorem bsc_positive {D : ℝ} (hd : 0<D) (dh : D<1) (k : ℕ) (x y : Bits k) :
    0<bsc D k x y := by
  induction k with
  | zero => exact zero_lt_one
  | succ n ih =>
    change 0<(if x.1=y.1 then 1-D else D)*bsc D n x.2 y.2
    exact mul_pos (by split <;> linarith) (ih _ _)

theorem bsc_normal (D : ℝ) (k : ℕ) (y : Bits k) : (∑ x, bsc D k x y)=1 := by
  induction k with
  | zero => simp [bsc,show Fintype.card (Bits 0)=1 from rfl]
  | succ n ih =>
    rw [sum_next]
    have inner (a : Bool) : (∑ x : Bits n, bsc D (n+1) (a,x) y)=if a=y.1 then 1-D else D := by
      change (∑ x : Bits n, (if a=y.1 then 1-D else D)*bsc D n x y.2)=_
      rw [←Finset.mul_sum,ih,mul_one]
    simp_rw [inner,Fintype.sum_bool]
    cases y.1 <;> simp <;> ring

theorem bsc_cost (D : ℝ) (k : ℕ) (y : Bits k) :
    (∑ x, bsc D k x y*(hamming k x y : ℝ))=k*D := by
  induction k with
  | zero => simp [hamming]
  | succ n ih =>
    rw [sum_next]
    have inner (a : Bool) : (∑ xs : Bits n, bsc D (n+1) (a,xs) y*(hamming (n+1) (a,xs) y : ℝ)) =
        (if a=y.1 then 1-D else D)*((if a=y.1 then 0 else 1)+(n:ℝ)*D) := by
      have term (xs : Bits n) : bsc D (n+1) (a,xs) y*(hamming (n+1) (a,xs) y : ℝ) =
          (if a=y.1 then 1-D else D)*
            (bsc D n xs y.2*(if a=y.1 then 0 else 1)+bsc D n xs y.2*(hamming n xs y.2 : ℝ)) := by
        by_cases e : a=y.1 <;> simp [bsc,hamming,e] <;> ring
      simp only [term,←Finset.mul_sum,Finset.sum_add_distrib,←Finset.sum_mul,bsc_normal,one_mul,ih]
    simp_rw [inner,Fintype.sum_bool]
    cases y.1 <;> simp <;> ring

theorem bsc_log {D : ℝ} (hd : 0<D) (dh : D<1) (k : ℕ) (x y : Bits k) :
    Real.log (bsc D k x y)=(Real.log D-Real.log (1-D))*(hamming k x y : ℝ)+k*Real.log (1-D) := by
  induction k with
  | zero => simp [bsc,hamming]
  | succ n ih =>
    change Real.log ((if x.1=y.1 then 1-D else D)*bsc D n x.2 y.2)=_
    rw [Real.log_mul (show (if x.1=y.1 then 1-D else D)≠0 by split <;> linarith)
      (bsc_positive hd dh n _ _).ne',ih]
    by_cases e : x.1=y.1 <;> simp [hamming,e] <;> ring

end BlockHierarchy.Converse
