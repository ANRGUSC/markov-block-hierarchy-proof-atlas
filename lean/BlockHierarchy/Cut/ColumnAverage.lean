import FiniteChannel

open scoped BigOperators
namespace BlockHierarchy.Cut

theorem weighted_column_bound {X Y : Type*} [Fintype X] [Fintype Y]
    (P z : X → ℝ) (q : Y → ℝ) (K : X → Y → ℝ)
    (prob : ∀ y,0≤q y) (total : ∑ y,q y=1)
    (test : ∀ y, (∑ x,P x*K x y/z x)≤1) :
    (∑ x,P x*((∑ y,q y*K x y)/z x))≤1 := by
  have swap : (∑ x,P x*((∑ y,q y*K x y)/z x)) =
      ∑ y,q y*(∑ x,P x*K x y/z x) := by
    simp_rw [div_eq_mul_inv,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [swap,← total]
  exact Finset.sum_le_sum (fun y _ => by simpa using mul_le_mul_of_nonneg_left (test y) (prob y))

theorem product_columns {X Y : Type*} [Fintype X] [Fintype Y] (a : X → ℝ) (b : Y → ℝ)
    (ha : 0≤∑ x,a x) (hb : 0≤∑ y,b y) (left : (∑ x,a x)≤1) (right : (∑ y,b y)≤1) :
    (∑ xy : X × Y,a xy.1*b xy.2)≤1 := by
  simp_rw [Fintype.sum_prod_type,← Finset.mul_sum,← Finset.sum_mul]
  exact (mul_le_mul_of_nonneg_right left hb).trans (by simpa using right)

end BlockHierarchy.Cut
