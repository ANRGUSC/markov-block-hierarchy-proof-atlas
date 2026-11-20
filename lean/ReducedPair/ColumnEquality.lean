import ChannelEquality

open scoped BigOperators
namespace BlockHierarchy.Channel

variable {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X]

/-- Equality under the column test fixes the conditional law of each used
output, even if some unused columns of the dual kernel have mass below one. -/
theorem column_equality (P : X → ℝ) (q t : Y → ℝ) (K J d : X → Y → ℝ)
    (s : ℝ) (f : X → ℝ) (hs : s ≤ 0) (hK : ∀ x y, 0 < K x y)
    (hJ : ∀ x y, 0 ≤ J x y) (mass : ∑ x, P x=1) (row : ∀ x, ∑ y, q y*K x y=P x)
    (out : ∀ y, ∑ x, q y*K x y=q y) (src : ∀ x, ∑ y, J x y=P x)
    (dst : ∀ y, ∑ x, J x y=t y) (test : ∀ y, ∑ x, K x y ≤ 1)
    (logK : ∀ x y, Real.log (K x y)=s*d x y+f x)
    (budget : cost d J ≤ cost d (fun x y => q y*K x y))
    (minimizes : info P t J ≤ info P q (fun x y => q y*K x y)) :
    ∀ x y, J x y = (t y / (∑ i, K i y))*K x y := by
  let c (y : Y) := ∑ x, K x y
  let k (x : X) (y : Y) := K x y / c y
  have pc (y : Y) : 0 < c y := Finset.sum_pos (fun x _ => hK x y) Finset.univ_nonempty
  have pk (x : X) (y : Y) : 0 < k x y := div_pos (hK x y) (pc y)
  have cols (y : Y) : ∑ x, k x y = 1 := by
    simp only [k,div_eq_mul_inv,←Finset.sum_mul]; exact mul_inv_cancel₀ (pc y).ne'
  have active (y : Y) : q y=0 ∨ c y=1 := by
    have h := out y
    rw [←Finset.mul_sum] at h
    by_cases e : q y=0
    · exact Or.inl e
    · right; apply (mul_left_cancel₀ e); simpa only [mul_one] using h
  have r (x : X) (y : Y) : q y*k x y=q y*K x y := by
    rcases active y with e | e <;> simp [k,e]
  have penalty (v : Y → ℝ) (L : X → Y → ℝ) (rows : ∀ x, ∑ y, L x y=P x)
      (outputs : ∀ y, ∑ x, L x y=v y) :
      cost (fun x y => -Real.log (k x y)) L =
      (-s)*cost d L - ∑ x, P x*f x + ∑ y, v y*Real.log (c y) := by
    have term (x : X) (y : Y) : L x y*(-Real.log (k x y)) =
        (-s)*(L x y*d x y)-L x y*f x+L x y*Real.log (c y) := by
      dsimp [k]; rw [Real.log_div (hK x y).ne' (pc y).ne',logK]; ring
    unfold cost
    simp_rw [term]
    have exchange : (∑ x, ∑ y, L x y*Real.log (c y)) = ∑ y, v y*Real.log (c y) := by
      rw [Finset.sum_comm]; simp only [←Finset.sum_mul,outputs]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
      ← Finset.sum_mul,rows,exchange]
  have qpen : (∑ y, q y*Real.log (c y))=0 := by
    apply Finset.sum_eq_zero
    intro y _
    rcases active y with e | e <;> simp [e]
  have tpen : (∑ y, t y*Real.log (c y))≤0 := by
    apply Finset.sum_nonpos
    intro y _
    have nonneg : 0 ≤ t y := by rw [←dst]; exact Finset.sum_nonneg (fun x _ => hJ x y)
    exact mul_nonpos_of_nonneg_of_nonpos nonneg (Real.log_nonpos (pc y).le (test y))
  have equalJoint : (fun x y => q y*k x y) = (fun x y => q y*K x y) :=
    funext (fun x => funext (r x))
  have feasible : cost (fun x y => -Real.log (k x y)) J ≤
      cost (fun x y => -Real.log (k x y)) (fun x y => q y*k x y) := by
    rw [equalJoint,penalty t J src dst,penalty q _ row out,qpen]
    linarith only [mul_le_mul_of_nonneg_left budget (neg_nonneg.mpr hs),tpen]
  have normalizedRows (x : X) : ∑ y, q y*k x y=P x := by simp_rw [r]; exact row x
  have comp : info P t J ≤ info P q (fun x y => q y*k x y) := equalJoint.symm ▸ minimizes
  have h := optimal_joint_factors P q t k J (fun x y => -Real.log (k x y)) (-1) 0
    (by norm_num) pk hJ normalizedRows mass cols (fun x y => by ring) src dst feasible comp
  intro x y
  rw [h]
  dsimp [k,c]; ring

end BlockHierarchy.Channel
