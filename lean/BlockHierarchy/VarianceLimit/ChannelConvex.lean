import BlockHierarchy.VarianceLimit.Statement

open scoped BigOperators
namespace BlockHierarchy.VarianceLimit
open Cut

private theorem log_tangent {x y r : ℝ} (hx : 0≤x) (hy : 0≤y) (hr : 0<r)
    (support : 0<x → 0<y) :
    x*Real.log r-x*Real.log (x/y) ≤ r*y-x := by
  by_cases h : x=0
  · subst x
    simp [mul_nonneg hr.le hy]
  have xp : 0<x := lt_of_le_of_ne hx (Ne.symm h)
  have yp := support xp
  have z := Real.log_le_sub_one_of_pos (div_pos (mul_pos hr yp) xp)
  rw [Real.log_div (mul_pos hr yp).ne' h,Real.log_mul hr.ne' yp.ne'] at z
  have z' := mul_le_mul_of_nonneg_right z hx
  rw [Real.log_div h yp.ne']
  simp only [sub_mul,div_mul_cancel₀ _ h,one_mul] at z'
  linarith

private theorem log_sum {s t u v : ℝ} (hs : 0≤s) (ht : 0≤t) (hu : 0≤u) (hv : 0≤v)
    (su : 0<s → 0<u) (tv : 0<t → 0<v) :
    (s+t)*Real.log ((s+t)/(u+v)) ≤ s*Real.log (s/u)+t*Real.log (t/v) := by
  by_cases h : s+t=0
  · have s0 : s=0 := by linarith
    have t0 : t=0 := by linarith
    simp [s0,t0]
  have n : 0<s+t := lt_of_le_of_ne (add_nonneg hs ht) (Ne.symm h)
  have d : 0<u+v := by
    by_cases sc : 0<s
    · linarith [su sc]
    · linarith [tv (by linarith)]
  let r := (s+t)/(u+v)
  have rp : 0<r := div_pos n d
  have cancel : r*(u+v)=s+t := div_mul_cancel₀ _ d.ne'
  have l := log_tangent hs hu rp su
  have k := log_tangent ht hv rp tv
  change (s+t)*Real.log r ≤ _
  linarith

private theorem kl_scale (a x y : ℝ) :
    (a*x)*Real.log ((a*x)/(a*y))=a*(x*Real.log (x/y)) := by
  by_cases h : a=0
  · simp [h]
  rw [mul_div_mul_left _ _ h]
  ring

private theorem output_pos {X : Type*} [Fintype X] {P : X → ℝ} {W : X → X → ℝ}
    (hp : IsPrior P) (hW : IsChannel W) {x y : X} (hx : 0<P x) (h : 0<W x y) :
    0<∑ u, P u*W u y := by
  classical
  apply lt_of_lt_of_le (mul_pos hx h)
  exact Finset.single_le_sum (f := fun u => P u*W u y)
    (fun u _ => mul_nonneg (hp.1 u) ((hW u).1 y)) (Finset.mem_univ x)

/-- Mutual information in nats is convex in the test channel at a fixed source,
including channels that have zero entries or unused reproduction symbols. -/
theorem information_mix {X : Type*} [Fintype X] {P : X → ℝ} {W V : X → X → ℝ} {a : ℝ}
    (hp : IsPrior P) (hW : IsChannel W) (hV : IsChannel V) (h0 : 0≤a) (h1 : a≤1) :
    informationNats P (fun x y => a*W x y+(1-a)*V x y) ≤
      a*informationNats P W+(1-a)*informationNats P V := by
  classical
  let b := 1-a
  have hb : 0≤b := by dsimp [b]; linarith
  let Y := fun y => ∑ x, P x*W x y
  let Z := fun y => ∑ x, P x*V x y
  have marg (y : X) :
      (∑ x, P x*(a*W x y+b*V x y))=a*Y y+b*Z y := by
    unfold Y Z
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold informationNats
  change (∑ x, ∑ y, P x*(a*W x y+b*V x y)*Real.log ((a*W x y+b*V x y)/
    (∑ u, P u*(a*W u y+b*V u y)))) ≤ a*(∑ x, ∑ y, P x*W x y*Real.log (W x y/Y y))+
    b*(∑ x, ∑ y, P x*V x y*Real.log (V x y/Z y))
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro y _
  rw [marg]
  by_cases h : P x = 0
  · simp [h]
  have px := lt_of_le_of_ne (hp.1 x) (Ne.symm h)
  have wy := (hW x).1 y
  have vy := (hV x).1 y
  have yp : 0≤Y y := Finset.sum_nonneg (fun u _ => mul_nonneg (hp.1 u) ((hW u).1 y))
  have zp : 0≤Z y := Finset.sum_nonneg (fun u _ => mul_nonneg (hp.1 u) ((hV u).1 y))
  have cs := log_sum (mul_nonneg h0 wy) (mul_nonneg hb vy) (mul_nonneg h0 yp) (mul_nonneg hb zp)
    (fun H => mul_pos (pos_of_mul_pos_left H wy) (output_pos hp hW px (pos_of_mul_pos_right H h0)))
    (fun H => mul_pos (pos_of_mul_pos_left H vy) (output_pos hp hV px (pos_of_mul_pos_right H hb)))
  rw [kl_scale,kl_scale] at cs
  linarith [mul_le_mul_of_nonneg_left cs (hp.1 x)]

#print axioms information_mix
end BlockHierarchy.VarianceLimit
