import ReducedPair

namespace BlockHierarchy.ReducedPair

/-- The second-branch crossover is feasible, and grows from its boundary value. -/
theorem branch_parameters {A B C r D : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (mass : A+2*C+B=1) (hr : 0 < r) (hr1 : r < 1/2) (root : r*(1-r)=C)
    (first : r ≤ D) (last : D < C+min A B) :
    let S := A+B
    let δ := (D-C)/S
    let u := Real.sqrt (δ/(1-δ))
    0 < δ ∧ δ < 1/2 ∧ 0 < u ∧ u < 1 ∧
      0 < A-B*u^2 ∧ 0 < B-A*u^2 ∧ C/S ≤ u/(1+u^2) ∧ u/(1+u^2) ≤ 1/2 := by
  let S := A+B
  let δ := (D-C)/S
  let u := Real.sqrt (δ/(1-δ))
  have hs : 0 < S := add_pos hA hB
  have pa : D < C+A := by linarith only [last,min_le_left A B]
  have pb : D < C+B := by linarith only [last,min_le_right A B]
  have hδ : 0 < δ := div_pos (by nlinarith only [root,first,sq_pos_of_pos hr]) hs
  have half : δ < 1/2 := (div_lt_iff₀ hs).mpr (by dsimp [S]; linarith only [pa,pb])
  have hd : 0 < 1-δ := by linarith
  have pos : 0 < u := Real.sqrt_pos.mpr (div_pos hδ hd)
  have sq : u^2 = δ/(1-δ) := Real.sq_sqrt (div_nonneg hδ.le hd.le)
  have eq := (eq_div_iff hd.ne').mp sq
  have ult : u < 1 := by
    apply (Real.sqrt_lt' (by norm_num : (0:ℝ)<1)).mpr
    apply (div_lt_iff₀ hd).mpr
    linarith
  have dscale : δ*S = D-C := div_mul_cancel₀ _ hs.ne'
  have constpos (a b : ℝ) (sum : a+b=S) (bound : D<C+a) : 0 < a-b*u^2 := by
    by_contra! hn
    nlinarith only [mul_nonpos_of_nonpos_of_nonneg hn hd.le,congrArg (fun v : ℝ => b*v) eq,
      congrArg (fun v : ℝ => δ*v) sum,dscale,bound]
  have rr : 0 < 1-r := by linarith
  have boundary : r^2 ≤ D-C := by nlinarith only [root,first]
  have hrSq : (1-r)^2 = S-r^2 := by dsimp [S]; nlinarith only [mass,root]
  have one : 0 < 1+u^2 := by nlinarith only [sq_nonneg u]
  have rbound : r/(1-r) ≤ u := by
    by_contra! lt
    have hlt := (lt_div_iff₀ rr).mp lt
    have strict := mul_pos (sub_pos.mpr hlt) (add_pos hr (mul_pos pos rr))
    have leδ : r^2 ≤ δ*S := by rwa [dscale]
    have hprod := mul_nonneg (sub_nonneg.mpr leδ) (le_of_lt one)
    nlinarith only [strict, hprod, congrArg (fun v : ℝ => u^2*v) hrSq,
      congrArg (fun v : ℝ => v*S) eq]
  have factor : 0 ≤ (u*(1-r)-r)*(1-r-u*r) := by
    apply mul_nonneg (sub_nonneg.mpr ((div_le_iff₀ rr).mp rbound))
    nlinarith only [hr1,mul_lt_mul_of_pos_right ult hr]
  have start : C/S ≤ u/(1+u^2) := by
    apply (div_le_div_iff₀ hs one).mpr
    change C*(1+u^2) ≤ u*(A+B)
    nlinarith only [factor,congrArg (fun v : ℝ => u^2*v) root,root,
      congrArg (fun v : ℝ => u*v) mass,congrArg (fun v : ℝ => u*v) root]
  exact ⟨hδ,half,pos,ult,constpos A B rfl pa,constpos B A (add_comm B A) pb,start,
    (div_le_iff₀ one).mpr (by nlinarith only [sq_nonneg (1-u)])⟩

end BlockHierarchy.ReducedPair
