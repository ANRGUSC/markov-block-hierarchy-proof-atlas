import BlockHierarchy.Cut.Statement
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open scoped BigOperators
open Set
namespace BlockHierarchy.Cut

variable {X : Type*} [Fintype X]

theorem Z_pos (τ : ℝ) (d : X → X → ℕ) {q : X → ℝ} (hq : IsPrior q) (x : X) :
    0 < Z τ d q x := by
  classical
  obtain ⟨y, _, pos⟩ := Finset.sum_pos_iff_of_nonneg (fun y (_ : y ∈ Finset.univ) => hq.1 y) |>.mp
    (show 0 < ∑ y, q y by rw [hq.2]; norm_num)
  exact Finset.sum_pos' (fun y _ => mul_nonneg (hq.1 y) (Real.exp_pos _).le)
    ⟨y, Finset.mem_univ _, mul_pos pos (Real.exp_pos _)⟩

private theorem prior_mix {q r : X → ℝ} (hq : IsPrior q) (hr : IsPrior r)
    {t : ℝ} (ht : t ∈ Icc 0 1) : IsPrior (fun y => (1-t)*q y + t*r y) := by
  refine ⟨fun y => add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (hq.1 y)) (mul_nonneg ht.1 (hr.1 y)), ?_⟩
  rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.mul_sum, hq.2, hr.2]
  ring

private theorem Z_mix (τ : ℝ) (d : X → X → ℕ) (q r : X → ℝ) (t : ℝ) (x : X) :
    Z τ d (fun y => (1-t)*q y+t*r y) x = Z τ d q x+t*(Z τ d r x-Z τ d q x) := by
  unfold Z
  simp only [mul_sub, Finset.mul_sum, ←Finset.sum_sub_distrib, ←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- One-sided derivative at an optimal prior toward any other probability law. -/
theorem optimal_direction {P q r : X → ℝ} {τ : ℝ} {d : X → X → ℕ}
    (hq : Optimal P τ d q) (hr : IsPrior r) :
    (∑ x, P x * ((Z τ d r x - Z τ d q x)/Z τ d q x)) ≤ 0 := by
  let z := Z τ d q
  let v := Z τ d r
  let F (t : ℝ) := ∑ x, P x*Real.log (z x+t*(v x-z x))
  have der : HasDerivAt F (∑ x, P x*((v x-z x)/z x)) 0 := by
    apply HasDerivAt.fun_sum
    intro x _
    apply HasDerivAt.const_mul
    have h := ((hasDerivAt_id (0:ℝ)).mul_const (v x-z x)).const_add (z x)
    have h' := h.log (by simpa using (Z_pos τ d hq.1 x).ne')
    simpa using h'
  have val (t : ℝ) : mean P (score τ d (fun y => (1-t)*q y+t*r y)) = -F t := by
    simp only [mean, score, Z_mix, F, z, v, mul_neg, Finset.sum_neg_distrib]
  have maxF : IsMaxOn F (Icc 0 1) 0 := by
    intro t ht
    have cmp := hq.2 _ (prior_mix hq.1 hr ht)
    rw [val] at cmp
    have zero := val 0
    simp only [sub_zero,one_mul,zero_mul,add_zero] at zero
    rw [zero] at cmp
    exact neg_le_neg_iff.mp cmp
  have cone : (1:ℝ) ∈ posTangentConeAt (Icc (0:ℝ) 1) 0 := by
    apply mem_posTangentConeAt_of_segment_subset
    simp [segment_eq_Icc]
  simpa using maxF.localize.hasFDerivWithinAt_nonpos der.hasFDerivAt.hasFDerivWithinAt cone

theorem optimal_column {P q : X → ℝ} {τ : ℝ} {d : X → X → ℕ}
    (hp : ∑ x, P x = 1) (hq : Optimal P τ d q) (y : X) :
    (∑ x, P x * Real.exp (-τ*(d x y : ℝ))/Z τ d q x) ≤ 1 := by
  classical
  let r (a : X) : ℝ := if a=y then 1 else 0
  have hr : IsPrior r := ⟨fun a => by dsimp [r]; split <;> norm_num, by simp [r]⟩
  have h := optimal_direction hq hr
  have single (x : X) : Z τ d r x = Real.exp (-τ*(d x y : ℝ)) := by
    simp [Z,r,ite_mul]
  have term (x : X) : P x*((Z τ d r x-Z τ d q x)/Z τ d q x) =
      P x * Real.exp (-τ*(d x y : ℝ))/Z τ d q x - P x := by
    rw [single,sub_div,div_self (Z_pos τ d hq.1 x).ne']
    ring
  simp_rw [term, Finset.sum_sub_distrib,hp] at h
  linarith


/-- All optimal priors have the same normalizer on a positive source, including at zero multiplier. -/
theorem optimal_Z_eq {P q r : X → ℝ} {τ : ℝ} {d : X → X → ℕ}
    (hp : ∀ x, 0 < P x) (hq : Optimal P τ d q) (hr : Optimal P τ d r) :
    Z τ d q = Z τ d r := by
  let z := Z τ d q
  let v := Z τ d r
  let E (x : X) := P x * (v x-z x)^2/(z x*v x)
  have zpos (x : X) : 0 < z x := Z_pos τ d hq.1 x
  have vpos (x : X) : 0 < v x := Z_pos τ d hr.1 x
  have nonneg (x : X) : 0 ≤ E x := div_nonneg (mul_nonneg (hp x).le (sq_nonneg _)) (mul_pos (zpos x) (vpos x)).le
  have term (x : X) : P x*((v x-z x)/z x)+P x*((z x-v x)/v x) = E x := by
    dsimp only [E]
    field_simp [(zpos x).ne', (vpos x).ne']
    ring
  have upper := add_le_add (optimal_direction hq hr.1) (optimal_direction hr hq.1)
  change (∑ x, P x*((v x-z x)/z x)) + (∑ x, P x*((z x-v x)/v x)) ≤ 0+0 at upper
  simp only [←Finset.sum_add_distrib, term, add_zero] at upper
  have allZero := (Finset.sum_eq_zero_iff_of_nonneg (fun x (_ : x ∈ Finset.univ) => nonneg x)).1
    (upper.antisymm (Finset.sum_nonneg (fun x _ => nonneg x)))
  funext x
  by_contra ne
  have positive : 0 < E x := div_pos (mul_pos (hp x) (sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm ne))))
    (mul_pos (zpos x) (vpos x))
  exact positive.ne' (allZero x (Finset.mem_univ _))

/-- Isometries of the source leave every optimal canonical score invariant. -/
theorem optimal_score_invariant {P q : X → ℝ} {τ : ℝ} {d : X → X → ℕ}
    (hp : ∀ x, 0 < P x) (hq : Optimal P τ d q) (e : X ≃ X)
    (massInv : ∀ x, P (e x)=P x)
    (distInv : ∀ x y, d (e x) (e y)=d x y) (x : X) :
    score τ d q (e x)=score τ d q x := by
  let r (y : X) := q (e y)
  have hr : IsPrior r := ⟨fun y => hq.1.1 (e y), (e.sum_comp q).trans hq.1.2⟩
  have moved (a : X) : Z τ d r a=Z τ d q (e a) := by
    unfold Z
    rw [←e.sum_comp (fun y => q y * Real.exp (-τ*(d (e a) y : ℝ)))]
    simp only [r,distInv]
  have obj : mean P (score τ d r)=mean P (score τ d q) := by
    unfold mean
    rw [←e.sum_comp (fun y => P y*score τ d q y)]
    simp only [score,moved,massInv]
  have opt : Optimal P τ d r := ⟨hr,fun v hv => obj.trans_le (hq.2 v hv)⟩
  have same := congrFun (optimal_Z_eq hp hq opt) x
  rw [moved] at same
  simp only [score,same]

#print axioms optimal_column
#print axioms optimal_score_invariant
end BlockHierarchy.Cut
