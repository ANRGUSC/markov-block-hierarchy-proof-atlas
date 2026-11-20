import BlockHierarchy.VarianceLimit.Dyadic
import Mathlib.Algebra.BigOperators.NatAntidiagonal

open Finset Filter
open scoped BigOperators Topology
namespace BlockHierarchy.VarianceLimit

private theorem squares_of_mean {b : ℕ → ℝ} {L : ℝ} (hL : 0 ≤ L) {N : ℕ}
    (avg : N*L ≤ ∑ i ∈ range N, b (i+1)) :
    N*L^2 ≤ ∑ i ∈ range N, b (i+1)^2 := by
  have h : 0 ≤ ∑ i ∈ range N, (b (i+1)^2 - (2*L)*b (i+1) + L^2) := by
    apply sum_nonneg
    intro i _
    nlinarith only [sq_nonneg (b (i+1)-L)]
  simp only [sum_add_distrib,sum_sub_distrib,← mul_sum,sum_const,card_range,nsmul_eq_mul] at h
  nlinarith only [h,mul_le_mul_of_nonneg_left avg (show 0 ≤ 2*L by positivity)]

/-- Group the N-by-N array of positive-length cuts by their total length.
The antidiagonal indexed by k represents all cuts of a word of length k+2. -/
theorem square_gain_le_diagonals (G : ℕ → ℕ → ℝ) (hG : ∀ i j, 0 ≤ G (i+1) (j+1)) (N : ℕ) :
    (∑ i ∈ range N, ∑ j ∈ range N, G (i+1) (j+1)) ≤
      ∑ k ∈ range (2*N), ∑ i ∈ range (k+1), G (i+1) (k-i+1) := by
  let rect := (range N) ×ˢ (range N)
  let gain (z : ℕ × ℕ) := G (z.1+1) (z.2+1)
  have in_range (z : ℕ × ℕ) (hz : z ∈ rect) : z.1+z.2 ∈ range (2*N) := by
    obtain ⟨a,b⟩ := mem_product.mp hz
    simp only [mem_range] at a b ⊢
    omega
  calc
    _ = ∑ z ∈ rect, gain z := (sum_product ..).symm
    _ = ∑ k ∈ range (2*N), ∑ z ∈ rect with z.1+z.2=k, gain z :=
      (sum_fiberwise_of_maps_to in_range gain).symm
    _ ≤ ∑ k ∈ range (2*N), ∑ z ∈ antidiagonal k, gain z := by
      apply sum_le_sum
      intro k _
      apply sum_le_sum_of_subset_of_nonneg
      · intro z hz
        exact mem_antidiagonal.mpr (mem_filter.mp hz).2
      · intro z _ _
        exact hG _ _
    _ = _ := sum_congr rfl (fun k _ => Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk gain k)

/-- Jensen's bound and the finite reindexing in Appendix (positive). -/
theorem gain_sandwich {G : ℕ → ℕ → ℝ} {b U : ℕ → ℝ} {A L : ℝ}
    (hA : 0 ≤ A) (hL : 0 ≤ L) (N : ℕ)
    (avg : N*L ≤ ∑ i ∈ range N, b (i+1))
    (lo : ∀ i j, A*b (i+1)^2*b (j+1)^2 ≤ G (i+1) (j+1))
    (hi : ∀ k, (∑ i ∈ range (k+1), G (i+1) (k-i+1)) ≤ U k) :
    A*L^4*(N:ℝ)^2 ≤ ∑ k ∈ range (2*N), U k := by
  have sqs := squares_of_mean hL avg
  calc
    _ = A*((N:ℝ)*L^2)^2 := by ring
    _ ≤ A*(∑ i ∈ range N, b (i+1)^2)^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) sqs _) hA
    _ = ∑ i ∈ range N, ∑ j ∈ range N, A*b (i+1)^2*b (j+1)^2 := by
      simp only [← mul_sum]
      rw [← sum_mul, ← mul_sum]
      ring
    _ ≤ ∑ i ∈ range N, ∑ j ∈ range N, G (i+1) (j+1) := by
      exact sum_le_sum (fun i _ => sum_le_sum (fun j _ => lo i j))
    _ ≤ _ := (square_gain_le_diagonals G (fun i j => (by positivity : 0 ≤ A*b (i+1)^2*b (j+1)^2).trans (lo i j)) N).trans
      (sum_le_sum (fun k _ => hi k))

private theorem total_weights (N : ℕ) :
    (∑ k ∈ range (2*N), ((k:ℝ)+2)) = 2*(N:ℝ)^2+3*N := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1) = (2*n+1)+1 by omega, sum_range_succ,sum_range_succ,ih]
    push_cast
    ring

/-- Above any strict upper limit u, the total excess of the weighted scores
is bounded by a single finite prefix, independently of the cutoff. -/
private theorem weighted_upper {ω : ℕ → ℝ} {W u : ℝ} (conv : Tendsto ω atTop (𝓝 W)) (hu : W < u) :
    ∃ H : ℝ, ∀ N : ℕ, (∑ k ∈ range (2*N), ((k:ℝ)+2)*ω (k+2)) ≤
      u*(2*(N:ℝ)^2+3*N)+H := by
  obtain ⟨K,hK⟩ := eventually_atTop.mp (conv.eventually (gt_mem_nhds hu))
  let d (k : ℕ) := ((k:ℝ)+2)*(ω (k+2)-u)
  refine ⟨∑ k ∈ range K, |d k|,fun N => ?_⟩
  have early : (∑ k ∈ range (2*N), d k) ≤ ∑ k ∈ range K, |d k| := by
    calc
      _ ≤ ∑ k ∈ range (2*N), if k<K then |d k| else 0 := by
        apply sum_le_sum
        intro k _
        split
        · exact le_abs_self _
        · exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr (hK (k+2) (by omega)).le)
      _ = ∑ k ∈ (range (2*N)).filter (·<K), |d k| := by rw [sum_filter]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (fun k h => mem_range.mpr (mem_filter.mp h).2) (fun k _ _ => abs_nonneg _)
  calc
    _ = ∑ k ∈ range (2*N), (u*((k:ℝ)+2) + d k) := by
      apply sum_congr rfl
      intro k _
      dsimp [d]
      ring
    _ ≤ _ := by rw [sum_add_distrib,←mul_sum,total_weights]; exact add_le_add le_rfl early

private theorem aggregate_limit {D C W : ℝ} {ω : ℕ → ℝ} (hC : 0 < C)
    (conv : Tendsto ω atTop (𝓝 W))
    (bound : ∀ N : ℕ, 0<N → D*(N:ℝ)^2 ≤ C*∑ k ∈ range (2*N), ((k:ℝ)+2)*ω (k+2)) :
    D/(2*C) ≤ W := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro u hu
  obtain ⟨H,upper⟩ := weighted_upper conv hu
  have cmp (N : ℕ) (hn : 0<N) :
      D ≤ C*(u*(2+3*(1/(N:ℝ)))+H*(1/(N:ℝ))^2) := by
    have npos : 0 < (N:ℝ) := Nat.cast_pos.mpr hn
    have estimate := (bound N hn).trans (mul_le_mul_of_nonneg_left (upper N) hC.le)
    calc
      D = D*(N:ℝ)^2/(N:ℝ)^2 := (mul_div_cancel_right₀ _ (pow_ne_zero 2 npos.ne')).symm
      _ ≤ (C*(u*(2*(N:ℝ)^2+3*N)+H))/(N:ℝ)^2 :=
        div_le_div_of_nonneg_right estimate (sq_nonneg _)
      _ = _ := by field_simp
  have inv : Tendsto (fun N : ℕ => 1/(N:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have lim : Tendsto (fun N : ℕ => C*(u*(2+3*(1/(N:ℝ)))+H*(1/(N:ℝ))^2)) atTop (𝓝 (C*(u*2))) := by
    simpa using (((((inv.const_mul 3).const_add 2).const_mul u).add ((inv.pow 2).const_mul H)).const_mul C)
  have le := le_of_tendsto_of_tendsto tendsto_const_nhds lim
    (eventually_atTop.2 ⟨1,fun N hN => cmp N hN⟩)
  exact (div_le_iff₀ (by positivity : 0 < 2*C)).mpr (by linarith only [le])

/-- The aggregate implication in Corollary (positive), using (gainlo), (gainhi),
the mean endpoint-correlation bound, and convergence of the normalized scores. -/
theorem gain_positivity {p L W : ℝ} {G : ℕ → ℕ → ℝ} {b ω : ℕ → ℝ}
    (hp : 0 < p) (ph : p < 1/2) (hL : 0 ≤ L)
    (avg : ∀ N : ℕ, 0<N → N*L ≤ ∑ i ∈ range N, b (i+1))
    (lo : ∀ i j, ((1-2*p)^2/2)*b (i+1)^2*b (j+1)^2 ≤ G (i+1) (j+1))
    (hi : ∀ k, (∑ i ∈ range (k+1), G (i+1) (k-i+1)) ≤
      ((1/2-p)/√(p*(1-p)))*√(((k:ℝ)+2)*((k:ℝ)+1))*ω (k+2))
    (hω : ∀ k, 0 ≤ ω (k+2)) (conv : Tendsto ω atTop (𝓝 W)) :
    ((1-2*p)*√(p*(1-p))/2)*L^4 ≤ W := by
  let A := (1-2*p)^2/2
  let C := (1/2-p)/√(p*(1-p))
  have hr : 0 < 1-2*p := by linarith
  have hs : 0 < √(p*(1-p)) := Real.sqrt_pos.mpr (mul_pos hp (by linarith))
  have hC : 0 < C := div_pos (sub_pos.mpr ph) hs
  have relaxed (k : ℕ) :
      (∑ i ∈ range (k+1), G (i+1) (k-i+1)) ≤ C*(((k:ℝ)+2)*ω (k+2)) := by
    have x : 0 ≤ (k:ℝ)+1 := by positivity
    have y : 0 ≤ (k:ℝ)+2 := by positivity
    have sq : √(((k:ℝ)+2)*((k:ℝ)+1)) ≤ (k:ℝ)+2 := by
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) y).mp
      rw [Real.sq_sqrt (mul_nonneg y x)]
      nlinarith only [y]
    calc
      _ ≤ C*√(((k:ℝ)+2)*((k:ℝ)+1))*ω (k+2) := hi k
      _ ≤ (C*((k:ℝ)+2))*ω (k+2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left sq hC.le) (hω k)
      _ = _ := mul_assoc .. 
  have bound (N : ℕ) (hn : 0<N) :
      A*L^4*(N:ℝ)^2 ≤ C*∑ k ∈ range (2*N), ((k:ℝ)+2)*ω (k+2) := by
    rw [mul_sum]
    exact gain_sandwich (A := A) (by dsimp [A]; positivity) hL N (avg N hn) lo relaxed
  have inequality := aggregate_limit hC conv bound
  have coef : 2*C = (1-2*p)/√(p*(1-p)) := by unfold C; ring
  rw [coef] at inequality
  calc
    _ = A*L^4/((1-2*p)/√(p*(1-p))) := by
      dsimp [A]
      field_simp [hr.ne',hs.ne']
    _ ≤ _ := inequality

#print axioms square_gain_le_diagonals
#print axioms gain_positivity
end BlockHierarchy.VarianceLimit
