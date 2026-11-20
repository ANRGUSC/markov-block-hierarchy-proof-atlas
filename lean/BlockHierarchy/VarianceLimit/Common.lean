import BlockHierarchy.VarianceLimit.Statement
import BlockHierarchy.VarianceLimit.Cut
import BlockHierarchy.Cut.Continuity
import Mathlib.Topology.UniformSpace.UniformApproximation

open Filter Topology
namespace BlockHierarchy.VarianceLimit
open Cut

noncomputable def commonOmega (p τ : ℝ) :=
  limUnder atTop (fun n : ℕ => blockSD p τ n / Real.sqrt n)

private theorem limit_spec {p τ : ℝ} (hp : 0<p) (ph : p<1/2) (ht : 0≤τ) :
    0≤commonOmega p τ ∧
    Tendsto (fun n : ℕ => blockSD p τ n / Real.sqrt n) atTop (𝓝 (commonOmega p τ)) ∧
    ∀ n : ℕ, 0<n → |blockSD p τ n / Real.sqrt n - commonOmega p τ| ≤
      (1+Real.sqrt 2)*Real.sqrt (1-2*p)/Real.sqrt n := by
  have hsd (n : ℕ) (_ : 0<n) : 0 ≤ blockSD p τ n := by
    cases n <;> simp [blockSD,Real.sqrt_nonneg]
  obtain ⟨L,hL,t,e⟩ := common_limit hsd (block_cut hp ph ht)
  have eq : commonOmega p τ=L := t.limUnder_eq
  exact eq.symm ▸ ⟨hL,t,e⟩

theorem commonOmega_nonneg {p τ : ℝ} (hp : 0<p) (ph : p<1/2) (ht : 0≤τ) :
    0≤commonOmega p τ := (limit_spec hp ph ht).1

theorem omegaAt_enclosure {p τ : ℝ} (hp : 0<p) (ph : p<1/2) (ht : 0≤τ)
    (n : ℕ) {q : Word n → ℝ} (hq : Optimal (mass p n) τ (distance n) q) :
    |omegaAt p τ n q-commonOmega p τ| ≤ (1+Real.sqrt 2)*Real.sqrt ((1-2*p)/((n:ℝ)+1)) := by
  have hz := optimal_Z_eq (mass_pos hp (by linarith) n) hq (canonical_optimal p τ n)
  have eq : score τ (distance n) q = blockScore p τ n := by
    funext x
    unfold blockScore score
    rw [hz]
  rw [omegaAt,eq,Real.sqrt_div (by linarith),←mul_div_assoc]
  simpa only [Nat.cast_succ,blockSD] using (limit_spec hp ph ht).2.2 (n+1) (Nat.succ_pos n)

theorem commonOmega_zero (p : ℝ) : commonOmega p 0=0 := by
  have zero (n : ℕ) : blockScore p 0 n = fun _ => 0 := by
    funext x
    simp [blockScore,score,Z,(canonical_optimal p 0 n).1.2]
  have sd (n : ℕ) : blockSD p 0 n=0 := by
    cases n with
    | zero => rfl
    | succ n => simp [blockSD,zero,variance,mean]
  apply Filter.Tendsto.limUnder_eq
  simpa only [sd,zero_div] using (tendsto_const_nhds (x := (0:ℝ)) (f := (atTop : Filter ℕ)))

theorem commonOmega_continuous {p : ℝ} (hp : 0<p) (ph : p<1/2) :
    ContinuousOn (commonOmega p) (Set.Ici 0) := by
  let F (n : ℕ) (τ : ℝ) := omegaAt p τ n (canonicalPrior p τ n)
  have cont (n : ℕ) : Continuous (F n) := by
    simpa only [F,omegaAt, Nat.cast_succ] using continuous_optimal_sd
      (mass_pos hp (by linarith) n) (distance n) (n+1)
      (fun t => canonicalPrior p t n) (fun t => canonical_optimal p t n)
  have err : Tendsto (fun n : ℕ => (1+Real.sqrt 2)*Real.sqrt ((1-2*p)/((n:ℝ)+1))) atTop (𝓝 0) := by
    have h := ((tendsto_const_nhds (x:=1-2*p)).mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))).sqrt
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x:=1+Real.sqrt 2)).mul h
  have uniform : TendstoUniformlyOn F (commonOmega p) atTop (Set.Ici 0) := by
    apply Metric.tendstoUniformlyOn_iff.2
    intro ε hε
    filter_upwards [err.eventually_lt_const hε] with n hn t ht
    rw [dist_comm,Real.dist_eq]
    exact (omegaAt_enclosure hp ph ht n (canonical_optimal p t n)).trans_lt hn
  exact uniform.continuousOn (Eventually.of_forall (fun n => (cont n).continuousOn)).frequently

#print axioms commonOmega_continuous
#print axioms commonOmega_zero
#print axioms omegaAt_enclosure
end BlockHierarchy.VarianceLimit