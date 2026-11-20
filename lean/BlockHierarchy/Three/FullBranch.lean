import BlockHierarchy.LosslessRD
import BlockHierarchy.Three.Entropy
import BlockHierarchy.Three.FullWeights

open scoped BigOperators
namespace BlockHierarchy.Three

theorem hamming_zero (x y : Word) : hamming x y=0 ↔ x=y := by
  obtain ⟨i,j,k⟩ := x
  obtain ⟨a,b,c⟩ := y
  cases i <;> cases j <;> cases k <;> cases a <;> cases b <;> cases c <;> decide

theorem zero_kernel (x y : Word) : (0:ℝ)^hamming x y=if x=y then 1 else 0 := by
  by_cases e : x=y
  · simp [e,(hamming_zero y y).mpr rfl]
  · simp [e,zero_pow (fun h => e ((hamming_zero x y).mp h))]

theorem cube_columns {u : ℝ} (hu : 0 ≤ u) (y : Word) :
    (∑ x, u^hamming x y/(1+u)^3)=1 ∧
    (∑ x, u^hamming x y/(1+u)^3*(hamming x y : ℝ))=3*u/(1+u) := by
  have h : 0 < 1+u := by linarith
  constructor <;> rw [word_sum] <;> obtain ⟨i,j,k⟩ := y
  all_goals cases i <;> cases j <;> cases k <;>
    norm_num [hamming] <;> field_simp [h.ne'] <;> ring

theorem full_branch {p D : ℝ} (hp : 0 < p) (ph : p < 1/2) (hd : 0 ≤ D)
    (bound : D ≤ criticalD p) :
    let u := D/(1-D)
    let z := fun x => (1+u)^3*markov p x
    let q := fullPrior p D
    let J := FiniteRD.joint (markov p) z q hamming u
    (∀ x, normalizer q u x=z x) ∧ (∀ y, 0 < q y ↔ flips y < 2 ∨ D < criticalD p) ∧
    FiniteRD.Optimal (markov p) q hamming J (3*D) ∧
    Channel.info (markov p) q J/Real.log 2=1+2*binaryEntropy p-3*binaryEntropy D ∧
    tilted p (3*D) u z=2*nu p := by
  obtain ⟨_,ch,_,_,_,_,_,_⟩ := thresholds hp ph
  have dh := bound.trans_lt ch
  have pos := source_pos hp ph
  let u := D/(1-D)
  let q := fullPrior p D
  let z := fun x => (1+u)^3*markov p x
  have dm : 0 < 1-D := by linarith
  have hu : 0 ≤ u := div_nonneg hd dm.le
  have uh : u < 1 := (div_lt_one dm).mpr (by linarith)
  have plus : 0 < 1+u := by linarith
  have norm := full_normalizer (p := p) dh
  obtain ⟨hq,support⟩ := full_support hp ph bound
  obtain ⟨rate,var⟩ := entropy_tilt_values hp ph hd dh
  refine ⟨norm,support,?_⟩
  have ker (x y : Word) : FiniteRD.kernel (markov p) z hamming u x y=u^hamming x y/(1+u)^3 := by
    unfold FiniteRD.kernel z
    field_simp [plus.ne',(pos x).ne']
  have hz (x : Word) : 0 < z x := mul_pos (pow_pos plus _) (pos x)
  by_cases positive : 0 < D
  ·
    have up : 0 < u := div_pos positive dm
    have total : ∑ y, q y=1 := (prior_total ..).trans (full_total dh)
    have cap : Channel.cost (fun x y => (hamming x y : ℝ))
        (FiniteRD.joint (markov p) z q hamming u)=3*D := by
      unfold Channel.cost FiniteRD.joint
      simp_rw [ker]
      rw [Finset.sum_comm]
      simp only [mul_assoc,← Finset.mul_sum, (cube_columns hu _).2,← Finset.sum_mul,total,one_mul]
      apply (div_eq_iff plus.ne').mpr
      have em : u*(1-D)=D := div_mul_cancel₀ _ dm.ne'
      linarith only [em]
    have cols (y : Word) : (∑ x, FiniteRD.kernel (markov p) z hamming u x y) ≤ 1 ∧
        (q y≠0 → ∑ x, FiniteRD.kernel (markov p) z hamming u x y=1) := by
      simp_rw [ker,(cube_columns hu y).1]
      simp
    have cert := FiniteRD.certificate pos hz hq up uh.le norm cols cap
    exact ⟨cert.1,cert.2.trans rate,var⟩
  · have zero : 0=D := le_antisymm hd (le_of_not_gt positive)
    have u0 : u=0 := by dsimp [u]; rw [← zero]; norm_num
    have z0 : z=markov p := by funext x; simp [z,u0]
    have q0 : q=markov p := by
      funext x
      have n : normalizer q u x=z x := norm x
      simpa [normalizer,u0,zero_kernel,z0] using n
    have diag : FiniteRD.joint (markov p) z q hamming u =
        fun x y => if x=y then markov p x else 0 := by
      funext x y
      rw [FiniteRD.joint,FiniteRD.kernel,u0,z0,q0,zero_kernel]
      by_cases e : x=y
      · subst y; simp [(pos x).ne']
      · simp [e]
    have cert := FiniteRD.lossless (fun x => (pos x).le) hamming_zero
    refine ⟨?_,?_,var⟩
    · change FiniteRD.Optimal (markov p) q hamming (FiniteRD.joint (markov p) z q hamming u) (3*D)
      rw [diag,q0,← zero,mul_zero]; exact cert.1
    · change Channel.info (markov p) q (FiniteRD.joint (markov p) z q hamming u)/Real.log 2=_
      rw [diag,q0]; refine cert.2.trans ?_
      simpa [← zero,binaryEntropy,logTwo] using (source_moments hp ph).1

end BlockHierarchy.Three
