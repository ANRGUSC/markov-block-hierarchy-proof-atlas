import BlockHierarchy.Three.PaperStatement
import BlockHierarchy.Three.Unique

open scoped BigOperators
namespace BlockHierarchy.Three

private theorem zero_marginal {p : ℝ} {t : Word → ℝ} {L : Word → Word → ℝ}
    (opt : FiniteRD.Optimal (markov p) t hamming L 0) : t=markov p := by
  obtain ⟨hL,src,dst,budget,_⟩ := opt
  have point (x y) : 0 ≤ L x y*(hamming x y : ℝ) := mul_nonneg (hL x y) (Nat.cast_nonneg _)
  have off (x y) (ne : x ≠ y) : L x y=0 := by
    have bound : L x y*(hamming x y : ℝ) ≤ Channel.cost (fun x y => (hamming x y : ℝ)) L :=
      (Finset.single_le_sum (fun j _ => point x j) (Finset.mem_univ y)).trans
      (Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => point i j)) (Finset.mem_univ x))
    exact (mul_eq_zero.mp (le_antisymm (bound.trans budget) (point x y))).resolve_right
      (Nat.cast_ne_zero.mpr (fun h => ne ((hamming_zero x y).mp h)))
  funext y
  rw [← dst y,← src y,Finset.sum_eq_single y,Finset.sum_eq_single y]
  · intro j _ ne; exact off y j ne.symm
  · simp
  · intro i _ ne; exact off i y ne
  · simp

theorem full_paper_point {p D : ℝ} (hp : 0 < p) (ph : p < 1/2) (hd : 0 ≤ D)
    (bound : D ≤ criticalD p) :
    let u := D/(1-D)
    let z := fun x => (1+u)^3*markov p x
    PaperPoint p D u (fullPrior p D) z (1+2*binaryEntropy p-3*binaryEntropy D) (2*nu p) := by
  let u := D/(1-D)
  let z := fun x => (1+u)^3*markov p x
  let q := fullPrior p D
  have dh := bound.trans_lt (thresholds hp ph).2.1
  have dm : 0 < 1-D := by linarith
  have hu : 0 ≤ u := div_nonneg hd dm.le
  have uh : u < 1 := (div_lt_one dm).mpr (by linarith)
  have plus : 0 < 1+u := by linarith
  have pos := source_pos hp ph
  have hz (x : Word) : 0 < z x := mul_pos (pow_pos plus _) (pos x)
  have ker (x y : Word) : FiniteRD.kernel (markov p) z hamming u x y=u^hamming x y/(1+u)^3 := by
    unfold FiniteRD.kernel z
    field_simp [plus.ne',(pos x).ne']
  have cols (y : Word) : (∑ x, FiniteRD.kernel (markov p) z hamming u x y) ≤ 1 := by
    simp_rw [ker,(cube_columns hu y).1]; exact le_rfl
  have total : ∑ y, q y=1 := (prior_total ..).trans (full_total dh)
  have cap : Channel.cost (fun x y => (hamming x y : ℝ)) (FiniteRD.joint (markov p) z q hamming u)=3*D := by
    unfold Channel.cost FiniteRD.joint
    simp_rw [ker]
    rw [Finset.sum_comm]
    simp only [mul_assoc,← Finset.mul_sum, (cube_columns hu _).2,← Finset.sum_mul,total,one_mul]
    apply (div_eq_iff plus.ne').mpr
    have em : u*(1-D)=D := div_mul_cancel₀ _ dm.ne'
    linarith only [em]
  obtain ⟨norm,_,opt,rate,var⟩ := full_branch hp ph hd bound
  refine ⟨norm,cap,opt,?_,rate,var⟩
  intro t L hL
  rcases eq_or_lt_of_le hd with e | positive
  · subst D
    have tq := zero_marginal (by simpa using hL)
    have fq := zero_marginal (by simpa using opt)
    exact tq.trans fq.symm
  · exact unique_gibbs hp ph (div_pos positive dm) uh hz cols opt cap t L hL

end BlockHierarchy.Three
