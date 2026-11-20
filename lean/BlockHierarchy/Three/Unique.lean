import BlockHierarchy.Three.FullBranch
import ReducedPair.ColumnEquality

open scoped BigOperators
namespace BlockHierarchy.Three

theorem cube_inverse {u : ℝ} (x z : Word) :
    ∑ y : Word, (-u)^hamming x y * u^hamming y z =
      if x=z then (1-u^2)^3 else 0 := by
  rw [word_sum]
  obtain ⟨i,j,k⟩ := x
  obtain ⟨a,b,c⟩ := z
  cases i <;> cases j <;> cases k <;> cases a <;> cases b <;> cases c <;>
    norm_num [hamming] <;> ring

theorem cube_injective {u : ℝ} (hu : 0 ≤ u) (h1 : u < 1) (v q : Word → ℝ)
    (eq : ∀ x, normalizer v u x=normalizer q u x) : v=q := by
  have nonzero : (1-u^2)^3 ≠ 0 := pow_ne_zero _ (by
    have := mul_pos (sub_pos.mpr h1) (show 0 < 1+u by linarith)
    nlinarith)
  have recover (a : Word → ℝ) (x : Word) :
      ∑ y, (-u)^hamming x y * normalizer a u y = a x*(1-u^2)^3 := by
    unfold normalizer
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have term (y z : Word) : (-u)^hamming x y*(a z*u^hamming y z)=
        a z*((-u)^hamming x y*u^hamming y z) := by ring
    simp_rw [term,← Finset.mul_sum,cube_inverse]
    simp [mul_ite]
  funext x
  apply (mul_left_inj' nonzero).mp
  rw [← recover v,← recover q]
  simp_rw [eq]

theorem unique_gibbs {p u b : ℝ} {z q : Word → ℝ} (hp : 0 < p) (ph : p < 1/2)
    (up : 0 < u) (uh : u < 1) (hz : ∀ x, 0 < z x)
    (test : ∀ y, (∑ x, FiniteRD.kernel (markov p) z hamming u x y) ≤ 1)
    (candidate : FiniteRD.Optimal (markov p) q hamming (FiniteRD.joint (markov p) z q hamming u) b)
    (cap : Channel.cost (fun x y => (hamming x y : ℝ)) (FiniteRD.joint (markov p) z q hamming u)=b)
    (t : Word → ℝ) (L : Word → Word → ℝ) (opt : FiniteRD.Optimal (markov p) t hamming L b) : t=q := by
  let P := markov p
  let K := FiniteRD.kernel P z hamming u
  let c (y : Word) := ∑ x, K x y
  let v (y : Word) := t y/c y
  have px := source_pos hp ph
  have pos (x y) : 0 < K x y := mul_pos (div_pos (px x) (hz x)) (pow_pos up _)
  have cp (y) : 0 < c y := Finset.sum_pos (fun x _ => pos x y) Finset.univ_nonempty
  obtain ⟨hJ,rows,cols,budget,_⟩ := candidate
  obtain ⟨hL,src,dst,bd,minimizes⟩ := opt
  have cmp := minimizes q _ hJ rows cols budget
  have logs (x y) : Real.log (K x y)=Real.log u*(hamming x y : ℝ)+(Real.log (P x)-Real.log (z x)) := by
    dsimp [K,FiniteRD.kernel]
    rw [Real.log_mul (div_pos (px x) (hz x)).ne' (pow_pos up _).ne',
      Real.log_div (px x).ne' (hz x).ne',Real.log_pow]
    ring
  have form := Channel.column_equality P q t K L (fun x y => (hamming x y : ℝ)) _ _
    (Real.log_nonpos up.le uh.le) pos hL (markov_mass p) rows cols src dst test logs
    (bd.trans_eq cap.symm) cmp
  have vrow (x : Word) : ∑ y, v y*K x y=P x := by
    change ∑ y, t y/(∑ i, K i y)*K x y=_
    simp_rw [← form]; exact src x
  have conv (a : Word → ℝ) (x : Word) :
      ∑ y, a y*K x y=P x/z x*normalizer a u x := by
    change ∑ y, a y*(P x/z x*u^hamming x y)=_
    simp_rw [mul_left_comm (a _) (P x/z x),← Finset.mul_sum]; rfl
  have eq : v=q := cube_injective up.le uh v q (fun x => by
    apply mul_left_cancel₀ (div_pos (px x) (hz x)).ne'
    rw [← conv,← conv,vrow]; exact (rows x).symm)
  funext y
  have ac := cols y
  change ∑ x, q y*K x y=q y at ac
  rw [← Finset.mul_sum] at ac
  exact ((div_eq_iff (cp y).ne').mp (congrFun eq y)).trans ac

end BlockHierarchy.Three
