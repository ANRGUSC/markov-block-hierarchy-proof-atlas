import BlockHierarchy.Varentropy.Covariance

namespace BlockHierarchy.Varentropy

theorem transition_positive (m : BinaryModel) (x y : Bool) : 0<transition m x y := by
  cases x <;> cases y <;> first | exact m.apos | exact m.bpos | exact sub_pos.mpr m.alt | exact sub_pos.mpr m.blt

theorem pi_positive (m : BinaryModel) (x : Bool) : 0<pi m x := by
  cases x <;> first | exact m.ppos | exact m.qpos

theorem tail_positive (m : BinaryModel) (n : ℕ) (x : Bool) (w : Bits n) : 0<tailLaw m x n w := by
  induction n generalizing x with
  | zero => exact zero_lt_one
  | succ n ih => exact mul_pos (transition_positive m x w.1) (ih w.1 w.2)

theorem path_positive (m : BinaryModel) (n : ℕ) (w : Bits (n+1)) : 0<pathLaw m n w :=
  mul_pos (pi_positive m w.1) (tail_positive m n w.1 w.2)

private theorem logTwo_mul {x y : ℝ} (hx : 0<x) (hy : 0<y) :
    logTwo (x*y)=logTwo x+logTwo y := by
  unfold logTwo
  rw [Real.log_mul hx.ne' hy.ne',add_div]

theorem score_eq (m : BinaryModel) (n : ℕ) (w : Bits (n+1)) :
    -logTwo (pathLaw m n w)=B m w.1+edgeSum m w.1 n w.2 := by
  have tail (k : ℕ) (a : Bool) (v : Bits k) : -logTwo (tailLaw m a k v)=edgeSum m a k v := by
    induction k generalizing a with
    | zero => simp [tailLaw,edgeSum,logTwo]
    | succ k ih =>
      rw [tailLaw,logTwo_mul (transition_positive ..) (tail_positive ..),neg_add,ih]
      rfl
  rw [pathLaw,logTwo_mul (pi_positive ..) (tail_positive ..),neg_add,tail]
  rfl

theorem backward_variance (m : BinaryModel) (n : ℕ) (D : ℝ) (q : Bits (n+1) → ℝ)
    (h : BackwardPoint m n D q) : tiltedVariance m n D q=blockVariance m n := by
  obtain ⟨lo,hi,_,_,normal⟩ := h
  let u := D/(1-D)
  have p1 : m.p<1 := by linarith only [m.normalized,m.qpos]
  have D1 := (hi.trans_le (min_le_left ..)).trans p1
  have un : 0≤u := div_nonneg lo (sub_pos.mpr D1).le
  let a := (1+u)^(n+1)
  have ap : 0<a := pow_pos (by linarith only [un]) _
  have eq (x : Bits (n+1)) : normalizer u q x=pathLaw m n x*a := (div_eq_iff ap.ne').mp (normal x)
  let c := ((n:ℝ)+1)*D*logTwo u-logTwo a
  have shift : (fun x => ((n:ℝ)+1)*D*logTwo u-logTwo (normalizer u q x))=
      (fun x => c+(-logTwo (pathLaw m n x))) := by
    funext x
    rw [eq,logTwo_mul (path_positive ..) ap]
    unfold c
    ring
  change variance (pathLaw m n) _ = _
  rw [shift]
  exact variance_shift (pathLaw m n) _ (path_mass m n) c

end BlockHierarchy.Varentropy
