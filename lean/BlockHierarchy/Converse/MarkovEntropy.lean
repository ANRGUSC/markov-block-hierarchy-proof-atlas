import BlockHierarchy.Cut.Flips

open scoped BigOperators
namespace BlockHierarchy.Converse
open Cut Varentropy

/-- Entropy in nats of the stationary path with n transitions. -/
theorem markov_entropy {p : ℝ} (hp : 0<p) (ph : p<1) (n : ℕ) :
    -mean (mass p n) (fun x => Real.log (mass p n x))=Real.log 2 + n*binaryEntropyNats p := by
  have pp : 0<1-p := sub_pos.mpr ph
  have col (b : Bool) : ∑ a, Cut.step p a b=1 := by cases b <;> simp [Cut.step] <;> ring
  have entropy (b : Bool) : ∑ a, Cut.step p a b*Real.log (Cut.step p a b)= -binaryEntropyNats p := by
    cases b <;> simp [Cut.step,binaryEntropyNats] <;> ring
  induction n with
  | zero =>
    have point (x : Word 0) : mass p 0 x=2⁻¹ := by simp [mass,tail,one_div]
    unfold mean
    have logs (x : Word 0) : Real.log (mass p 0 x)= -Real.log 2 := by rw [point,Real.log_inv]
    simp only [logs,←Finset.sum_mul,mass_sum hp ph 0,one_mul,neg_neg,Nat.cast_zero,zero_mul,add_zero]
  | succ n ih =>
    have h (a : Bool) (w : Word n) : mass p (n+1) (a,w)=mass p n w*Cut.step p a w.1 := by
      unfold mass
      change (1/2:ℝ)*(Cut.step p a w.1*tail p w.1 n w.2)=_
      ring
    have inner (w : Word n) :
        ∑ a, mass p (n+1) (a,w)*Real.log (mass p (n+1) (a,w)) =
          mass p n w*Real.log (mass p n w)-mass p n w*binaryEntropyNats p := by
      have term (a : Bool) : mass p (n+1) (a,w)*Real.log (mass p (n+1) (a,w)) =
          (mass p n w*Real.log (mass p n w))*Cut.step p a w.1+
          mass p n w*(Cut.step p a w.1*Real.log (Cut.step p a w.1)) := by
        have sp : 0 < Cut.step p a w.1 := by unfold Cut.step; split <;> assumption
        rw [h,Real.log_mul (mass_pos hp ph n w).ne' sp.ne']; ring
      simp_rw [term,Finset.sum_add_distrib,←Finset.mul_sum,col,entropy]
      ring
    unfold mean
    rw [sum_next,Finset.sum_comm]
    simp_rw [inner,Finset.sum_sub_distrib,←Finset.sum_mul,mass_sum hp ph n]
    unfold mean at ih
    push_cast
    linarith

end BlockHierarchy.Converse
