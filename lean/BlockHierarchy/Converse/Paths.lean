import BlockHierarchy.Cut.Flips

namespace BlockHierarchy.Converse
open Cut Varentropy

def flipAfter (x b : Bool) := if b then !x else x

def fromFlips (x : Bool) : (n : ℕ) → Bits n → Bits n
  | 0, _ => ()
  | n+1, w => (flipAfter x w.1, fromFlips (flipAfter x w.1) n w.2)

def toFlips (x : Bool) : (n : ℕ) → Bits n → Bits n
  | 0, _ => ()
  | n+1, w => (decide (x≠w.1), toFlips w.1 n w.2)

def flipEquiv (x : Bool) (n : ℕ) : Bits n ≃ Bits n where
  toFun := fromFlips x n
  invFun := toFlips x n
  left_inv := by
    induction n generalizing x with
    | zero => intro w; cases w; rfl
    | succ n ih =>
      intro w
      obtain ⟨b,w⟩ := w
      cases x <;> cases b <;> simp [fromFlips,toFlips,flipAfter,ih false w,ih true w] <;> rfl
  right_inv := by
    induction n generalizing x with
    | zero => intro w; cases w; rfl
    | succ n ih =>
      intro w
      obtain ⟨y,w⟩ := w
      cases x <;> cases y <;> simp [fromFlips,toFlips,flipAfter,ih false w,ih true w] <;> rfl

def flipCount : (n : ℕ) → Bits n → ℕ
  | 0, _ => 0
  | n+1, w => (if w.1 then 1 else 0) + flipCount n w.2

noncomputable def iidFlips (p : ℝ) : (n : ℕ) → Bits n → ℝ
  | 0, _ => 1
  | n+1, w => (if w.1 then p else 1-p)*iidFlips p n w.2

theorem tail_flips (p : ℝ) (n : ℕ) (x : Bool) (w : Bits n) :
    tail p x n (fromFlips x n w) = iidFlips p n w := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    obtain ⟨b,w⟩ := w
    cases b <;> cases x <;> simp [tail,fromFlips,iidFlips,flipAfter,Cut.step,ih]

theorem path_from_flips (p : ℝ) (n : ℕ) (x : Bool) (w : Bits n) :
    mass p n (x, flipEquiv x n w) = (1/2:ℝ)*iidFlips p n w := by
  exact congrArg (fun t : ℝ => (1/2:ℝ)*t) (tail_flips p n x w)

private theorem iid_pos {p : ℝ} (hp : 0<p) (h1 : p<1) (n : ℕ) (w : Bits n) :
    0 < iidFlips p n w := by
  induction n with
  | zero => exact zero_lt_one
  | succ n ih =>
    obtain ⟨b,w⟩ := w
    change 0<(if b then p else 1-p)*iidFlips p n w
    exact mul_pos (by split <;> linarith) (ih _)

theorem iid_log {p : ℝ} (hp : 0<p) (h1 : p<1) (n : ℕ) (w : Bits n) :
    -Real.log (iidFlips p n w) = -(n:ℝ)*Real.log (1-p)+
      (flipCount n w : ℝ)*Real.log ((1-p)/p) := by
  induction n with
  | zero => simp [iidFlips,flipCount]
  | succ n ih =>
    obtain ⟨b,w⟩ := w
    have h' := ih w
    have hn : 0 < 1-p := by linarith
    rw [Real.log_div hn.ne' hp.ne'] at h'
    cases b <;> simp only [iidFlips,flipCount,Bool.false_eq_true,ite_false,ite_true,
      Nat.cast_add,Nat.cast_one,Nat.cast_zero,Nat.cast_succ,Real.log_mul hn.ne' (iid_pos hp h1 n w).ne',
      Real.log_mul hp.ne' (iid_pos hp h1 n w).ne',Real.log_div hn.ne' hp.ne'] <;> linarith

/-- The true symmetric path score is an affine function of its n independent
Bernoulli flips; the initial uniform bit adds log 2 nats. -/
theorem path_information {p : ℝ} (hp : 0<p) (h1 : p<1) (n : ℕ) (x : Bool) (w : Bits n) :
    -Real.log (mass p n (x,flipEquiv x n w)) =
      Real.log 2 -(n:ℝ)*Real.log (1-p)+(flipCount n w : ℝ)*Real.log ((1-p)/p) := by
  rw [path_from_flips,Real.log_mul (by norm_num) (iid_pos hp h1 n w).ne',one_div,Real.log_inv]
  linarith [iid_log hp h1 n w]

#print axioms path_information
end BlockHierarchy.Converse
