import BlockHierarchy.Cut.Flips

namespace BlockHierarchy.VarianceLimit
open Cut Varentropy

def appendBit : (k : ℕ) → Bits k → Bool → Bits (k+1)
  | 0, _, b => (b,())
  | k+1, w, b => (w.1,appendBit k w.2 b)

def reverseBits : (k : ℕ) → Bits k → Bits k
  | 0, _ => ()
  | k+1, w => appendBit k (reverseBits k w.2) w.1

private theorem reverse_append (k : ℕ) (w : Bits k) (b : Bool) :
    reverseBits (k+1) (appendBit k w b)=(b,reverseBits k w) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change appendBit (k+1) (reverseBits (k+1) (appendBit k w.2 b)) w.1=_
    rw [ih]
    rfl

theorem reverse_reverse (k : ℕ) (w : Bits k) : reverseBits k (reverseBits k w)=w := by
  induction k with
  | zero => cases w; rfl
  | succ k ih =>
    change reverseBits (k+1) (appendBit k (reverseBits k w.2) w.1)=w
    rw [reverse_append,ih]; rfl

def reverseEquiv (k : ℕ) : Bits k ≃ Bits k :=
  ⟨reverseBits k,reverseBits k,reverse_reverse k,reverse_reverse k⟩

private theorem complement_append (k : ℕ) (w : Bits k) (b : Bool) :
    complement (k+1) (appendBit k w b)=appendBit k (complement k w) (!b) := by
  induction k with
  | zero => rfl
  | succ k ih => change (!w.1,complement (k+1) (appendBit k w.2 b))=_; rw [ih]; rfl

theorem complement_reverse (k : ℕ) (w : Bits k) :
    complement k (reverseBits k w)=reverseBits k (complement k w) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change complement (k+1) (appendBit k (reverseBits k w.2) w.1)=_
    rw [complement_append,ih]; rfl

private theorem hamming_append (k : ℕ) (x y : Bits k) (a b : Bool) :
    hamming (k+1) (appendBit k x a) (appendBit k y b)=hamming k x y+(if a=b then 0 else 1) := by
  induction k with
  | zero => simp [appendBit,hamming]; rfl
  | succ k ih =>
    change (if x.1=y.1 then 0 else 1)+hamming (k+1) (appendBit k x.2 a) (appendBit k y.2 b)=_
    rw [ih]
    simp only [hamming,Nat.add_assoc]

theorem reverse_distance (n : ℕ) (x y : Word n) :
    distance n (reverseBits (n+1) x) (reverseBits (n+1) y)=distance n x y := by
  have h (k : ℕ) (x y : Bits k) : hamming k (reverseBits k x) (reverseBits k y)=hamming k x y := by
    induction k with
    | zero => rfl
    | succ k ih => change hamming (k+1) (appendBit k _ _) (appendBit k _ _)=_; rw [hamming_append,ih]; exact Nat.add_comm _ _
  exact h _ _ _

private theorem last_append (k : ℕ) (w : Bits k) (a b : Bool) :
    lastBit a (k+1) (appendBit k w b)=b := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => exact ih w.2 w.1

theorem reverse_last (n : ℕ) (x : Word n) : last (reverseBits (n+1) x)=x.1 := by
  cases n with
  | zero => rfl
  | succ n => exact last_append n _ _ _

theorem reverse_first (n : ℕ) (x : Word n) : (reverseBits (n+1) x).1=last x := by
  have h := reverse_last n (reverseBits (n+1) x)
  rw [reverse_reverse] at h
  exact h.symm

private theorem tail_append (p : ℝ) (n : ℕ) (a b : Bool) (w : Bits n) :
    tail p a (n+1) (appendBit n w b)=tail p a n w*Cut.step p (lastBit a n w) b := by
  induction n generalizing a with
  | zero => simp [appendBit,tail,lastBit]
  | succ n ih =>
    change Cut.step p a w.1*tail p w.1 (n+1) (appendBit n w.2 b)=_
    rw [ih]
    simp only [tail,lastBit,mul_assoc]

theorem reverse_mass (p : ℝ) (n : ℕ) (x : Word n) :
    mass p n (reverseBits (n+1) x)=mass p n x := by
  have aux (k : ℕ) (y : Word k) :
      tail p (reverseBits (k+1) y).1 k (reverseBits (k+1) y).2=tail p y.1 k y.2 := by
    induction k with
    | zero => rfl
    | succ k ih =>
      let w := reverseBits (k+1) y.2
      change tail p w.1 (k+1) (appendBit k w.2 y.1)=_
      rw [tail_append]
      have last' : lastBit w.1 k w.2=y.2.1 := reverse_last k y.2
      have eq : tail p w.1 k w.2=tail p y.2.1 k y.2.2 := ih y.2
      rw [last',eq]
      have symm : Cut.step p y.2.1 y.1=Cut.step p y.1 y.2.1 := by
        cases y.2.1 <;> cases y.1 <;> rfl
      rw [symm,mul_comm]
      rfl
  exact congrArg (fun t : ℝ => (1/2:ℝ)*t) (aux n x)

end BlockHierarchy.VarianceLimit
