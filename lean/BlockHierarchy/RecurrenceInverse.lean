import BlockHierarchy.RecurrenceStatement

open scoped BigOperators
namespace BlockHierarchy.Recurrence

private theorem wsCong {n : ℕ} {f g : List Bool → ℝ}
    (h : ∀ w, w.length=n → f w=g w) : wordSum n f=wordSum n g := by
  induction n generalizing f g with
  | zero => exact h [] rfl
  | succ n ih => unfold wordSum; apply Finset.sum_congr rfl; intro b _; apply ih
                 intro w hw; exact h (b::w) (by simp [hw])

private theorem wsAdd (n : ℕ) (f g : List Bool → ℝ) :
    wordSum n (fun w => f w+g w)=wordSum n f+wordSum n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih => simp only [wordSum,ih,Finset.sum_add_distrib]

private theorem wsMul (n : ℕ) (a : ℝ) (f : List Bool → ℝ) :
    wordSum n (fun w => a*f w)=a*wordSum n f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => simp only [wordSum,ih,Finset.mul_sum]

private theorem wsSwap (m n : ℕ) (f : List Bool → List Bool → ℝ) :
    wordSum m (fun x => wordSum n (f x))=wordSum n (fun y => wordSum m (fun x => f x y)) := by
  induction m generalizing f with
  | zero => rfl
  | succ m ih => simp only [wordSum,Fintype.sum_bool,wsAdd,← ih]

private theorem wsPick (y : List Bool) (f : List Bool → ℝ) :
    wordSum y.length (fun x => if x=y then f x else 0)=f y := by
  induction y generalizing f with
  | nil => simp [wordSum]
  | cons b y ih =>
    have zero (n : ℕ) : wordSum n (fun _ => 0)=0 := by simpa using wsMul n 0 (fun _ => 0)
    cases b <;> simp [wordSum,Fintype.sum_bool,ih,zero]

private theorem expSwap (p : ℝ) (a : Bool) (n k : ℕ) (f : List Bool → Bool → List Bool → ℝ) :
    expectFrom p a n (fun x t => wordSum k (f x t)) =
      wordSum k (fun y => expectFrom p a n (fun x t => f x t y)) := by
  induction n generalizing a f with
  | zero => rfl
  | succ n ih => simp only [expectFrom,Fintype.sum_bool,wsAdd,wsMul,← ih]

private theorem expCong (p : ℝ) (a : Bool) (n : ℕ) (f g : List Bool → Bool → ℝ)
    (h : ∀ w, w.length=n → ∀ t, f w t=g w t) : expectFrom p a n f=expectFrom p a n g := by
  induction n generalizing a f g with
  | zero => exact h [] rfl a
  | succ n ih =>
    unfold expectFrom; apply Finset.sum_congr rfl; intro b _
    congr 1; apply ih; intro w hw t; exact h _ (by simp [hw]) t

private theorem expectation_sum (p : ℝ) (n : ℕ) (f : List Bool → ℝ) :
    markovExpect p n (fun x _ => f x)=wordSum n (fun x => pathLaw p x*f x) := by
  let terms (x y : List Bool) := if y=x then f y else 0
  have eval (a : Bool) : expectFrom p a n (fun x _ => f x)=
      wordSum n (fun y => expectFrom p a n (fun x _ => terms x y)) := by
    rw [← expSwap]; apply expCong; intro w hw t; rw [← hw]; exact (wsPick w f).symm
  have scale (a : Bool) (n : ℕ) (f : List Bool → Bool → ℝ) (c : ℝ) :
      expectFrom p a n (fun w t => c*f w t)=c*expectFrom p a n f := by
    induction n generalizing a f with
    | zero => rfl
    | succ n ih => simp only [expectFrom,Fintype.sum_bool,ih]; ring
  unfold markovExpect; simp only [Fintype.sum_bool,eval]
  rw [← wsAdd,div_eq_inv_mul,← wsMul]
  apply wsCong; intro y hy
  unfold terms pathLaw markovExpect; rw [hy]
  simp only [Fintype.sum_bool]
  simp_rw [show ∀ x : List Bool, (if y=x then f y else 0) =
    f y*(if x=y then 1 else 0) by intro x; by_cases h : x=y <;> simp [h,Ne.symm]]
  rw [scale,scale]; ring

private theorem tensor_inverse (n : ℕ) (a b : Bool → Bool → ℝ)
    (h : ∀ i j, (∑ k : Bool, a i k*b k j)=if i=j then 1 else 0)
    (x y : List Bool) (hx : x.length=n) (hy : y.length=n) :
    wordSum n (fun w => wordWeight a x w*wordWeight b w y)=if x=y then 1 else 0 := by
  induction n generalizing x y with
  | zero => cases x <;> cases y <;> simp_all [wordSum,wordWeight]
  | succ n ih =>
    cases x with
    | nil => simp at hx
    | cons i x =>
      cases y with
      | nil => simp at hy
      | cons j y =>
        simp only [List.length_cons,Nat.succ.injEq] at hx hy
        simp only [wordSum,wordWeight]
        simp_rw [show ∀ k w, a i k*wordWeight a x w*(b k j*wordWeight b w y)=
          (a i k*b k j)*(wordWeight a x w*wordWeight b w y) by intros; ring]
        simp only [wsMul,ih x y hx hy,← Finset.sum_mul,h]
        by_cases e : i=j <;> by_cases e' : x=y <;> simp [e,e']

private theorem apply_inverse (k : ℕ) (a b : Bool → Bool → ℝ) (q : List Bool → ℝ)
    (h : ∀ i j, (∑ t : Bool, a i t*b t j)=if i=j then 1 else 0)
    (y : List Bool) (hy : y.length=k) :
    wordSum k (fun x => wordSum k (fun w => q w*wordWeight a w x)*wordWeight b x y)=q y := by
  simp_rw [mul_comm (wordSum k _) _,← wsMul]
  rw [wsSwap]
  conv_rhs => rw [← wsPick y q,hy]
  apply wsCong; intro w hw
  simp_rw [show ∀ x, wordWeight b x y*(q w*wordWeight a w x)=
    q w*(wordWeight a w x*wordWeight b x y) by intro x; ring]
  rw [wsMul,tensor_inverse k a b h w y hw hy]
  split <;> simp_all

private theorem symmetric_marginal (k : ℕ) (a : Bool → Bool → ℝ) (q law : List Bool → ℝ)
    (sym : ∀ x y, wordWeight a x y = wordWeight a y x)
    (marginal : ∀ x, x.length = k → wordSum k (fun w => q w * wordWeight a x w) = law x)
    (x : List Bool) (hx : x.length = k) :
    wordSum k (fun w => q w * wordWeight a w x) = law x := by
  refine Eq.trans (wsCong (g := fun w => q w * wordWeight a x w) ?_) (marginal x hx)
  intro w _
  exact congrArg (fun c => q w * c) (sym w x)

theorem backward_iff_inverse {p D : ℝ} (hd : D<1/2) (k : ℕ) :
    BackwardFeasible p D k ↔ InverseNonnegative p (1-2*D) k := by
  let a := backWeight D
  let b := invWeight (1-2*D)
  have nz : 1-2*D ≠ 0 := by linarith
  have ab : ∀ i j, (∑ t : Bool, a i t*b t j)=if i=j then 1 else 0 := by
    intro i j; cases i <;> cases j <;> simp [a,b,backWeight,invWeight,spin] <;> field_simp [nz] <;> ring_nf <;>
      nlinarith only [mul_inv_cancel₀ (show 1-D*2 ≠ 0 by linarith)]
  have ba : ∀ i j, (∑ t : Bool, b i t*a t j)=if i=j then 1 else 0 := by
    intro i j; cases i <;> cases j <;> simp [a,b,backWeight,invWeight,spin,Fintype.sum_bool] <;> field_simp [nz] <;> ring
  have sym (x y : List Bool) : wordWeight a x y=wordWeight a y x := by
    induction x generalizing y with
    | nil => cases y <;> rfl
    | cons i x ih => cases y with
                     | nil => rfl
                     | cons j y => simp only [wordWeight,ih y]; congr 1; simp [a,backWeight,eq_comm]
  have m (y : List Bool) (hy : y.length=k) : mass p (1-2*D) y=
      wordSum k (fun x => pathLaw p x*wordWeight b x y) := by
    unfold mass; rw [hy]; apply expectation_sum
  constructor
  · rintro ⟨q,nonneg,unit,eq⟩ y hy
    rw [m y hy]
    apply le_of_le_of_eq (nonneg y hy)
    rw [← apply_inverse k a b q ab y hy]
    apply wsCong
    intro x hx
    exact congrArg (fun c => c * wordWeight b x y)
      (symmetric_marginal k a q (pathLaw p) sym eq x hx)
  · intro nonneg
    refine ⟨mass p (1-2*D),nonneg,?_,?_⟩
    · have row (x : List Bool) : wordSum x.length (wordWeight b x)=1 := by
        induction x with
        | nil => rfl
        | cons i x ih =>
          simp only [List.length_cons,wordSum,Fintype.sum_bool,wordWeight,wsMul,ih,mul_one]
          cases i <;> simp [b,invWeight,spin] <;> ring
      have norm (a : Bool) (n : ℕ) : expectFrom p a n (fun _ _ => 1)=1 := by
        induction n generalizing a with
        | zero => rfl
        | succ n ih => cases a <;> simp [expectFrom,ih,Three.step] <;> ring
      calc
        _ = wordSum k (fun y => wordSum k (fun x => pathLaw p x*wordWeight b x y)) := wsCong m
        _ = _ := wsSwap k k _
        _ = wordSum k (pathLaw p) := by
          apply wsCong; intro x hx; rw [wsMul,← hx,row,mul_one]
        _ = markovExpect p k (fun _ _ => 1) := by simpa using (expectation_sum p k (fun _ => 1)).symm
        _ = 1 := by simp [markovExpect,norm]
    · intro x hx; rw [← apply_inverse k b a (pathLaw p) ba x hx]
      apply wsCong; intro y hy; rw [m y hy,sym x y]

end BlockHierarchy.Recurrence

#print axioms BlockHierarchy.Recurrence.backward_iff_inverse
