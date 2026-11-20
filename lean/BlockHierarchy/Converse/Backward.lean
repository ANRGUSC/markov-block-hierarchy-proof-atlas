import BlockHierarchy.Cut.Flips
import BlockHierarchy.RecurrencePaper
import BlockHierarchy.Converse.Bernoulli

open scoped BigOperators Topology
open Filter
namespace BlockHierarchy.Converse
open Varentropy Cut

def wordList : (n : ℕ) → Bits n → List Bool
  | 0, _ => []
  | n+1, w => w.1::wordList n w.2

@[simp] theorem length_wordList (n : ℕ) (w : Bits n) : (wordList n w).length=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [wordList,ih]

theorem wordList_inj (n : ℕ) : Function.Injective (wordList n) := by
  induction n with
  | zero => intro x y _; cases x; cases y; rfl
  | succ n ih =>
    rintro ⟨x,u⟩ ⟨y,v⟩ h
    obtain ⟨rfl,e⟩ := List.cons.inj h
    change wordList n u=wordList n v at e
    have htail : u=v := ih e
    subst v
    rfl

private theorem list_bsc (D : ℝ) (n : ℕ) (x y : Bits n) :
    Recurrence.wordWeight (Recurrence.backWeight D) (wordList n x) (wordList n y) =
      bsc D n x y := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [wordList,Recurrence.wordWeight,Recurrence.backWeight,bsc,ih]

private theorem word_sum (n : ℕ) (f : List Bool → ℝ) :
    Recurrence.wordSum n f=∑ x : Bits n, f (wordList n x) := by
  induction n generalizing f with
  | zero => simp [Recurrence.wordSum,wordList,show Fintype.card (Bits 0)=1 from rfl]
  | succ n ih => simp only [Recurrence.wordSum,sum_next,wordList,ih]

private theorem expect_word (p : ℝ) (n : ℕ) (a : Bool) (f : List Bool → ℝ) :
    Recurrence.expectFrom p a (n+1) (fun xs _ => f xs) =
      ∑ z : Bits n, tail p a n z*f (a::wordList n z) := by
  induction n generalizing a f with
  | zero =>
    cases a <;> simp [Recurrence.expectFrom,Three.step,Fintype.sum_bool,tail,wordList,
      show Fintype.card (Bits 0)=1 from rfl] <;> ring
  | succ n ih =>
    rw [Recurrence.expectFrom,sum_next]
    apply Finset.sum_congr rfl
    intro b _
    rw [ih,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    change Three.step p a b*(_*_)= (Cut.step p a b*_)*_
    rw [mul_assoc]
    rfl

theorem word_mass (p : ℝ) (n : ℕ) (x : Word n) :
    Recurrence.pathLaw p (wordList (n+1) x)=mass p n x := by
  classical
  unfold Recurrence.pathLaw Recurrence.markovExpect
  rw [length_wordList]
  simp_rw [expect_word p n _ (fun xs => if xs=wordList (n+1) x then 1 else 0)]
  change (∑ a : Bool, ∑ w : Bits n, tail p a n w *
    (if a::wordList n w=wordList (n+1) x then 1 else 0))/2 = _
  have test (a : Bool) (w : Bits n) :
      a::wordList n w=wordList (n+1) x ↔ (a,w)=x := by
    change wordList (n+1) (a,w)=wordList (n+1) x ↔ _
    exact (wordList_inj (n+1)).eq_iff
  have replace : (∑ a : Bool, ∑ w : Bits n, tail p a n w *
      (if a::wordList n w=wordList (n+1) x then 1 else 0)) =
      ∑ a : Bool, ∑ z : Bits n, tail p a n z * (if (a,z)=x then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro w _
    by_cases e : (a,w)=x
    · simp only [if_pos e,if_pos ((test a w).2 e)]
    · simp only [if_neg e,if_neg (fun h => e ((test a w).1 h))]
  rw [replace]
  have pack : (∑ a : Bool, ∑ z : Bits n, tail p a n z * (if (a,z)=x then 1 else 0)) =
      ∑ w : Word n, tail p w.1 n w.2*(if w=x then 1 else 0) :=
    (sum_next n (fun w : Word n => tail p w.1 n w.2*(if w=x then 1 else 0))).symm
  rw [pack]
  simp [mul_ite,mass]
  ring

/-- At every block length and at equality in Gray's critical distortion,
there is an actual normalized backward Bernoulli reproduction prior. -/
theorem exists_backward {p D : ℝ} (hp : 0<p) (ph : p<1/2) (hd : 0<D)
    (hD : D≤Recurrence.grayD p) (n : ℕ) :
    ∃ q : Word n → ℝ, IsPrior q ∧ ∀ x, (∑ y, q y*bsc D (n+1) x y)=mass p n x := by
  obtain ⟨_,_,d,_,anti,feas,conv⟩ := Recurrence.finite_block_recurrence p hp ph
  have bound : Recurrence.grayD p ≤ d n :=
    le_of_tendsto conv (eventually_atTop.2 ⟨n,fun m hm => anti hm⟩)
  obtain ⟨q,pos,total,law⟩ := (feas n D hd (hD.trans_lt (Recurrence.gray_interior hp ph).2)).2
    (hD.trans bound)
  refine ⟨fun w => q (wordList (n+1) w),⟨fun w => pos _ (length_wordList _ _),?_⟩,?_⟩
  · simpa only [word_sum] using total
  · intro x
    have e := law _ (length_wordList _ x)
    simpa only [word_sum,list_bsc,word_mass] using e

#print axioms exists_backward
end BlockHierarchy.Converse
