import BlockHierarchy.Cut.Optimality
import BlockHierarchy.Varentropy.Score

open scoped BigOperators
namespace BlockHierarchy.Cut
open Varentropy

noncomputable def symmetricModel (p : ℝ) (hp : 0 < p) (hp' : p < 1) : BinaryModel where
  p := 1/2
  q := 1/2
  a := p
  b := p
  ppos := by norm_num
  qpos := by norm_num
  normalized := by norm_num
  apos := hp
  bpos := hp
  alt := hp'
  blt := hp'
  balanced := rfl

theorem mass_eq_pathLaw {p : ℝ} (hp : 0 < p) (hp' : p < 1) (n : ℕ) (w : Word n) :
    mass p n w = pathLaw (symmetricModel p hp hp') n w := by
  let m := symmetricModel p hp hp'
  have transition_eq (a b : Bool) : Cut.step p a b = transition m a b := by
    cases a <;> cases b <;> rfl
  have tail_eq (k : ℕ) (a : Bool) (ys : Bits k) : tail p a k ys = tailLaw m a k ys := by
    induction k generalizing a with
    | zero => rfl
    | succ k ih => rw [tail, tailLaw, transition_eq, ih]
  change (1/2:ℝ)*tail p w.1 n w.2 = pi m w.1 * tailLaw m w.1 n w.2
  rw [tail_eq]
  cases w.1 <;> rfl

theorem mass_pos {p : ℝ} (hp : 0 < p) (hp' : p < 1) (n : ℕ) (w : Word n) :
    0 < mass p n w := by rw [mass_eq_pathLaw hp hp']; exact path_positive .. 

theorem mass_sum {p : ℝ} (hp : 0 < p) (hp' : p < 1) (n : ℕ) : ∑ w, mass p n w = 1 := by
  simp_rw [mass_eq_pathLaw hp hp']
  exact path_mass .. 

theorem complement_twice (n : ℕ) (w : Bits n) : complement n (complement n w) = w := by
  induction n with
  | zero => cases w; rfl
  | succ n ih =>
    obtain ⟨b,ys⟩ := w
    change ((!(!b)),complement n (complement n ys)) = (b,ys)
    rw [ih, Bool.not_not]

def complementEquiv (n : ℕ) : Bits n ≃ Bits n :=
  ⟨complement n, complement n, complement_twice n, complement_twice n⟩

theorem complement_distance (n : ℕ) (x y : Word n) :
    distance n (complement (n+1) x) (complement (n+1) y) = distance n x y := by
  have aux (k : ℕ) (s t : Bits k) : hamming k (complement k s) (complement k t) = hamming k s t := by
    induction k with
    | zero => rfl
    | succ k ih =>
      obtain ⟨a,s⟩ := s
      obtain ⟨b,t⟩ := t
      cases a <;> cases b <;> simp [complement,hamming,ih s t]
  exact aux _ _ _

theorem complement_mass (p : ℝ) (n : ℕ) (w : Word n) :
    mass p n (complement (n+1) w) = mass p n w := by
  have aux (k : ℕ) (x : Bool) (ys : Bits k) :
      tail p (!x) k (complement k ys) = tail p x k ys := by
    induction k generalizing x with
    | zero => rfl
    | succ k ih =>
      obtain ⟨b,t⟩ := ys
      change Cut.step p (!x) (!b) * tail p (!b) k (complement k t) = Cut.step p x b * tail p b k t
      rw [ih]
      cases x <;> cases b <;> rfl
  exact congrArg (fun a : ℝ => (1/2:ℝ)*a) (aux n w.1 w.2)

theorem adjacent_density (p : ℝ) (i j : ℕ) (w : Word i × Word j) :
    adjacent p i j w = productMass p i j w * (2 * Cut.step p (last w.1) w.2.1) := by
  unfold adjacent productMass mass
  ring

theorem adjacent_le_product {p : ℝ} (hp : 0 < p) (ph : p < 1/2) (i j : ℕ) (w : Word i × Word j) :
    adjacent p i j w ≤ (2*(1-p)) * productMass p i j w := by
  have h1 : p < 1 := by linarith
  have nonneg : 0 ≤ productMass p i j w := (mul_pos (mass_pos hp h1 i _) (mass_pos hp h1 j _)).le
  rw [adjacent_density, mul_comm (2*(1-p))]
  apply mul_le_mul_of_nonneg_left _ nonneg
  unfold Cut.step
  split <;> linarith

/-- Averaging the right word with its global complement cancels the dependence
of every complement-invariant observation on the incoming boundary state. -/
theorem boundary_average (p : ℝ) (j : ℕ) (b : Bool) (g : Word j → ℝ)
    (hs : ∀ y, g (complement (j+1) y) = g y) :
    (∑ y : Word j, mass p j y * (2 * Cut.step p b y.1) * g y) = mean (mass p j) g := by
  let h (y : Word j) := mass p j y * (2 * Cut.step p b y.1) * g y
  have total : (∑ y, h (complement (j+1) y)) = ∑ y, h y :=
    (complementEquiv (j+1)).sum_comp h
  have point (y : Word j) : h y + h (complement (j+1) y) = 2*(mass p j y*g y) := by
    dsimp only [h]
    rw [complement_mass,hs]
    change _ + mass p j y * (2*Cut.step p b (!y.1))*g y = _
    cases b <;> cases y.1 <;> simp [Cut.step] <;> ring
  have summed := Finset.sum_congr (s₁ := Finset.univ) rfl (fun y _ => point y)
  rw [Finset.sum_add_distrib,total,← Finset.mul_sum] at summed
  change (∑ y, h y) = ∑ y, mass p j y * g y
  linarith only [summed]

theorem independent_of_complement {i j : ℕ} (p : ℝ) (f : Word i → ℝ) (g : Word j → ℝ)
    (hg : ∀ y, g (complement (j+1) y) = g y) : IndependentScores p f g := by
  intro a b
  unfold mean
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  calc
    _ = ∑ y : Word j, (mass p i x*a (f x)) *
          (mass p j y*(2*Cut.step p (last x) y.1)*b (g y)) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [adjacent_density]
      unfold productMass
      ring
    _ = _ := by
      rw [← Finset.mul_sum, boundary_average p j (last x) (fun y => b (g y))
        (fun y => congrArg b (hg y))]
      rfl

/-- Concatenation is a bijection from two word alphabets onto one longer alphabet.
The reversed order of the summands makes recursion on the left word definitional. -/
def concatEquiv (r : ℕ) : (l : ℕ) → Bits l × Bits r ≃ Bits (r+l)
  | 0 => {
      toFun := fun w => w.2
      invFun := fun w => ((), w)
      left_inv := by rintro ⟨⟨⟩,w⟩; rfl
      right_inv := fun _ => rfl }
  | l+1 => (Equiv.prodAssoc Bool (Bits l) (Bits r)).trans
      ((Equiv.refl Bool).prodCongr (concatEquiv r l))

theorem concat_distance (i j : ℕ) (x y : Word i × Word j) :
    distance ((j+1)+i) (concatEquiv (j+1) (i+1) x) (concatEquiv (j+1) (i+1) y) =
      jointDistance i j x y := by
  have aux (r l : ℕ) (s t : Bits l) (a b : Bits r) :
      hamming (r+l) (concatEquiv r l (s,a)) (concatEquiv r l (t,b)) =
        hamming l s t + hamming r a b := by
    induction l with
    | zero => exact (Nat.zero_add _).symm
    | succ l ih =>
      change (if s.1=t.1 then 0 else 1) +
        hamming (r+l) (concatEquiv r l (s.2,a)) (concatEquiv r l (t.2,b)) =
          ((if s.1=t.1 then 0 else 1)+hamming l s.2 t.2)+hamming r a b
      rw [ih, Nat.add_assoc]
  exact aux (j+1) (i+1) x.1 y.1 x.2 y.2

theorem concat_mass (p : ℝ) (i j : ℕ) (w : Word i × Word j) :
    mass p ((j+1)+i) (concatEquiv (j+1) (i+1) w) = adjacent p i j w := by
  have aux (r l : ℕ) (b : Bool) (s : Bits l) (t : Bits r) :
      tail p b (r+l) (concatEquiv r l (s,t)) = tail p b l s * tail p (lastBit b l s) r t := by
    induction l generalizing b with
    | zero => exact (one_mul _).symm
    | succ l ih =>
      change Cut.step p b s.1 * tail p s.1 (r+l) (concatEquiv r l (s.2,t)) =
        (Cut.step p b s.1 * tail p s.1 l s.2) * tail p (lastBit s.1 l s.2) r t
      rw [ih, mul_assoc]
  change (1/2 : ℝ)*tail p w.1.1 ((j+1)+i) (concatEquiv (j+1) i (w.1.2,w.2)) = _
  rw [aux]
  change _ * (_ * (Cut.step p (last w.1) w.2.1 * tail p w.2.1 j w.2.2)) =
    (_ * tail p w.1.1 i w.1.2) * Cut.step p (last w.1) w.2.1 * tail p w.2.1 j w.2.2
  ring

theorem adjacent_pos {p : ℝ} (hp : 0 < p) (ph : p < 1) (i j : ℕ) (w : Word i × Word j) :
    0 < adjacent p i j w := by rw [← concat_mass]; exact mass_pos hp ph _ _

theorem adjacent_sum {p : ℝ} (hp : 0 < p) (ph : p < 1) (i j : ℕ) : ∑ w, adjacent p i j w = 1 := by
  simp_rw [← concat_mass]
  rw [(concatEquiv (j+1) (i+1)).sum_comp]
  exact mass_sum hp ph _

theorem optimal_independent {p τ : ℝ} (hp : 0 < p) (ph : p < 1) {i j : ℕ}
    (qL : Word i → ℝ) {qR : Word j → ℝ} (opt : Optimal (mass p j) τ (distance j) qR) :
    IndependentScores p (score τ (distance i) qL) (score τ (distance j) qR) := by
  apply independent_of_complement
  exact optimal_score_invariant (mass_pos hp ph j) opt (complementEquiv (j+1))
    (complement_mass p j) (complement_distance j)

#print axioms optimal_independent
#print axioms concat_mass
#print axioms concat_distance
#print axioms independent_of_complement
#print axioms adjacent_le_product
end BlockHierarchy.Cut
