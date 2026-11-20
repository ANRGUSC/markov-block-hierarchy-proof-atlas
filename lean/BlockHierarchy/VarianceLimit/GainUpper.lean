import BlockHierarchy.Converse.Paths
import BlockHierarchy.VarianceLimit.Redundancy

open scoped BigOperators
namespace BlockHierarchy.VarianceLimit
open Cut Varentropy Converse

private def flipValue (a b : Bool) : ℝ := if a=b then 0 else 1

/-- Indicator of internal transition i, numbered from zero in physical path order. -/
def edgeIndicator : (n : ℕ) → Word n → ℕ → ℝ
  | 0, _, _ => 0
  | _+1, w, 0 => flipValue w.1 w.2.1
  | n+1, w, i+1 => edgeIndicator n w.2 i

private theorem cut_indicator (i j : ℕ) (w : Word i × Word j) :
    edgeIndicator ((j+1)+i) (concatEquiv (j+1) (i+1) w) i = flipValue (last w.1) w.2.1 := by
  induction i with
  | zero => rfl
  | succ i ih => exact ih (w.1.2,w.2)

private theorem product_preferred {p τ : ℝ} (hp : 0<p) (ph : p<1/2) (i j : ℕ)
    {r : Word i × Word j → ℝ} (hr : IsPrior r) :
    totalCost p τ (i+1)+totalCost p τ (j+1) ≤
      mean (productMass p i j) (score τ (jointDistance i j) r) := by
  have h1 : p<1 := by linarith
  let Q := productMass p i j
  let d := jointDistance i j
  let v := trialPrior (canonicalPrior p τ i) (canonicalPrior p τ j)
  have L := canonical_optimal p τ i
  have R := canonical_optimal p τ j
  have hv : IsPrior v := trial_isPrior L.1 R.1
  have unit : ∑ x,Q x=1 := (trial_isPrior (show IsPrior (mass p i) from
    ⟨fun x => (mass_pos hp h1 i x).le,mass_sum hp h1 i⟩) (show IsPrior (mass p j) from
    ⟨fun x => (mass_pos hp h1 j x).le,mass_sum hp h1 j⟩)).2
  have point (x : Word i × Word j) :
      Q x*(score τ d v x-score τ d r x) ≤ Q x*(Z τ d r x/Z τ d v x)-Q x := by
    have hQ : 0 ≤ Q x := (mul_pos (mass_pos hp h1 i _) (mass_pos hp h1 j _)).le
    have h := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos (Z_pos τ d hr x) (Z_pos τ d hv x))) hQ
    rw [Real.log_div (Z_pos _ _ hr _).ne' (Z_pos _ _ hv _).ne'] at h
    simpa only [score,neg_sub_neg,mul_sub,mul_one] using h
  have bound := weighted_column_bound Q (Z τ d v) r _ hr.1 hr.2 (trial_column hp ph L R)
  have total := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => point x)
  simp only [mul_sub,Finset.sum_sub_distrib,unit] at total
  change (∑ x,Q x*(Z τ d r x/Z τ d v x))≤1 at bound
  have better : mean Q (score τ d v) ≤ mean Q (score τ d r) := by unfold mean; linarith only [bound,total]
  have blocks : mean Q (score τ d v) = totalCost p τ (i+1)+totalCost p τ (j+1) := by
    change mean (productMass p i j) (score τ (jointDistance i j) (trialPrior _ _))=_
    unfold mean
    simp_rw [trial_score τ L.1 R.1]
    rw [Fintype.sum_prod_type]
    have row (x : Word i) : (∑ y : Word j, productMass p i j (x,y) *
        (blockScore p τ i x+blockScore p τ j y)) =
        mass p i x*blockScore p τ i x + mass p i x*totalCost p τ (j+1) := by
      unfold productMass
      simp only [mul_add,Finset.sum_add_distrib,mul_right_comm (mass p i x) _ (blockScore p τ i x),
        mul_assoc (mass p i x) _ (blockScore p τ j _),←Finset.mul_sum,mass_sum hp h1,mul_one]
      rfl
    change (∑ x, ∑ y : Word j, productMass p i j (x,y)*(blockScore p τ i x+blockScore p τ j y))=_
    simp_rw [row,Finset.sum_add_distrib,←Finset.sum_mul,mass_sum hp h1,one_mul]
    rfl
  exact blocks ▸ better

private theorem expectation_change {X : Type*} [Fintype X] (P Q a f : X → ℝ) (c p : ℝ)
    (hP : ∑ x,P x=1) (hQ : ∑ x,Q x=1) (tilt : ∀ x,Q x-P x=c*P x*(a x-p)) :
    mean Q f - mean P f = c*mean P (fun x => (f x-mean P f)*(a x-p)) := by
  calc
    _ = ∑ x,(Q x-P x)*(f x-mean P f) := by
      simp only [sub_mul,mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,hP,hQ,one_mul]
      unfold mean
      ring
    _ = _ := by
      unfold mean
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [tilt]
      ring

/-- Evaluate the full-word optimal score after replacing the one boundary flip
by a fair bit. The resulting source is the product of the stationary marginals. -/
theorem single_cut_gain {p τ : ℝ} (hp : 0<p) (ph : p<1/2) (i j : ℕ) :
    let n := (j+1)+i
    totalCost p τ (i+1)+totalCost p τ (j+1)-totalCost p τ (n+1) ≤
      ((1/2-p)/(p*(1-p)))*mean (mass p n) (fun x =>
        (blockScore p τ n x-totalCost p τ (n+1))*(edgeIndicator n x i-p)) := by
  let n := (j+1)+i
  let e : Word i × Word j ≃ Word n := concatEquiv (j+1) (i+1)
  let P := adjacent p i j
  let Q := productMass p i j
  let f (w : Word i × Word j) := blockScore p τ n (e w)
  let c := (1/2-p)/(p*(1-p))
  let mark (w : Word i × Word j) := flipValue (last w.1) w.2.1
  have h1 : p<1 := by linarith
  have hd : (fun x y => distance n (e x) (e y)) = jointDistance i j := funext fun x => funext (concat_distance i j x)
  have hP : (fun w => mass p n (e w)) = P := funext (concat_mass p i j)
  have avg : mean P f = totalCost p τ (n+1) := by rw [←hP]; exact mean_pull e _ _
  have unitQ : ∑ x,Q x=1 := (trial_isPrior (show IsPrior (mass p i) from
    ⟨fun x => (mass_pos hp h1 i x).le,mass_sum hp h1 i⟩) (show IsPrior (mass p j) from
    ⟨fun x => (mass_pos hp h1 j x).le,mass_sum hp h1 j⟩)).2
  let q := fun w => canonicalPrior p τ n (e w)
  have qr : IsPrior q := ⟨fun w => (canonical_optimal p τ n).1.1 _,(e.sum_comp _).trans (canonical_optimal p τ n).1.2⟩
  have opt := product_preferred (τ := τ) hp ph i j qr
  have score_eq : score τ (jointDistance i j) q = f := by
    rw [←hd]
    exact funext (score_pull e τ (distance n) (canonicalPrior p τ n))
  rw [score_eq] at opt
  have tilt (w : Word i × Word j) : Q w-P w = c*P w*(mark w-p) := by
    change Q w-adjacent p i j w = c*adjacent p i j w*(mark w-p)
    rw [adjacent_density]
    unfold c mark flipValue Cut.step
    change Q w-Q w*(2*(if _ then _ else _)) = _* (Q w*(2*(if _ then _ else _))) * _
    by_cases h : last w.1=w.2.1 <;> simp only [h,if_true,if_false]
    all_goals field_simp [hp.ne',(sub_pos.mpr h1).ne']
    all_goals ring
  have changeLaw := expectation_change P Q mark f c p (adjacent_sum hp h1 i j) unitQ tilt
  have lift : mean P (fun w => (f w-mean P f)*(mark w-p)) =
      mean (mass p n) (fun x => (blockScore p τ n x-totalCost p τ (n+1))*(edgeIndicator n x i-p)) := by
    rw [avg,←hP]
    have id (w : Word i × Word j) : mark w = edgeIndicator n (e w) i := (cut_indicator i j w).symm
    simp_rw [id]
    exact mean_pull e (mass p n) (fun x => (blockScore p τ n x-totalCost p τ (n+1))*(edgeIndicator n x i-p))
  change _ ≤ c*_
  rw [←lift,←changeLaw,avg]
  exact sub_le_sub_right opt _

#print axioms single_cut_gain

private theorem path_edge_count (n : ℕ) (a : Bool) (w : Bits n) :
    (∑ i ∈ Finset.range n, edgeIndicator n (a,fromFlips a n w) i) = (flipCount n w : ℝ) := by
  induction n generalizing a with
  | zero => simp [flipCount]
  | succ n ih =>
    obtain ⟨b,w⟩ := w
    rw [Finset.sum_range_succ']
    change (∑ i ∈ Finset.range n, edgeIndicator n
      (flipAfter a b,fromFlips (flipAfter a b) n w) i) + flipValue a (flipAfter a b) = _
    rw [ih]
    cases a <;> cases b <;> simp [flipValue,flipAfter,flipCount] <;> ring

/-- The shifted second moment gives both the binomial variance and the zero
centered first moment, while the induction accounts for one new Bernoulli bit. -/
theorem iid_count_square (p : ℝ) (n : ℕ) (t : ℝ) :
    (∑ w : Bits n, iidFlips p n w*((flipCount n w:ℝ)-n*p+t)^2) =
      n*p*(1-p)+t^2 := by
  induction n generalizing t with
  | zero =>
    letI : Unique (Bits 0) := inferInstanceAs (Unique Unit)
    simp only [iidFlips,flipCount,Nat.cast_zero,zero_mul,sub_zero,zero_add,one_mul]
    exact Fintype.sum_unique _
  | succ n ih =>
    rw [Varentropy.sum_next]
    have branch (b : Bool) :
        (∑ w : Bits n, iidFlips p (n+1) (b,w)*((flipCount (n+1) (b,w):ℝ)-(n+1:ℕ)*p+t)^2) =
          (if b then p else 1-p)*(n*p*(1-p)+(t+(if b then 1 else 0)-p)^2) := by
      calc
        _ = (if b then p else 1-p)*∑ w : Bits n, iidFlips p n w*
             ((flipCount n w:ℝ)-n*p+(t+(if b then 1 else 0)-p))^2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro w _
          cases b <;> simp only [iidFlips,flipCount,Bool.false_eq_true,ite_false,ite_true,
            Nat.cast_add,Nat.cast_succ,Nat.cast_zero] <;> ring
        _ = _ := by rw [ih]
    simp_rw [branch]
    simp only [Fintype.sum_bool,Bool.false_eq_true,ite_false,ite_true,Nat.cast_succ]
    ring

theorem path_count_variance (p : ℝ) (n : ℕ) :
    mean (mass p n) (fun x => ((∑ i ∈ Finset.range n, edgeIndicator n x i)-n*p)^2) = n*p*(1-p) := by
  unfold mean
  rw [Varentropy.sum_next]
  have row (a : Bool) : (∑ y : Bits n, mass p n (a,y)*
      ((∑ i ∈ Finset.range n, edgeIndicator n (a,y) i)-n*p)^2) = (1/2:ℝ)*(n*p*(1-p)) := by
    rw [← (flipEquiv a n).sum_comp (fun y : Bits n => mass p n (a,y)*
      ((∑ i ∈ Finset.range n, edgeIndicator n (a,y) i)-n*p)^2)]
    simp_rw [path_from_flips]
    change (∑ y : Bits n, (1/2:ℝ)*iidFlips p n y*
      ((∑ i ∈ Finset.range n, edgeIndicator n (a,fromFlips a n y) i)-n*p)^2)=_
    simp_rw [path_edge_count,mul_assoc,←Finset.mul_sum]
    exact congrArg (fun v : ℝ => 1/2*v) (by simpa [mul_assoc] using iid_count_square p n 0)
  simp_rw [row]
  simp

private theorem weighted_cs {X : Type*} [Fintype X] (P f g : X → ℝ) (hP : ∀ x,0≤P x) :
    mean P (fun x => f x*g x) ≤ √(mean P (fun x => f x^2))*√(mean P (fun x => g x^2)) := by
  have square (v : X → ℝ) : (∑ x,(√(P x)*v x)^2) = mean P (fun x => v x^2) := by
    unfold mean
    apply Finset.sum_congr rfl
    intro x _
    rw [mul_pow,Real.sq_sqrt (hP x)]
  have pair : (∑ x,(√(P x)*f x)*(√(P x)*g x)) = mean P (fun x => f x*g x) := by
    unfold mean
    apply Finset.sum_congr rfl
    intro x _
    calc
      _ = (√(P x))^2*(f x*g x) := by ring
      _ = _ := by rw [Real.sq_sqrt (hP x)]
  have pos (v : X → ℝ) : 0≤mean P (fun x => v x^2) :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (hP x) (sq_nonneg _))
  apply le_of_sq_le_sq _ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  rw [mul_pow,Real.sq_sqrt (pos f),Real.sq_sqrt (pos g),←square f,←square g,←pair]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _

#print axioms path_count_variance

/-- The true-law covariance estimate (gainhi) in the appendix. At length k+2
there are exactly k+1 independent Bernoulli flips, one per possible cut. -/
theorem gain_upper {p τ : ℝ} (hp : 0<p) (ph : p<1/2) (k : ℕ) :
    (∑ i ∈ Finset.range (k+1), (totalCost p τ (i+1)+totalCost p τ (k-i+1)-
      totalCost p τ (k+2))) ≤ ((1/2-p)/√(p*(1-p)))*√(((k:ℝ)+2)*((k:ℝ)+1))*
        (blockSD p τ (k+2)/√((k:ℝ)+2)) := by
  let n := k+1
  let P := mass p n
  let f (x : Word n) := blockScore p τ n x-totalCost p τ (n+1)
  let g (x : Word n) := (∑ i ∈ Finset.range n, edgeIndicator n x i)-(n:ℝ)*p
  let c := (1/2-p)/(p*(1-p))
  have h1 : p<1 := by linarith
  have hc : 0≤c := (div_pos (sub_pos.mpr ph) (mul_pos hp (sub_pos.mpr h1))).le
  have each (i : ℕ) (hi : i ∈ Finset.range n) :
      totalCost p τ (i+1)+totalCost p τ (k-i+1)-totalCost p τ (k+2) ≤
        c*mean P (fun x => f x*(edgeIndicator n x i-p)) := by
    have eq : (k-i+1)+i = n := by
      have h := Finset.mem_range.mp hi
      dsimp [n] at h ⊢
      omega
    have r := single_cut_gain (τ := τ) hp ph i (k-i)
    dsimp only at r
    rw [eq] at r
    exact r
  have sum_cross :
      (∑ i ∈ Finset.range n, mean P (fun x => f x*(edgeIndicator n x i-p))) =
        mean P (fun x => f x*g x) := by
    unfold mean
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    simp only [←mul_assoc,←Finset.mul_sum,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,g]
  have cs := weighted_cs P f g (fun x => (mass_pos hp h1 n x).le)
  have vg : mean P (fun x => g x^2) = (n:ℝ)*p*(1-p) := path_count_variance p n
  have vf : √(mean P (fun x => f x^2)) = blockSD p τ (k+2) := rfl
  rw [vg,vf] at cs
  have varPos : 0 < p*(1-p) := mul_pos hp (sub_pos.mpr h1)
  have rootPos := Real.sqrt_pos.mpr varPos
  have upper :
      (∑ i ∈ Finset.range n, (totalCost p τ (i+1)+totalCost p τ (k-i+1)-totalCost p τ (k+2))) ≤
        c*(blockSD p τ (k+2)*√((n:ℝ)*p*(1-p))) := by
    calc
      _ ≤ ∑ i ∈ Finset.range n, c*mean P (fun x => f x*(edgeIndicator n x i-p)) := Finset.sum_le_sum each
      _ = c*mean P (fun x => f x*g x) := by rw [←Finset.mul_sum,sum_cross]
      _ ≤ _ := mul_le_mul_of_nonneg_left cs hc
  apply upper.trans_eq
  rw [mul_assoc (n:ℝ) p, Real.sqrt_mul (by positivity : 0 ≤ (n:ℝ)),Real.sqrt_mul (by positivity : 0 ≤ (k:ℝ)+2)]
  have coeff : c*√(p*(1-p)) = (1/2-p)/√(p*(1-p)) := by
    unfold c
    apply (eq_div_iff rootPos.ne').mpr
    rw [mul_assoc,←sq,Real.sq_sqrt varPos.le,div_mul_cancel₀ _ varPos.ne']
  rw [←coeff]
  dsimp only [n]
  push_cast
  field_simp

#print axioms gain_upper
end BlockHierarchy.VarianceLimit
