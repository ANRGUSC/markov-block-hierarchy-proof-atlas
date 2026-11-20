import Mathlib.Analysis.Subadditive
import BlockHierarchy.VarianceLimit.Statement
import BlockHierarchy.VarianceLimit.Cut

open scoped BigOperators
namespace BlockHierarchy.VarianceLimit
open Cut

noncomputable def boundaryInformation (p : ℝ) :=
  (1-p)*Real.log (2*(1-p)) + p*Real.log (2*p)

private theorem boundary_kl {p : ℝ} (hp : 0<p) (ph : p<1) (i j : ℕ) :
    mean (adjacent p i j) (fun w => Real.log (2*Cut.step p (last w.1) w.2.1))=boundaryInformation p := by
  have rows (k : ℕ) (x : Bool) : (∑ w,tail p x k w)=1 := by
    induction k generalizing x with
    | zero => change (∑ _ : Unit, (1:ℝ))=1; simp
    | succ k ih =>
      rw [Varentropy.sum_next]
      simp only [tail,← Finset.mul_sum,ih,mul_one]
      cases x <;> simp [Cut.step]
  unfold mean
  rw [Fintype.sum_prod_type]
  have each (x : Word i) : (∑ y : Word j, adjacent p i j (x,y)*Real.log (2*Cut.step p (last x) y.1)) =
      mass p i x*boundaryInformation p := by
    rw [Varentropy.sum_next]
    simp only [adjacent,mul_right_comm (_ * _) _ (Real.log _),← Finset.mul_sum,rows,mul_one]
    cases last x <;> simp [Cut.step,boundaryInformation] <;> ring
  simp_rw [each,← Finset.sum_mul,mass_sum hp ph,one_mul]

private theorem log_test {X : Type*} [Fintype X] (P Q d a b : X → ℝ)
    (hd : ∀ x,0<d x) (hP : ∀ x,0≤P x) (dens : ∀ x,P x=Q x*d x)
    (ha : ∀ x,0<a x) (hb : ∀ x,0<b x) (unit : ∑ x,P x=1)
    (avg : (∑ x,Q x*(a x/b x))≤1) :
    mean P (fun x => Real.log (a x)-Real.log (b x)) ≤ mean P (fun x => Real.log (d x)) := by
  have bound (x : X) : P x*((Real.log (a x)-Real.log (b x))-Real.log (d x))
      ≤ Q x*(a x/b x)-P x := by
    rw [←Real.log_div (ha x).ne' (hb x).ne',←Real.log_div (div_pos (ha x) (hb x)).ne' (hd x).ne']
    have point := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos (div_pos (ha x) (hb x)) (hd x))) (hP x)
    apply point.trans_eq
    rw [mul_sub,mul_one,dens x]
    field_simp [(hd x).ne',(hb x).ne']
  have sums := Finset.sum_le_sum (fun x (_ : x∈Finset.univ) => bound x)
  simp only [mul_sub,Finset.sum_sub_distrib,unit] at sums
  unfold mean
  simp only [mul_sub,Finset.sum_sub_distrib]
  linarith

noncomputable def totalCost (p τ : ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => mean (mass p n) (blockScore p τ n)

theorem totalCost_cut {p τ : ℝ} (hp : 0<p) (ph : p<1/2) (i j : ℕ) :
    totalCost p τ (i+1) + totalCost p τ (j+1) - boundaryInformation p ≤ totalCost p τ ((i+1)+(j+1)) ∧
    totalCost p τ ((i+1)+(j+1)) ≤ totalCost p τ (i+1) + totalCost p τ (j+1) := by
  have ph' : p<1 := by linarith
  let k := (j+1)+i
  let e : Word i × Word j ≃ Word k := concatEquiv (j+1) (i+1)
  let q := fun w => canonicalPrior p τ k (e w)
  let d := jointDistance i j
  let P := adjacent p i j
  let Q := productMass p i j
  let v := trialPrior (canonicalPrior p τ i) (canonicalPrior p τ j)
  have hd : (fun x y => distance k (e x) (e y))=d := by funext x y; exact concat_distance i j x y
  have hP : (fun w => mass p k (e w))=P := by funext w; exact concat_mass p i j w
  have opt : Optimal P τ d q := by rw [←hP,←hd]; exact optimal_pull e (canonical_optimal p τ k)
  have hq : mean P (score τ d q)=totalCost p τ (k+1) := by
    rw [←hP,←hd,show score τ (fun x y => distance k (e x) (e y)) q =
        (fun w => blockScore p τ k (e w)) from funext (score_pull e τ (distance k) (canonicalPrior p τ k))]
    exact mean_pull e _ _
  have L := canonical_optimal p τ i
  have R := canonical_optimal p τ j
  have vprior := trial_isPrior L.1 R.1
  have ind := optimal_independent hp ph' (canonicalPrior p τ i) R
  have ml := ind id (fun _ => 1)
  have mr := ind (fun _ => 1) id
  simp [mean,mass_sum hp ph'] at ml mr
  have hv : mean P (score τ d v)=totalCost p τ (i+1)+totalCost p τ (j+1) := by
    change mean (adjacent p i j) (score τ (jointDistance i j) (trialPrior _ _))=_
    unfold mean
    simp_rw [trial_score _ L.1 R.1,mul_add,Finset.sum_add_distrib]
    exact congrArg₂ (·+·) ml mr
  rw [show i+1+(j+1)=k+1 by dsimp [k]; omega,←hq,←hv]
  refine ⟨?_,opt.2 _ vprior⟩
  let c := fun w : Word i × Word j => 2*Cut.step p (last w.1) w.2.1
  have cp (w) : 0<c w := by unfold c Cut.step; split <;> linarith
  have col := weighted_column_bound Q (Z τ d v) q (fun x y => Real.exp (-τ*(d x y : ℝ)))
    opt.1.1 opt.1.2 (trial_column hp ph L R)
  have kl := log_test P Q c (Z τ d q) (Z τ d v) cp (fun x => (adjacent_pos hp ph' i j x).le)
    (adjacent_density p i j) (Z_pos _ _ opt.1) (Z_pos _ _ vprior) (adjacent_sum hp ph' i j) col
  rw [show mean P (fun x => Real.log (c x))=boundaryInformation p from boundary_kl hp ph' i j] at kl
  unfold mean score at *
  simp only [mul_sub,Finset.sum_sub_distrib,mul_neg,Finset.sum_neg_distrib] at kl ⊢
  linarith

theorem canonicalCost_eq (p τ : ℝ) (n : ℕ) :
    canonicalCost p n τ = totalCost p τ (n+1)/((n:ℝ)+1) := by
  have h := canonical_optimal p τ n
  apply IsLeast.csInf_eq
  refine ⟨⟨canonicalPrior p τ n,h.1,rfl⟩,?_⟩
  rintro z ⟨q,hq,rfl⟩
  exact div_le_div_of_nonneg_right (h.2 q hq) (by positivity)

noncomputable def commonCost (p τ : ℝ) :=
  Filter.limUnder Filter.atTop (fun n : ℕ => canonicalCost p n τ)

open Filter Topology in
theorem cost_redundancy {p : ℝ} (hp : 0<p) (ph : p<1/2) (τ : ℝ) :
    Tendsto (fun n => canonicalCost p n τ) atTop (𝓝 (commonCost p τ)) ∧
    ∀ n, 0 ≤ canonicalCost p n τ-commonCost p τ ∧
      canonicalCost p n τ-commonCost p τ ≤ boundaryInformation p/((n:ℝ)+1) := by
  let S := totalCost p τ
  let J := boundaryInformation p
  let T := fun n => J-S n
  have h0 : S 0=0 := rfl
  have a := totalCost_cut (τ:=τ) hp ph 0 0
  have j0 : 0 ≤ J := by dsimp only [J]; linarith only [a.1,a.2]
  have subS : Subadditive S := by
    rintro (_|i) (_|j) <;> first | simp [h0] | exact (totalCost_cut hp ph i j).2
  have subT : Subadditive T := by
    rintro (_|i) (_|j) <;> dsimp only [T]
    · simp [h0,j0]
    · simp [h0,j0]
    · simp [h0,j0]
    · have := (totalCost_cut (τ:=τ) hp ph i j).1
      dsimp [S,J]
      linarith
  have ubS (n : ℕ) : S n ≤ (n:ℝ)*S 1 := by
    simpa [h0] using subS.apply_mul_add_le n 1 0
  have ubT (n : ℕ) : J-S n ≤ (n:ℝ)*T 1+J := by
    simpa [T,h0] using subT.apply_mul_add_le n 1 0
  have bS : BddBelow (Set.range fun n : ℕ => S n/(n:ℝ)) := by
    refine ⟨min 0 (-(T 1)),?_⟩
    rintro z ⟨n,rfl⟩
    cases n with
    | zero => simp
    | succ n =>
      apply (min_le_right ..).trans
      apply (le_div_iff₀ (Nat.cast_pos.mpr (Nat.succ_pos n))).2
      linarith only [ubT (n+1)]
  have bT : BddBelow (Set.range fun n : ℕ => T n/(n:ℝ)) := by
    refine ⟨min 0 (-(S 1)),?_⟩
    rintro z ⟨n,rfl⟩
    cases n with
    | zero => simp
    | succ n =>
      apply (min_le_right ..).trans
      apply (le_div_iff₀ (Nat.cast_pos.mpr (Nat.succ_pos n))).2
      dsimp only [T]
      linarith only [ubS (n+1), j0]
  have tendS := subS.tendsto_lim bS
  have tendT : Tendsto (fun n : ℕ => T n/n) atTop (𝓝 (-subS.lim)) := by
    simpa only [T,sub_div,zero_sub] using (tendsto_const_div_atTop_nhds_zero_nat J).sub tendS
  have flip := tendsto_nhds_unique (subT.tendsto_lim bT) tendT
  have law : Tendsto (fun n => canonicalCost p n τ) atTop (𝓝 subS.lim) := by
    simp_rw [canonicalCost_eq]
    simpa [S,Nat.cast_succ] using (tendsto_add_atTop_iff_nat 1).mpr tendS
  have value : commonCost p τ=subS.lim := law.limUnder_eq
  rw [value]
  refine ⟨law,?_⟩
  intro n
  have lo := subS.lim_le_div bS (Nat.succ_ne_zero n)
  have hi := subT.lim_le_div bT (Nat.succ_ne_zero n)
  rw [flip] at hi
  simp only [T,sub_div,Nat.cast_succ] at lo hi
  rw [canonicalCost_eq]
  change 0 ≤ S (n+1)/((n:ℝ)+1)-subS.lim ∧ S (n+1)/((n:ℝ)+1)-subS.lim ≤ J/((n:ℝ)+1)
  constructor <;> linarith

#print axioms cost_redundancy

#print axioms totalCost_cut
end BlockHierarchy.VarianceLimit