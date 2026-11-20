import BlockHierarchy.Cut.Paper
import BlockHierarchy.Cut.Existence
import BlockHierarchy.VarianceLimit.Norm
import BlockHierarchy.VarianceLimit.Dyadic

open scoped BigOperators
namespace BlockHierarchy.VarianceLimit
open Cut

private theorem bits_nonempty : ∀ n, Nonempty (Varentropy.Bits n)
  | 0 => ⟨()⟩
  | n+1 => ⟨false,Classical.choice (bits_nonempty n)⟩

private theorem word_opt (p τ : ℝ) (n : ℕ) :
    ∃ q, Optimal (mass p n) τ (distance n) q := by
  let : Nonempty (Word n) := bits_nonempty (n+1)
  exact exists_optimal _ _ _

noncomputable def canonicalPrior (p τ : ℝ) (n : ℕ) := Classical.choose (word_opt p τ n)
theorem canonical_optimal (p τ : ℝ) (n : ℕ) : Optimal (mass p n) τ (distance n) (canonicalPrior p τ n) :=
  Classical.choose_spec (word_opt p τ n)
noncomputable def blockScore (p τ : ℝ) (n : ℕ) := score τ (distance n) (canonicalPrior p τ n)
noncomputable def blockSD (p τ : ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => Real.sqrt (variance (mass p n) (blockScore p τ n))

private theorem mean_pull {X Y : Type*} [Fintype X] [Fintype Y] (e : X ≃ Y) (P f : Y → ℝ) :
    mean (fun x => P (e x)) (fun x => f (e x))=mean P f := e.sum_comp (fun y => P y*f y)

private theorem variance_pull {X Y : Type*} [Fintype X] [Fintype Y] (e : X ≃ Y) (P f : Y → ℝ) :
    variance (fun x => P (e x)) (fun x => f (e x))=variance P f := by
  unfold variance
  rw [mean_pull]
  exact e.sum_comp (fun y => P y*(f y-mean P f)^2)

private theorem prior_pull {X Y : Type*} [Fintype X] [Fintype Y] (e : X ≃ Y) {q : Y → ℝ} (hq : IsPrior q) :
    IsPrior (fun x => q (e x)) := ⟨fun _ => hq.1 _,(e.sum_comp q).trans hq.2⟩

private theorem score_pull {X Y : Type*} [Fintype X] [Fintype Y] (e : X ≃ Y)
    (τ : ℝ) (d : Y → Y → ℕ) (q : Y → ℝ) (x : X) :
    score τ (fun a b => d (e a) (e b)) (fun a => q (e a)) x=score τ d q (e x) := by
  unfold score Z
  rw [e.sum_comp (fun y => q y*Real.exp (-τ*(d (e x) y : ℝ)))]

private theorem optimal_pull {X Y : Type*} [Fintype X] [Fintype Y] (e : X ≃ Y)
    {P q : Y → ℝ} {τ : ℝ} {d : Y → Y → ℕ} (h : Optimal P τ d q) :
    Optimal (fun x => P (e x)) τ (fun a b => d (e a) (e b)) (fun a => q (e a)) := by
  refine ⟨prior_pull e h.1,?_⟩
  intro r hr
  have score_r (x : X) : score τ (fun a b => d (e a) (e b)) r x =
      score τ d (fun y => r (e.symm y)) (e x) := by
    simpa using score_pull e τ d (fun y => r (e.symm y)) x
  rw [show score τ (fun a b => d (e a) (e b)) (fun a => q (e a)) =
        (fun x => score τ d q (e x)) from funext (score_pull e τ d q),
      show score τ (fun a b => d (e a) (e b)) r = _ from funext score_r]
  rw [mean_pull,mean_pull]
  exact h.2 _ (prior_pull e.symm hr)

private theorem independent_variance {i j : ℕ} {p : ℝ} (hp : 0<p) (ph : p<1) (f : Word i → ℝ)
    (g : Word j → ℝ) (ind : IndependentScores p f g) :
    variance (adjacent p i j) (fun w => f w.1+g w.2)=variance (mass p i) f+variance (mass p j) g := by
  let P := adjacent p i j
  let a := mean (mass p i) f
  let b := mean (mass p j) g
  have margL (k : ℝ → ℝ) : mean P (fun w => k (f w.1)) = mean (mass p i) (fun x => k (f x)) := by
    simpa [P,mean,mass_sum hp ph] using ind k (fun _ => 1)
  have margR (k : ℝ → ℝ) : mean P (fun w => k (g w.2)) = mean (mass p j) (fun x => k (g x)) := by
    simpa [P,mean,mass_sum hp ph] using ind (fun _ => 1) k
  have add_mean {X : Type} [Fintype X] (Q l r : X → ℝ) :
      mean Q (fun x => l x+r x)=mean Q l+mean Q r := by simp [mean,mul_add,Finset.sum_add_distrib]
  have avg : mean P (fun w => f w.1+g w.2)=a+b := (add_mean P (fun w => f w.1) (fun w => g w.2)).trans (congrArg₂ (·+·) (margL id) (margR id))
  have cent : mean (mass p i) (fun x => f x-a)=0 := by
    simp [mean,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,mass_sum hp ph,a]
  have cross := ind (fun x => x-a) (fun y => y-b)
  rw [cent,zero_mul] at cross
  change mean P (fun w => (f w.1+g w.2-mean P (fun w => f w.1+g w.2))^2)=_
  rw [avg]
  have decomp (w : Word i × Word j) :
      (f w.1+g w.2-(a+b))^2 = ((f w.1-a)^2+(g w.2-b)^2) + 2*((f w.1-a)*(g w.2-b)) := by ring
  simp_rw [decomp]
  rw [add_mean,add_mean,margL (fun z => (z-a)^2),margR (fun z => (z-b)^2)]
  have scale : mean P (fun w => 2*((f w.1-a)*(g w.2-b))) =
      2*mean P (fun w => (f w.1-a)*(g w.2-b)) := by
    unfold mean
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    ring
  rw [scale,show mean P (fun w => (f w.1-a)*(g w.2-b))=0 from cross,mul_zero,add_zero]
  rfl

theorem block_cut {p τ : ℝ} (hp : 0<p) (ph : p<1/2) (ht : 0≤τ) :
    CutBound (blockSD p τ) (Real.sqrt (1-2*p)) := by
  rintro (_|i) (_|j) hi hj <;> try omega
  let k := (j+1)+i
  let e : Word i × Word j ≃ Word k := concatEquiv (j+1) (i+1)
  let qJ := fun w => canonicalPrior p τ k (e w)
  have hd : (fun x y => distance k (e x) (e y))=jointDistance i j := by
    funext x y; exact concat_distance i j x y
  have hm : (fun w => mass p k (e w))=adjacent p i j := by funext w; exact concat_mass p i j w
  have hJ : Optimal (adjacent p i j) τ (jointDistance i j) qJ := by
    rw [←hm,←hd]
    exact optimal_pull e (canonical_optimal p τ k)
  have hscore (w) : score τ (jointDistance i j) qJ w=blockScore p τ k (e w) := by
    rw [←hd]
    exact score_pull e _ _ _ w
  obtain ⟨ind,bnd⟩ := one_cut p τ hp ph ht i j _ _ qJ (canonical_optimal p τ i) (canonical_optimal p τ j) hJ
  let f := blockScore p τ i
  let g := blockScore p τ j
  have ph' : p<1 := by linarith
  have hsum := independent_variance hp ph' f g ind
  have h := sd_diff (adjacent p i j) (score τ (jointDistance i j) qJ) (fun w : Word i × Word j => f w.1+g w.2)
    ⟨fun w => (adjacent_pos hp ph' i j w).le,adjacent_sum hp ph' i j⟩
  have hh := h.trans (Real.sqrt_le_sqrt (show mean (adjacent p i j)
    (fun w => (score τ (jointDistance i j) qJ w-(f w.1+g w.2))^2) ≤ 1-2*p by simpa [sub_add_eq_sub_sub,f,g,blockScore] using bnd))
  have hjVar : variance (adjacent p i j) (score τ (jointDistance i j) qJ) = variance (mass p k) (blockScore p τ k) := by
    rw [←hm,show score τ (jointDistance i j) qJ=(fun w => blockScore p τ k (e w)) from funext hscore]
    exact variance_pull e _ _
  rw [hjVar,hsum] at hh
  have varpos (n : ℕ) : 0 ≤ variance (mass p n) (blockScore p τ n) :=
    Finset.sum_nonneg (fun w _ => mul_nonneg (mass_pos hp ph' n w).le (sq_nonneg _))
  rw [show i+1+(j+1)=k+1 by dsimp [k]; omega]
  simpa only [blockSD,Real.sq_sqrt (varpos i),Real.sq_sqrt (varpos j),f,g] using hh

#print axioms block_cut
end BlockHierarchy.VarianceLimit