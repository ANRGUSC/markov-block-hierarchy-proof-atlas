import BlockHierarchy.VarianceLimit.GainLower
import BlockHierarchy.VarianceLimit.Reversal

open scoped BigOperators
namespace BlockHierarchy.VarianceLimit
open Cut

variable {X : Type*} [Fintype X]

private theorem push_Z (τ : ℝ) (d : X → X → ℕ) (q : X → ℝ) (e : X ≃ X)
    (inv : ∀ x y, d (e x) (e y)=d x y) (x : X) :
    Z τ d (fun y => q (e y)) x=Z τ d q (e x) := by
  unfold Z
  rw [←e.sum_comp (fun y => q y*Real.exp (-τ*(d (e x) y : ℝ)))]
  simp only [inv]

private noncomputable def symPrior (q : X → ℝ) (e : X ≃ X) (x : X) := (q x+q (e x))/2

private theorem symPrior_optimal {P q : X → ℝ} {τ : ℝ} {d : X → X → ℕ}
    (pos : ∀ x, 0<P x) (opt : Optimal P τ d q) (e : X ≃ X)
    (pinv : ∀ x, P (e x)=P x) (dinv : ∀ x y, d (e x) (e y)=d x y) :
    Optimal P τ d (symPrior q e) := by
  let r (x : X) := q (e x)
  have h : IsPrior r := ⟨fun y => opt.1.1 _,(e.sum_comp q).trans opt.1.2⟩
  have obj : mean P (score τ d r)=mean P (score τ d q) := by
    unfold mean
    rw [←e.sum_comp (fun y => P y*score τ d q y)]
    simp only [score,r,push_Z τ d q e dinv,pinv]
  have ro : Optimal P τ d r := ⟨h,fun a ha => obj.trans_le (opt.2 a ha)⟩
  have same := optimal_Z_eq pos opt ro
  have prior : IsPrior (symPrior q e) := by
    refine ⟨fun a => div_nonneg (add_nonneg (opt.1.1 _) (opt.1.1 _)) (by norm_num),?_⟩
    change ∑ a, (q a+r a)/2=1
    simp only [div_eq_mul_inv,←Finset.sum_mul,Finset.sum_add_distrib,opt.1.2,h.2]
    norm_num
  have z (x : X) : Z τ d (symPrior q e) x=Z τ d q x := by
    have mix : Z τ d (symPrior q e) x=(Z τ d q x+Z τ d r x)/2 := by
      unfold Z symPrior
      simp only [div_eq_mul_inv,Finset.sum_mul,←Finset.sum_add_distrib]
      rw [←Finset.sum_mul]
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y _
      dsimp only [r]
      ring
    rw [mix,←same]
    ring
  refine ⟨prior,fun a ha => ?_⟩
  have eq : score τ d (symPrior q e) = score τ d q := by funext x; exact congrArg (fun t => -Real.log t) (z x)
  rw [eq]
  exact opt.2 a ha

/-- A common optimal reproduction law may be chosen invariant under both
reversal and complement, for every multiplier. -/
theorem symmetric_choice {p τ : ℝ} (hp : 0<p) (ph : p<1) (n : ℕ)
    {q : Word n → ℝ} (opt : Optimal (mass p n) τ (distance n) q) :
    ∃ v, Optimal (mass p n) τ (distance n) v ∧
      (∀ x, v (complement (n+1) x)=v x) ∧ (∀ x, v (reverseBits (n+1) x)=v x) := by
  let C := complementEquiv (n+1)
  let R := reverseEquiv (n+1)
  let u := symPrior q C
  let v := symPrior u R
  have uo := symPrior_optimal (mass_pos hp ph n) opt C (complement_mass p n) (complement_distance n)
  have vo := symPrior_optimal (mass_pos hp ph n) uo R (reverse_mass p n) (reverse_distance n)
  have uc (x : Word n) : u (complement (n+1) x)=u x := by
    change (q (complement _ x)+q (complement _ (complement _ x)))/2=_
    rw [complement_twice]
    exact congrArg (·/2) (add_comm _ _)
  refine ⟨v,vo,?_,?_⟩
  · intro x
    change (u (complement _ x)+u (reverseBits _ (complement _ x)))/2=_
    rw [←complement_reverse,uc,uc]
    rfl
  · intro x
    change (u (reverseBits _ x)+u (reverseBits _ (reverseBits _ x)))/2=_
    rw [reverse_reverse]
    exact congrArg (·/2) (add_comm _ _)

private theorem first_complement (n : ℕ) (x : Word n) :
    firstSpin n (complement (n+1) x)= -firstSpin n x := by
  change bitSpin (!x.1)= -bitSpin x.1
  cases x.1 <;> norm_num [bitSpin]

theorem symmetric_centered {n : ℕ} {q : Word n → ℝ}
    (hc : ∀ x, q (complement (n+1) x)=q x) (hr : ∀ x, q (reverseBits (n+1) x)=q x) :
    mean q (endSpin n)=0 ∧ mean q (firstSpin n)=0 := by
  have c := (complementEquiv (n+1)).sum_comp (fun x => q x*firstSpin n x)
  change (∑ x, q (complement _ x)*firstSpin n (complement _ x))=_ at c
  simp only [hc,first_complement,mul_neg,Finset.sum_neg_distrib] at c
  have zero : mean q (firstSpin n)=0 := by unfold mean; linarith
  refine ⟨?_,zero⟩
  have r := (reverseEquiv (n+1)).sum_comp (fun x => q x*firstSpin n x)
  change (∑ x, q (reverseBits _ x)*bitSpin ((reverseBits _ x).1))=mean q (firstSpin n) at r
  rw [zero] at r
  simpa only [hr,reverse_first,endSpin,mean] using r

theorem symmetric_endpoints {p τ : ℝ} {n : ℕ} {q : Word n → ℝ}
    (hr : ∀ x, q (reverseBits (n+1) x)=q x) :
    endpointCorrelation p τ n q (endSpin n)=endpointCorrelation p τ n q (firstSpin n) := by
  let e := reverseEquiv (n+1)
  have mv : (fun x => q (e x))=q := funext hr
  have z (x : Word n) : Z τ (distance n) q (e x)=Z τ (distance n) q x := by
    rw [←push_Z τ _ q e (reverse_distance n),mv]
  let W := gibbsChannel τ (distance n) q
  have w (x y : Word n) : W (e x) (e y)=W x y := by
    unfold W gibbsChannel
    rw [show q (e y)=_ from hr y,show distance n (e x) (e y)=_ from reverse_distance n x y,z]
  have f (x : Word n) : firstSpin n (e x)=endSpin n x := congrArg bitSpin (reverse_first n x)
  have inner (x : Word n) : mean (W (e x)) (firstSpin n)=mean (W x) (endSpin n) := by
    unfold mean
    rw [←e.sum_comp (fun y => W (e x) y*firstSpin n y)]
    simp only [w,f]
  have sum := e.sum_comp (fun x => mass p n x*(firstSpin n x*mean (W x) (firstSpin n)))
  have m (x : Word n) : mass p n (e x)=mass p n x := reverse_mass p n x
  simp only [m,f,inner] at sum
  exact sum

#print axioms symmetric_choice
#print axioms symmetric_endpoints
end BlockHierarchy.VarianceLimit
