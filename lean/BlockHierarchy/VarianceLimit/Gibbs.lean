import BlockHierarchy.VarianceLimit.Statement
import BlockHierarchy.Cut.Optimality
import Variational

open scoped BigOperators
namespace BlockHierarchy.VarianceLimit
open Cut

variable {X : Type*} [Fintype X]

noncomputable def gibbsChannel (τ : ℝ) (d : X → X → ℕ) (q : X → ℝ) (x y : X) : ℝ :=
  q y * Real.exp (-τ*(d x y : ℝ)) / Z τ d q x

theorem gibbs_isChannel (τ : ℝ) (d : X → X → ℕ) {q : X → ℝ} (hq : IsPrior q) :
    IsChannel (gibbsChannel τ d q) := by
  intro x
  refine ⟨fun y => div_nonneg (mul_nonneg (hq.1 y) (Real.exp_pos _).le) (Z_pos τ d hq x).le,?_⟩
  unfold gibbsChannel
  simp only [div_eq_mul_inv,←Finset.sum_mul]
  exact mul_inv_cancel₀ (Z_pos τ d hq x).ne'

theorem gibbs_marginal {τ : ℝ} {d : X → X → ℕ} {P q : X → ℝ}
    (hp : IsPrior P) (opt : Optimal P τ d q) (y : X) :
    ∑ x, P x*gibbsChannel τ d q x y=q y := by
  let W := gibbsChannel τ d q
  let M (v : X) := ∑ x, P x*W x v
  have law := gibbs_isChannel τ d opt.1
  have upper (v : X) : M v ≤ q v := by
    have factor : M v = q v * (∑ x, P x*Real.exp (-τ*(d x v : ℝ))/Z τ d q x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      dsimp [W,gibbsChannel]
      ring
    rw [factor]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (optimal_column hp.2 opt v) (opt.1.1 v)
  have total : ∑ v, M v=1 := by
    unfold M
    rw [Finset.sum_comm]
    simp only [←Finset.mul_sum,W,(law _).2,mul_one,hp.2]
  have zero : ∑ v, (q v-M v)=0 := by rw [Finset.sum_sub_distrib,opt.1.2,total,sub_self]
  exact (sub_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg
    (fun v (_ : v ∈ Finset.univ) => sub_nonneg.mpr (upper v))).mp zero y (Finset.mem_univ _))).symm

theorem gibbs_attains {τ : ℝ} {d : X → X → ℕ} {P q : X → ℝ}
    (hp : IsPrior P) (opt : Optimal P τ d q) :
    informationNats P (gibbsChannel τ d q) + τ*totalDistortion P d (gibbsChannel τ d q) =
      mean P (score τ d q) := by
  let W := gibbsChannel τ d q
  have law := gibbs_isChannel τ d opt.1
  have term (x y : X) : P x*W x y*Real.log (W x y/q y)+τ*(P x*W x y*(d x y : ℝ))=
      P x*W x y*score τ d q x := by
    by_cases z : q y=0
    · simp [W,gibbsChannel,z]
    have eq : W x y/q y=Real.exp (-τ*(d x y : ℝ))/Z τ d q x := by
      dsimp [W,gibbsChannel]
      field_simp [z]
    rw [eq,Real.log_div (Real.exp_pos _).ne' (Z_pos τ d opt.1 x).ne',Real.log_exp]
    unfold score
    ring
  unfold informationNats totalDistortion mean
  change (∑ x, ∑ y, P x*W x y*Real.log (W x y/(∑ u,P u*W u y)))+
    τ*(∑ x, ∑ y, P x*W x y*(d x y : ℝ))=_
  have marg (y : X) : ∑ u,P u*W u y=q y := gibbs_marginal hp opt y
  simp only [marg,Finset.mul_sum,←Finset.sum_add_distrib,term]
  simp only [←Finset.sum_mul,←Finset.mul_sum,W,(law _).2,mul_one]


/-- The relative-entropy dual bound applies to every test channel, including
channels with a reproduction symbol of zero marginal probability. -/
theorem gibbs_variational [Nonempty X] {τ : ℝ} {d : X → X → ℕ} {P q : X → ℝ}
    (hp : IsPrior P) (pos : ∀ x, 0<P x) (opt : Optimal P τ d q)
    (W : X → X → ℝ) (hW : IsChannel W) :
    mean P (score τ d q) ≤ informationNats P W + τ*totalDistortion P d W := by
  classical
  let J (x y : X) := P x*W x y
  let v (y : X) := ∑ x, J x y
  let K (x y : X) := P x * Real.exp (-τ*(d x y : ℝ)) / Z τ d q x
  have nn (x y : X) : 0≤J x y := mul_nonneg (hp.1 x) ((hW x).1 y)
  have kp (x y : X) : 0<K x y := div_pos (mul_pos (pos x) (Real.exp_pos _)) (Z_pos τ d opt.1 x)
  have kl := Channel.subprob_entropy_bound J K v nn kp (fun _ => rfl) (optimal_column hp.2 opt)
  have row (x : X) : ∑ y, J x y=P x := by simp [J,←Finset.mul_sum,(hW x).2]
  have term (x y : X) : J x y*(Real.log (J x y)-Real.log (v y)-Real.log (K x y)) =
      J x y*Real.log (W x y/v y) + τ*(J x y*(d x y : ℝ)) - J x y*score τ d q x := by
    by_cases z : W x y=0
    · simp [J,z]
    have positive := mul_pos (pos x) (lt_of_le_of_ne ((hW x).1 y) (Ne.symm z))
    have vp : 0<v y := positive.trans_le
      (Finset.single_le_sum (fun u (_ : u ∈ Finset.univ) => nn u y) (Finset.mem_univ x))
    have lk : Real.log (K x y)=Real.log (P x)-τ*(d x y : ℝ)-Real.log (Z τ d q x) := by
      dsimp only [K]
      rw [Real.log_div (mul_pos (pos x) (Real.exp_pos _)).ne' (Z_pos τ d opt.1 x).ne',
        Real.log_mul (pos x).ne' (Real.exp_pos _).ne',Real.log_exp]
      ring
    have lj : Real.log (J x y)=Real.log (P x)+Real.log (W x y) := Real.log_mul (pos x).ne' z
    rw [lj,lk,Real.log_div z vp.ne']
    unfold score
    ring
  simp_rw [term] at kl
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul,row] at kl
  change 0 ≤ informationNats P W+τ*totalDistortion P d W-mean P (score τ d q) at kl
  linarith

#print axioms gibbs_marginal
#print axioms gibbs_attains
#print axioms gibbs_variational
end BlockHierarchy.VarianceLimit
