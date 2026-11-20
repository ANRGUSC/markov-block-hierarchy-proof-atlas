import BlockHierarchy.VarianceLimit.Statement
import ChannelOptimizer

open scoped BigOperators
namespace BlockHierarchy.Converse
open Cut VarianceLimit

variable {X : Type*} [Fintype X]

private theorem info_joint {P : X → ℝ} (pos : ∀ x, 0<P x) (W : X → X → ℝ) (hw : IsChannel W) :
    informationNats P W=Channel.info P (fun y => ∑ x,P x*W x y) (fun x y => P x*W x y) := by
  unfold informationNats Channel.info
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases e : W x y=0
  · simp [e]
  have py : 0<∑ u,P u*W u y := (mul_pos (pos x) (lt_of_le_of_ne ((hw x).1 y) (Ne.symm e))).trans_le
    (Finset.single_le_sum (fun u (_ : u∈Finset.univ) => mul_nonneg (pos u).le ((hw u).1 y)) (Finset.mem_univ x))
  rw [Real.log_div e py.ne',Real.log_mul (pos x).ne' e]
  ring

/-- A normalized backward channel with an affine log kernel gives the finite
Shannon lower bound. A reproducing law with the same source marginal attains it. -/
theorem backward_rate_pair (P q : X → ℝ) (d : X → X → ℕ) (K : X → X → ℝ) (s z δ : ℝ)
    (hp : IsPrior P) (pos : ∀ x, 0<P x) (hq : IsPrior q) (ks : ∀ x y, 0<K x y)
    (kn : ∀ y, ∑ x,K x y=1) (kr : ∀ x, ∑ y,q y*K x y=P x)
    (kl : ∀ x y, Real.log (K x y)=s*(d x y : ℝ)-z)
    (kc : ∀ y, ∑ x, K x y*(d x y : ℝ)=δ) (hs : s≤0) :
    (∀ W, IsChannel W → totalDistortion P d W≤δ →
      -mean P (fun x => Real.log (P x))+s*δ-z ≤ informationNats P W) ∧
    (∃ W, IsChannel W ∧ totalDistortion P d W=δ ∧
      informationNats P W= -mean P (fun x => Real.log (P x))+s*δ-z) := by
  let dR (x y : X) := (d x y : ℝ)
  constructor
  · intro W hw budget
    let J (x y : X) := P x*W x y
    let v (y : X) := ∑ x,J x y
    have src (x : X) : ∑ y,J x y=P x := by simp [J,←Finset.mul_sum,(hw x).2]
    have h := Channel.rate_lower_bound P v J K dR s z
      (fun x y => mul_nonneg (hp.1 x) ((hw x).1 y)) ks src (fun _ => rfl) kn hp.2 kl
    rw [info_joint pos W hw]
    change _ ≤ Channel.info P v J
    have hb : s*δ ≤ s*Channel.cost dR J := mul_le_mul_of_nonpos_left budget hs
    change -mean P (fun x => Real.log (P x))+s*Channel.cost dR J-z ≤ _ at h
    linarith only [h,hb]
  · let W (x y : X) := q y*K x y/P x
    have joint (x y : X) : P x*W x y=q y*K x y := by dsimp [W]; field_simp [(pos x).ne']
    have hw : IsChannel W := by
      intro x
      refine ⟨fun y => div_nonneg (mul_nonneg (hq.1 y) (ks x y).le) (pos x).le,?_⟩
      simp only [W,div_eq_mul_inv,←Finset.sum_mul,kr,mul_inv_cancel₀ (pos x).ne']
    have col (y : X) : ∑ x,P x*W x y=q y := by simp only [joint,←Finset.mul_sum,kn,mul_one]
    have cost : Channel.cost dR (fun x y => q y*K x y)=δ := by
      unfold Channel.cost
      rw [Finset.sum_comm]
      simp only [dR,mul_assoc,←Finset.mul_sum,kc,←Finset.sum_mul,hq.2,one_mul]
    refine ⟨W,hw,?_,?_⟩
    · unfold totalDistortion
      simp_rw [joint]
      exact cost
    · rw [info_joint pos W hw]
      simp_rw [col,joint]
      have h := Channel.backward_attains P q K dR s z ks kr hp.2 kl
      rw [cost] at h
      exact h

#print axioms backward_rate_pair
end BlockHierarchy.Converse
