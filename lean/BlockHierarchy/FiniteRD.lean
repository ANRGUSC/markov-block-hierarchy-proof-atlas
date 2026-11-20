import Variational
import ReducedPair.Moments

open scoped BigOperators
namespace BlockHierarchy.FiniteRD
variable {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X]

def Optimal (P : X → ℝ) (q : Y → ℝ) (d : X → Y → ℕ) (J : X → Y → ℝ) (b : ℝ) : Prop :=
  (∀ x y, 0 ≤ J x y) ∧ (∀ x, ∑ y, J x y = P x) ∧ (∀ y, ∑ x, J x y = q y) ∧
  Channel.cost (fun x y => (d x y : ℝ)) J ≤ b ∧
  ∀ t L, (∀ x y, 0 ≤ L x y) → (∀ x, ∑ y, L x y=P x) → (∀ y, ∑ x, L x y=t y) →
    Channel.cost (fun x y => (d x y : ℝ)) L ≤ b → Channel.info P q J ≤ Channel.info P t L

noncomputable def kernel (P Z : X → ℝ) (d : X → Y → ℕ) (u : ℝ) (x : X) (y : Y) :=
  P x/Z x * u^(d x y)

noncomputable def joint (P Z : X → ℝ) (q : Y → ℝ) (d : X → Y → ℕ) (u : ℝ) (x : X) (y : Y) :=
  q y * kernel P Z d u x y

theorem certificate {P Z : X → ℝ} {q : Y → ℝ} {d : X → Y → ℕ} {u b : ℝ}
    (hp : ∀ x, 0 < P x) (hz : ∀ x, 0 < Z x) (hq : ∀ y, 0 ≤ q y) (hu : 0 < u) (h1 : u ≤ 1)
    (norm : ∀ x, ∑ y, q y*u^(d x y) = Z x)
    (columns : ∀ y, (∑ x, kernel P Z d u x y) ≤ 1 ∧
      (q y ≠ 0 → ∑ x, kernel P Z d u x y = 1))
    (cost : Channel.cost (fun x y => (d x y : ℝ)) (joint P Z q d u) = b) :
    Optimal P q d (joint P Z q d u) b ∧
    Channel.info P q (joint P Z q d u) / Real.log 2 =
      b*logTwo u - mean P (fun x => logTwo (Z x)) := by
  let K := kernel P Z d u
  let J := joint P Z q d u
  have pos (x y) : 0 < K x y := mul_pos (div_pos (hp x) (hz x)) (pow_pos hu _)
  have row (x : X) : ∑ y, q y*K x y=P x := by
    change ∑ y, q y*(P x/Z x*u^(d x y))=P x
    simp_rw [mul_left_comm (q _) (P x/Z x), ← Finset.mul_sum, norm]
    exact div_mul_cancel₀ _ (hz x).ne'
  have col (y : Y) : ∑ x, q y*K x y=q y := by
    rw [← Finset.mul_sum]
    by_cases e : q y=0
    · simp [e]
    · rw [(columns y).2 e,mul_one]
  have logs (x y) : Real.log (K x y)=Real.log u*(d x y : ℝ)+(Real.log (P x)-Real.log (Z x)) := by
    change Real.log (P x/Z x*u^(d x y))=_
    rw [Real.log_mul (div_pos (hp x) (hz x)).ne' (pow_pos hu _).ne',
      Real.log_div (hp x).ne' (hz x).ne',Real.log_pow]
    ring
  constructor
  · refine ⟨fun x y => mul_nonneg (hq y) (pos x y).le,row,col,cost.le,?_⟩
    intro t L hL src dst budget
    exact Channel.column_optimal _ q t K L _ _ _ (Real.log_nonpos hu.le h1)
      pos hL row dst src (fun y => (columns y).1) logs (budget.trans_eq cost.symm)
  have term (x y) : J x y*(Real.log (J x y)-Real.log (P x)-Real.log (q y)) =
      (J x y*(d x y : ℝ))*Real.log u-J x y*Real.log (Z x) := by
    by_cases e : q y=0
    · simp [J,joint,e]
    · change J x y*(Real.log (q y*K x y)-Real.log (P x)-Real.log (q y))=_
      rw [Real.log_mul e (pos x y).ne',logs]
      ring
  have val : Channel.info P q J = b*Real.log u-mean P (fun x => Real.log (Z x)) := by
    unfold Channel.info
    simp_rw [term]
    have rows (x) : ∑ y, J x y=P x := row x
    simp only [Finset.sum_sub_distrib,← Finset.sum_mul,rows]
    change Channel.cost (fun x y => (d x y : ℝ)) J*Real.log u-_=_
    rw [cost]
    rfl
  change Channel.info P q J/Real.log 2=_
  rw [val]
  simp only [mean,logTwo,div_eq_mul_inv,sub_mul,Finset.sum_mul,mul_assoc]

end BlockHierarchy.FiniteRD
