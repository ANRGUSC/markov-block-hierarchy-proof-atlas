import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open Filter
open scoped Topology
namespace BlockHierarchy.VarianceLimit

/-- Equation (cut) on positive block lengths. -/
def CutBound (σ : ℕ → ℝ) (B : ℝ) : Prop :=
  ∀ n k : ℕ, 0 < n → 0 < k → |σ (n+k) - √((σ n)^2 + (σ k)^2)| ≤ B

private theorem hypot_shift {a b c : ℝ} (h : b ≤ a) :
    √(a^2+c^2) ≤ √(b^2+c^2)+(a-b) := by
  have hs := Real.sqrt_nonneg (b^2+c^2)
  have hsq := Real.sq_sqrt (add_nonneg (sq_nonneg b) (sq_nonneg c))
  have hbase : b ≤ √(b^2+c^2) := by nlinarith only [hsq,hs,sq_nonneg c]
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (add_nonneg hs (sub_nonneg.mpr h))).mp
  rw [Real.sq_sqrt (add_nonneg (sq_nonneg a) (sq_nonneg c))]
  nlinarith only [hsq, mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr hbase)]

private theorem hypot_lipschitz {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (c : ℝ) :
    |√(a^2+c^2)-√(b^2+c^2)| ≤ |a-b| := by
  rcases le_total b a with h|h
  · have hs := Real.sqrt_le_sqrt (show b^2+c^2 ≤ a^2+c^2 by nlinarith [mul_nonneg (sub_nonneg.mpr h) (add_nonneg ha hb)])
    rw [abs_of_nonneg (sub_nonneg.mpr hs), abs_of_nonneg (sub_nonneg.mpr h)]
    linarith [hypot_shift (c := c) h]
  · have hs := Real.sqrt_le_sqrt (show a^2+c^2 ≤ b^2+c^2 by nlinarith [mul_nonneg (sub_nonneg.mpr h) (add_nonneg ha hb)])
    rw [abs_sub_comm, abs_sub_comm a b, abs_of_nonneg (sub_nonneg.mpr hs), abs_of_nonneg (sub_nonneg.mpr h)]
    linarith [hypot_shift (c := c) h]

private theorem hypot_scale {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    √((√t*s)^2+s^2) = √(t+1)*s := by
  rw [mul_pow,Real.sq_sqrt ht,← add_one_mul,Real.sqrt_mul (by positivity),Real.sqrt_sq hs]

/-- Join t+1 equal pieces. The accumulated error in the unnormalized standard
deviation is at most t times the one-cut error. -/
theorem equal_pieces {σ : ℕ → ℝ} {B : ℝ} (hs : ∀ n, 0 < n → 0 ≤ σ n) (cut : CutBound σ B)
    (n : ℕ) (hn : 0 < n) (t : ℕ) :
    |σ ((t+1)*n) - √((t+1 : ℕ) : ℝ)*σ n| ≤ (t:ℝ)*B := by
  induction t with
  | zero => simp
  | succ t ih =>
    have pos : 0 < (t+1)*n := Nat.mul_pos (by omega) hn
    have bound := cut ((t+1)*n) n pos hn
    have lip := hypot_lipschitz (hs _ pos)
      (mul_nonneg (Real.sqrt_nonneg ((t+1:ℕ):ℝ)) (hs _ hn)) (σ n)
    rw [hypot_scale (by positivity) (hs _ hn)] at lip
    rw [Nat.succ_mul (t+1)]
    push_cast at lip ih ⊢
    calc
      _ ≤ _ := abs_sub_le (σ ((t+1)*n+n)) (√((σ ((t+1)*n))^2+(σ n)^2)) _
      _ ≤ B+(t:ℝ)*B := add_le_add bound (lip.trans ih)
      _ = _ := by ring

private noncomputable def ratio := 1 / √(2:ℝ)

private theorem ratio_pos : 0 < ratio := by unfold ratio; positivity

private theorem ratio_lt : ratio < 1 := by
  unfold ratio
  rw [div_lt_one (by positivity)]
  nlinarith only [Real.sq_sqrt (by norm_num : 0 ≤ (2:ℝ)), Real.sqrt_nonneg (2:ℝ)]

noncomputable def dyadic (σ : ℕ → ℝ) (n k : ℕ) := ratio^k * σ (2^k*n)

theorem doubling_steps {σ : ℕ → ℝ} {B : ℝ} (hs : ∀ n, 0 < n → 0 ≤ σ n) (cut : CutBound σ B)
    {n : ℕ} (hn : 0 < n) (k : ℕ) :
    dist (dyadic σ n k) (dyadic σ n (k+1)) ≤ (B*ratio)*ratio^k := by
  let m := 2^k*n
  have hm : 0 < m := Nat.mul_pos (by positivity) hn
  have bound := cut m m hm hm
  have sq : √((σ m)^2+(σ m)^2) = √(2:ℝ)*σ m := by
    rw [← two_mul, Real.sqrt_mul (by norm_num),Real.sqrt_sq (hs _ hm)]
  rw [sq] at bound
  have index : 2^(k+1)*n = m+m := by dsimp [m]; ring
  have eq : dyadic σ n (k+1) - dyadic σ n k =
      (ratio^k*ratio) * (σ (m+m)-√(2:ℝ)*σ m) := by
    dsimp only [dyadic]
    rw [index,pow_succ]
    change ratio^k*ratio*σ (m+m) - ratio^k*σ m = _
    have hr : ratio*√(2:ℝ) = 1 := by unfold ratio; field_simp
    rw [mul_sub]
    congr 1
    calc
      _ = ratio^k*(ratio*√(2:ℝ))*σ m := by rw [hr,mul_one]
      _ = _ := by ring
  rw [Real.dist_eq,abs_sub_comm,eq,abs_mul,abs_of_nonneg (mul_nonneg (pow_nonneg ratio_pos.le _) ratio_pos.le)]
  calc
    _ ≤ (ratio^k*ratio)*B := mul_le_mul_of_nonneg_left bound (mul_nonneg (pow_nonneg ratio_pos.le _) ratio_pos.le)
    _ = _ := by ring

theorem dyadic_limit {σ : ℕ → ℝ} {B : ℝ} (hs : ∀ n, 0 < n → 0 ≤ σ n) (cut : CutBound σ B)
    {n : ℕ} (hn : 0 < n) :
    ∃ L, Tendsto (dyadic σ n) atTop (𝓝 L) ∧ |σ n - L| ≤ (1+√2)*B := by
  have steps := doubling_steps hs cut hn
  obtain ⟨L,hL⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric ratio (B*ratio) ratio_lt steps)
  refine ⟨L,hL,?_⟩
  have h := dist_le_of_le_geometric_of_tendsto₀ ratio (B*ratio) ratio_lt steps hL
  have id : (1+√2)*(1-ratio) = ratio := by
    unfold ratio
    field_simp
    nlinarith only [Real.sq_sqrt (by norm_num : 0 ≤ (2:ℝ))]
  have hC : B*ratio/(1-ratio) = (1+√2)*B := by
    apply (div_eq_iff (sub_ne_zero.mpr ratio_lt.ne')).mpr
    calc
      _ = B*((1+√2)*(1-ratio)) := by rw [id]
      _ = _ := by ring
  simpa only [Real.dist_eq, dyadic, pow_zero, one_mul, hC] using h

private theorem identify_limit {σ : ℕ → ℝ} {B : ℝ} (hs : ∀ n, 0 < n → 0 ≤ σ n)
    (cut : CutBound σ B) {L : ℝ} (one : Tendsto (dyadic σ 1) atTop (𝓝 L))
    (t : ℕ) {M : ℝ} (many : Tendsto (dyadic σ (t+1)) atTop (𝓝 M)) :
    M = √((t+1:ℕ):ℝ) * L := by
  let s := √((t+1:ℕ):ℝ)
  have compare (k : ℕ) :
      |dyadic σ (t+1) k - s*dyadic σ 1 k| ≤ ratio^k*((t:ℝ)*B) := by
    have pieces := equal_pieces hs cut (2^k) (by positivity) t
    calc
      _ = |ratio^k * (σ ((t+1)*2^k) - s*σ (2^k))| := by
        unfold dyadic
        rw [Nat.mul_one, Nat.mul_comm (2^k) (t+1)]
        congr 1
        ring
      _ ≤ _ := by
        rw [abs_mul,abs_of_nonneg (pow_nonneg ratio_pos.le _)]
        exact mul_le_mul_of_nonneg_left pieces (pow_nonneg ratio_pos.le _)
  have upper : Tendsto (fun k : ℕ => ratio^k*((t:ℝ)*B)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ratio_pos.le ratio_lt).mul_const ((t:ℝ)*B)
  have lower : Tendsto (fun k => |dyadic σ (t+1) k-s*dyadic σ 1 k|) atTop (𝓝 |M-s*L|) :=
    (many.sub (one.const_mul s)).abs
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm (le_of_tendsto_of_tendsto' lower upper compare) (abs_nonneg _)))

/-- The pointwise-in-multiplier quantitative part of Theorem (common).
No restriction on the unused value at block length zero is necessary. -/
theorem common_limit {σ : ℕ → ℝ} {B : ℝ} (hs : ∀ n, 0 < n → 0 ≤ σ n) (cut : CutBound σ B) :
    ∃ L : ℝ, 0 ≤ L ∧ Tendsto (fun n : ℕ => σ n / √(n:ℝ)) atTop (𝓝 L) ∧
      ∀ n : ℕ, 0 < n → |σ n / √(n:ℝ) - L| ≤ (1+√2)*B / √(n:ℝ) := by
  obtain ⟨L,one,_⟩ := dyadic_limit hs cut (n := 1) (by decide)
  have nonneg : 0 ≤ L := ge_of_tendsto' one (fun k =>
    mul_nonneg (pow_nonneg ratio_pos.le k) (hs _ (by positivity)))
  have error (n : ℕ) (hn : 0 < n) :
      |σ n / √(n:ℝ) - L| ≤ (1+√2)*B / √(n:ℝ) := by
    obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    obtain ⟨M,many,bound⟩ := dyadic_limit hs cut hn
    rw [identify_limit hs cut one t many] at bound
    have den : 0 < √((t+1:ℕ):ℝ) := by positivity
    have eq : σ (t+1)/√((t+1:ℕ):ℝ)-L =
        (σ (t+1) - √((t+1:ℕ):ℝ)*L)/√((t+1:ℕ):ℝ) := by
      field_simp
    rw [eq,abs_div,abs_of_nonneg den.le]
    exact div_le_div_of_nonneg_right bound den.le
  refine ⟨L,nonneg,?_,error⟩
  have large : ∀ᶠ n : ℕ in atTop, dist (σ n/√(n:ℝ)) L ≤ (1+√2)*B/√(n:ℝ) :=
    eventually_atTop.2 ⟨1, fun n hn => by simpa only [Real.dist_eq] using error n hn⟩
  have vanishes : Tendsto (fun n : ℕ => (1+√2)*B/√(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  exact tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg)
    large vanishes)

#print axioms equal_pieces
#print axioms dyadic_limit
#print axioms common_limit
end BlockHierarchy.VarianceLimit
