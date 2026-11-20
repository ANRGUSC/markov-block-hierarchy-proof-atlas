import BlockHierarchy.Converse.Center
import BlockHierarchy.Converse.Tails
import BlockHierarchy.Converse.Quantile
import BlockHierarchy.Converse.Rate

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators
namespace BlockHierarchy.Converse
open Cut Varentropy

private theorem minimum_feasible (p : ℝ) {D ε : ℝ} (hd : 0<D) (he : 0<ε) (n : ℕ) :
    sInf (feasibleSizes p D ε n) ∈ feasibleSizes p D ε n := by
  classical
  have bits (k : ℕ) : Nonempty (Bits k) := by
    induction k with
    | zero => exact ⟨()⟩
    | succ k ih => exact ⟨false,Classical.choice ih⟩
  let : Nonempty (Word n) := bits (n+1)
  have self : ∀ k (x : Bits k), hamming k x x=0 := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih => intro x; simp [hamming,ih]
  apply Nat.sInf_mem
  refine ⟨Fintype.card (Word n),Fintype.card_pos,Fintype.equivFin _,(Fintype.equivFin _).symm,?_⟩
  have prod : 0≤((n:ℝ)+1)*D := by positivity
  simpa [distance,self,not_lt_of_ge prod] using he.le

private theorem below_quantile {ε : ℝ} (he : ε<1) {a : ℝ} (ha : a<upperQuantile ε) :
    ε<gaussianTail a := by
  let μ := gaussianReal 0 1
  have h : Tendsto (fun t : ℝ => μ.real (Set.Ici t)) atBot (𝓝 1) := by
    simpa [measureReal_def, Function.comp_def] using (ENNReal.tendsto_toReal (measure_ne_top μ Set.univ)).comp
      (tendsto_measure_Ici_atBot μ)
  obtain ⟨u,hu⟩ := (h.eventually_const_lt he).exists
  have bounded : BddBelow {x : ℝ | gaussianTail x≤ε} := by
    refine ⟨u-1,?_⟩
    intro x hx
    by_contra! hxu
    have subset : Set.Ici u ⊆ Set.Ioi x := by intro y hy; change x<y; linarith [show u≤y from hy]
    exact hu.not_ge ((measureReal_mono (μ:=μ) subset).trans hx)
  by_contra! hbad
  exact ha.not_ge (csInf_le bounded hbad)

private theorem dispersion_scale {p : ℝ} (hp : 0<p) (ph : p<1/2) :
    Real.sqrt (sourceDispersion p)=scale p/Real.log 2 := by
  have h : 0≤Real.log ((1-p)/p)/Real.log 2 :=
    div_nonneg (Real.log_nonneg ((le_div_iff₀ hp).2 (by linarith))) (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  rw [sourceDispersion,Real.sqrt_mul (mul_nonneg hp.le (by linarith)),Real.sqrt_sq h,scale,mul_div_assoc]

theorem low_distortion_converse : LowDistortionConverseStatement := by
  intro p D ε hp ph hd hD he he' a ha
  let M := fun n => sInf (feasibleSizes p D ε n)
  let r (n : ℕ) := (Real.log (M n)-center p D n)/(Real.sqrt n*scale p)
  let γ (n : ℕ) := Real.sqrt (Real.sqrt n)
  let ov (n : ℕ) := γ n/(Real.sqrt n*scale p)
  let tail (n : ℕ) (b : ℝ) := ∑ v : Bits n, if b<normalizedFlips p n v then iidFlips p n v else 0
  have sp := scale_pos hp ph
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  have dh := hD.trans_lt (Recurrence.gray_interior hp ph).2
  have ht : Tendsto (fun n : ℕ => Real.sqrt (n:ℝ)) atTop atTop := Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hg : Tendsto γ atTop atTop := Real.tendsto_sqrt_atTop.comp ht
  have hov : Tendsto ov atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x:=(1:ℝ))).div_atTop hg
    have eq (n : ℕ) : ov n=(1/γ n)/scale p := by
      dsimp [ov,γ]
      rw [←div_div,Real.sqrt_div_self']
    rw [show ov = (fun n => (1/γ n)/scale p) from funext eq]
    simpa only [zero_div,Pi.div_def] using h.div_const (scale p)
  have hrm : Tendsto (fun n => Real.exp (-(γ n))) atTop (𝓝 0) := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hg)
  have flips (n : ℕ) (w : Bits n) : 0 ≤ iidFlips p n w := by
    induction n with
    | zero => exact zero_le_one
    | succ n ih =>
      unfold iidFlips
      apply mul_nonneg _ (ih _)
      split <;> linarith
  have mono (n : ℕ) : Antitone (tail n) := by
    intro x y hxy
    apply Finset.sum_le_sum
    intro w _
    split_ifs <;> first | rfl | exact flips _ _ | linarith
  have finite : ∀ᶠ n : ℕ in atTop, tail n (r n+ov n)≤ε+Real.exp (-(γ n)) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact code_tail_bound hp ph hd dh hn (minimum_feasible p hd he n) (γ n)
  have clt (b : ℝ) (_ : b<upperQuantile ε) : Tendsto (fun n => tail n b) atTop (𝓝 (gaussianTail b)) :=
    normalized_flip_tails ⟨p,hp.le,by linarith⟩ hp (by linarith) b
  have low := quantile_lower r ov (fun n => Real.exp (-(γ n))) tail gaussianTail mono
    (fun _ hb => below_quantile he' hb) clt hov hrm finite
  have pos := div_pos sp hl
  rw [dispersion_scale hp ph] at ha
  obtain ⟨b,hab,hb⟩ := exists_between ((div_lt_iff₀ pos).2 (by linarith only [ha,mul_comm (upperQuantile ε) (scale p/Real.log 2)]) :
      a/(scale p/Real.log 2)<upperQuantile ε)
  let c := Real.log 2-binaryEntropyNats p
  let A (n : ℕ) := (b*scale p*(Real.sqrt n/Real.sqrt ((n:ℝ)+1)) + c/Real.sqrt ((n:ℝ)+1))/Real.log 2
  have ratio : Tendsto (fun n : ℕ => Real.sqrt n /Real.sqrt ((n:ℝ)+1)) atTop (𝓝 1) := by
    have h := ((tendsto_const_nhds (x:=(1:ℝ))).sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))).sqrt
    have eq (n : ℕ) : 1-1/((n:ℝ)+1)=(n:ℝ)/((n:ℝ)+1) := by field_simp; ring
    simpa only [eq,Real.sqrt_div (Nat.cast_nonneg _),sub_zero,Real.sqrt_one] using h
  have root : Tendsto (fun n : ℕ => Real.sqrt ((n:ℝ)+1)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have conv : Tendsto A atTop (𝓝 (b*(scale p/Real.log 2))) := by
    have h := ((tendsto_const_nhds (x:=b*scale p)).mul ratio).add ((tendsto_const_nhds (x:=c)).div_atTop root)
    simpa [A,mul_div_assoc] using h.div_const (Real.log 2)
  filter_upwards [low b hb,conv.eventually_const_lt ((div_lt_iff₀ pos).mp hab),eventually_gt_atTop 0] with n hn hA npos
  apply hA.trans
  have ns : 0<Real.sqrt (n:ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.mpr npos)
  have ns' : 0<Real.sqrt ((n:ℝ)+1) := Real.sqrt_pos.2 (by positivity)
  have pow := Real.sq_sqrt (show 0≤(n:ℝ)+1 by positivity)
  have logbd := (lt_div_iff₀ (mul_pos ns sp)).mp hn
  have result : A n < (Real.log (M n)-((n:ℝ)+1)*(binaryEntropyNats p-binaryEntropyNats D))/
      (Real.sqrt ((n:ℝ)+1)*Real.log 2) := by
    apply (lt_div_iff₀ (mul_pos ns' hl)).2
    have cancel : A n*(Real.sqrt ((n:ℝ)+1)*Real.log 2)= b*scale p*Real.sqrt n + c := by
      dsimp only [A]
      field_simp [hl.ne',ns'.ne']
    rw [cancel]
    dsimp only [center] at logbd
    dsimp only [c]
    linarith only [logbd,mul_comm (Real.sqrt (n:ℝ)) (scale p),mul_assoc b (scale p) (Real.sqrt n)]
  apply result.trans_le
  rw [operationalRate,rateBits_low hp ph hd hD]
  change _ ≤ Real.sqrt ((n:ℝ)+1) * (Real.log (M n)/(((n:ℝ)+1)*Real.log 2)-_)
  have normalize (K S l x h : ℝ) (hs : 0<S) (hl' : 0<l) (e : S^2=K) :
      (x-K*h)/(S*l) = S*(x/(K*l)-h/l) := by
    subst K
    field_simp [hs.ne',hl'.ne']
  exact (normalize _ _ _ _ _ ns' hl pow).le

#print axioms low_distortion_converse
end BlockHierarchy.Converse