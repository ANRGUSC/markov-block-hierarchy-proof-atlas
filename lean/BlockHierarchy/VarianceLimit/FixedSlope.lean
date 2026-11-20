import BlockHierarchy.VarianceLimit.FiniteDual
import BlockHierarchy.VarianceLimit.Common
import Mathlib.Analysis.Calculus.Deriv.Slope

open Filter Topology
namespace BlockHierarchy.VarianceLimit
open Cut

theorem rate_convergence {p D : ℝ} (hp : 0<p) (ph : p<1/2) (hD : 0<D) :
    Tendsto (fun n => constrainedRate p n D) atTop (𝓝 (rateBits p D)) := by
  let E := (fun t => commonCost p t-t*D) '' Set.Ici (0:ℝ)
  let F := sSup E
  have ne : E.Nonempty := ⟨_,0,show (0:ℝ)≤0 by norm_num,rfl⟩
  have upper (n : ℕ) : constrainedRate p n D*Real.log 2 ∈ upperBounds E := by
    rintro z ⟨t,ht,rfl⟩
    have finite := (finite_duality hp ph hD n).1 t ht
    have lo := ((cost_redundancy hp ph t).2 n).1
    linarith
  have bdd : BddAbove E := ⟨_,upper 0⟩
  have lower (n : ℕ) : F ≤ constrainedRate p n D*Real.log 2 := csSup_le ne (upper n)
  have high (n : ℕ) : constrainedRate p n D*Real.log 2 ≤ F+boundaryInformation p/((n:ℝ)+1) := by
    obtain ⟨t,ht⟩ := (finite_duality hp ph hD n).2.1
    rw [(finite_duality hp ph hD n).2.2 t ht]
    have up := ((cost_redundancy hp ph t).2 n).2
    have mem : commonCost p t-t*D∈E := ⟨t,ht.1,rfl⟩
    have htF : commonCost p t-t*D≤F := le_csSup bdd mem
    linarith
  have terr : Tendsto (fun n : ℕ => boundaryInformation p/((n:ℝ)+1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x:=boundaryInformation p)).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
  have T : Tendsto (fun n => constrainedRate p n D*Real.log 2) atTop (𝓝 F) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa using (tendsto_const_nhds (x:=F)).add terr) lower high
  have L := T.div (tendsto_const_nhds (x:=Real.log 2)) (Real.log_pos (by norm_num : (1:ℝ)<2)).ne'
  have final : Tendsto (fun n => constrainedRate p n D) atTop (𝓝 (F/Real.log 2)) := by
    simpa [Pi.div_def,(Real.log_pos (by norm_num : (1:ℝ)<2)).ne'] using L
  rw [rateBits,final.limUnder_eq]
  exact final

private theorem subgradient_limit (f : ℕ → ℝ → ℝ) (v : ℝ → ℝ) (s : ℕ → ℝ)
    {D r : ℝ} (hD : 0<D) (der : HasDerivAt v r D)
    (conv : ∀ y, 0<y → Tendsto (fun n => f n y) atTop (𝓝 (v y)))
    (support : ∀ n y, 0<y → f n D+(y-D)*s n ≤ f n y) :
    Tendsto s atTop (𝓝 r) := by
  have slopes (y : ℝ) (hy : 0<y) :
      Tendsto (fun n => slope (f n) D y) atTop (𝓝 (slope v D y)) := by
    simp only [slope_def_field]
    exact ((conv y hy).sub (conv D hD)).div_const _
  obtain ⟨left,right⟩ := hasDerivAt_iff_tendsto_slope_left_right.mp der
  apply tendsto_order.2
  constructor
  · intro a ha
    have pos : ∀ᶠ y in 𝓝[<] D, 0<y := (lt_mem_nhds hD).filter_mono nhdsWithin_le_nhds
    obtain ⟨y,hay,hy,hyD⟩ := ((left.eventually (lt_mem_nhds ha)).and (pos.and self_mem_nhdsWithin)).exists
    have hyD' : y<D := hyD
    filter_upwards [(slopes y hy).eventually (lt_mem_nhds hay)] with n hn
    apply hn.trans_le
    rw [slope_def_field,div_le_iff_of_neg (sub_neg.mpr hyD')]
    linarith only [support n y hy,mul_comm (s n) (y-D)]
  · intro b hb
    have pos : ∀ᶠ y in 𝓝[>] D, 0<y := (lt_mem_nhds hD).filter_mono nhdsWithin_le_nhds
    obtain ⟨y,hyb,hy,hyD⟩ := ((right.eventually_lt_const hb).and (pos.and self_mem_nhdsWithin)).exists
    have hyD' : D<y := hyD
    filter_upwards [(slopes y hy).eventually_lt_const hyb] with n hn
    apply lt_of_le_of_lt _ hn
    rw [slope_def_field,le_div_iff₀ (sub_pos.mpr hyD')]
    linarith only [support n y hy,mul_comm (s n) (y-D)]

theorem maximizingSlope_convergence {p D r : ℝ} (hp : 0<p) (ph : p<1/2)
    (hD : 0<D) (der : HasDerivAt (rateBits p) r D)
    (T : ℕ → ℝ) (hT : ∀ n, MaximizingSlope p D n (T n)) :
    Tendsto T atTop (𝓝 (-(Real.log 2)*r)) := by
  let f (n : ℕ) (y : ℝ) := constrainedRate p n y*Real.log 2
  let v (y : ℝ) := rateBits p y*Real.log 2
  have z := subgradient_limit f v (fun n => -T n) hD (der.mul_const (Real.log 2))
    (fun y hy => (rate_convergence hp ph hy).mul_const _) (by
      intro n y hy
      have h := (finite_duality hp ph hy n).1 (T n) (hT n).1
      have e := (finite_duality hp ph hD n).2.2 _ (hT n)
      dsimp only [f]
      linarith only [h,e])
  simpa [mul_comm] using z.neg

theorem moving_variance {p D r : ℝ} (hp : 0<p) (ph : p<1/2)
    (hD : 0<D) (der : HasDerivAt (rateBits p) r D)
    (T : ℕ → ℝ) (q : (n : ℕ) → Word n → ℝ)
    (ht : ∀ n, MaximizingSlope p D n (T n))
    (hq : ∀ n, Optimal (mass p n) (T n) (distance n) (q n)) :
    Tendsto (fun n => (omegaAt p (T n) n (q n))^2/(Real.log 2)^2)
      atTop (𝓝 ((commonOmega p (-(Real.log 2)*r))^2/(Real.log 2)^2)) := by
  let t := -(Real.log 2)*r
  have hT : Tendsto T atTop (𝓝 t) := maximizingSlope_convergence hp ph hD der T ht
  have ht0 : 0≤t := ge_of_tendsto' hT (fun n => (ht n).1)
  have hω : Tendsto (fun n => commonOmega p (T n)) atTop (𝓝 (commonOmega p t)) :=
    ((commonOmega_continuous hp ph).continuousWithinAt ht0).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hT,Eventually.of_forall (fun n => (ht n).1)⟩)
  let b (n : ℕ) := (1+Real.sqrt 2)*Real.sqrt ((1-2*p)/((n:ℝ)+1))
  have hb : Tendsto b atTop (𝓝 0) := by
    have z := ((tendsto_const_nhds (x:=1-2*p)).mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))).sqrt
    simpa [b,div_eq_mul_inv] using (tendsto_const_nhds (x:=1+Real.sqrt 2)).mul z
  let d (n : ℕ) := omegaAt p (T n) n (q n)-commonOmega p (T n)
  have E (n : ℕ) : -b n≤d n ∧ d n≤b n := abs_le.mp (omegaAt_enclosure hp ph (ht n).1 n (hq n))
  have hd : Tendsto d atTop (𝓝 0) := tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa using hb.neg) hb (fun n => (E n).1) (fun n => (E n).2)
  have whole : Tendsto (fun n => omegaAt p (T n) n (q n)) atTop (𝓝 (commonOmega p t)) := by
    simpa [d] using hd.add hω
  exact (whole.pow 2).div_const _

#print axioms moving_variance
#print axioms rate_convergence
#print axioms maximizingSlope_convergence
end BlockHierarchy.VarianceLimit