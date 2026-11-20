import BlockHierarchy.VarianceLimit.Redundancy

open Filter
open scoped BigOperators Topology
namespace BlockHierarchy.VarianceLimit
open Cut Varentropy

private noncomputable def mid (f : Bool → ℝ) := (f false+f true)/2
private noncomputable def gap (f : Bool → ℝ) := (f false-f true)/2
private noncomputable def size (k : ℝ) (f : Bool → ℝ) := |mid f|+k*|gap f|

private def update (p u : ℝ) (y : Bool) (f : Bool → ℝ) (x : Bool) :=
  Cut.step p x false*(if false=y then 1 else u)*f false +
  Cut.step p x true*(if true=y then 1 else u)*f true

private noncomputable def moment (p u : ℝ) (n : ℕ) (y : Bits n) (a : Bool) :=
  ∑ x : Bits n, tail p a n x*u^(hamming n x y)

private theorem moment_succ (p u : ℝ) (n : ℕ) (y : Bits (n+1)) :
    moment p u (n+1) y = update p u y.1 (moment p u n y.2) := by
  funext a
  change (∑ x : Bits (n+1), tail p a (n+1) x*u^hamming (n+1) x y) = _
  rw [sum_next]
  have row (b : Bool) : (∑ x : Bits n, tail p a (n+1) (b,x)*u^hamming (n+1) (b,x) y) =
      Cut.step p a b*(if b=y.1 then 1 else u)*moment p u n y.2 b := by
    unfold moment
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : b=y.1 <;> simp [tail,hamming,h,pow_add] <;> ring
  simp_rw [row]
  simp [update,add_comm]

/-- One site contracts a weighted sum of the midpoint and half-difference of the
two conditional Laplace transforms. The sign switches with the reproduction bit. -/
private theorem update_size {p u k : ℝ} (hr : 0≤1-2*p) (hu : 0≤u) (u1 : u≤1) (hk : 0≤k)
    (coef : (1-u)/2+k*(1-2*p)*((1+u)/2) ≤ k*((1+u)/2+k*(1-2*p)*((1-u)/2)))
    (y : Bool) (f : Bool → ℝ) :
    size k (update p u y f) ≤ ((1+u)/2+k*(1-2*p)*((1-u)/2))*size k f := by
  let α := (1+u)/2
  let δ := (1-u)/2
  let ρ := 1-2*p
  let t := if y then -δ else δ
  have a : 0≤α := by unfold α; linarith
  have d : 0≤δ := by unfold δ; linarith
  have ts : |t|=δ := by cases y <;> simp [t,abs_of_nonneg d]
  have m : mid (update p u y f) = α*mid f+t*gap f := by
    cases y <;> simp [α,δ,t,mid,gap,update,Cut.step] <;> ring
  have v : gap (update p u y f) = ρ*(t*mid f+α*gap f) := by
    cases y <;> simp [α,δ,t,ρ,mid,gap,update,Cut.step] <;> ring
  have mBound : |mid (update p u y f)| ≤ α*|mid f|+δ*|gap f| := by
    rw [m]
    simpa only [abs_mul,abs_of_nonneg a,ts] using abs_add_le (α*mid f) (t*gap f)
  have vBound : |gap (update p u y f)| ≤ ρ*(δ*|mid f|+α*|gap f|) := by
    rw [v,abs_mul,abs_of_nonneg hr]
    apply mul_le_mul_of_nonneg_left _ hr
    simpa only [abs_mul,abs_of_nonneg a,ts] using abs_add_le (t*mid f) (α*gap f)
  calc
    _ ≤ (α*|mid f|+δ*|gap f|)+k*(ρ*(δ*|mid f|+α*|gap f|)) :=
      add_le_add mBound (mul_le_mul_of_nonneg_left vBound hk)
    _ = (α+k*ρ*δ)*|mid f|+(δ+k*ρ*α)*|gap f| := by ring
    _ ≤ (α+k*ρ*δ)*|mid f|+(k*(α+k*ρ*δ))*|gap f| :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right coef (abs_nonneg _))
    _ = _ := by change _ = (α+k*ρ*δ)*(|mid f|+k*|gap f|); ring

/-- Every deterministic reproduction word obeys the same exponential moment
bound, for the stationary symmetric source and its physical Hamming distance. -/
theorem word_laplace_bound {p u k : ℝ} (hp : p≤1/2) (hu : 0≤u) (u1 : u≤1) (hk : 0≤k)
    (coef : (1-u)/2+k*(1-2*p)*((1+u)/2) ≤ k*((1+u)/2+k*(1-2*p)*((1-u)/2)))
    (n : ℕ) (y : Word n) :
    mean (mass p n) (fun x => u^(distance n x y)) ≤ ((1+u)/2+k*(1-2*p)*((1-u)/2))^(n+1) := by
  let c := (1+u)/2+k*(1-2*p)*((1-u)/2)
  have hr : 0≤1-2*p := by linarith
  have hc : 0≤c := add_nonneg (by positivity) (mul_nonneg (mul_nonneg hk hr) (by linarith))
  have iterate_bound (m : ℕ) (w : Bits m) : size k (moment p u m w) ≤ c^m := by
    induction m with
    | zero =>
      have eq : moment p u 0 w = fun _ => 1 := by
        funext a
        simp [moment,tail,hamming,show Fintype.card (Bits 0)=1 from rfl]
      simp [eq,size,mid,gap]
    | succ m ih =>
      rw [moment_succ,pow_succ']
      exact (update_size hr hu u1 hk coef w.1 _).trans (mul_le_mul_of_nonneg_left (ih w.2) hc)
  have pair (x : Word n) : tail p false (n+1) x + tail p true (n+1) x = 2*mass p n x := by
    change Cut.step p false x.1*tail p x.1 n x.2 + Cut.step p true x.1*tail p x.1 n x.2 = _
    unfold mass
    cases x.1 <;> simp [Cut.step] <;> ring
  have stationary : mean (mass p n) (fun x => u^(distance n x y)) = mid (moment p u (n+1) y) := by
    unfold mid moment mean
    apply (eq_div_iff (by norm_num : (2:ℝ)≠0)).mpr
    rw [Finset.sum_mul,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [←add_mul,pair]
    unfold distance
    ring
  rw [stationary]
  exact ((le_abs_self _).trans (le_add_of_nonneg_right (mul_nonneg hk (abs_nonneg _)))).trans (iterate_bound (n+1) y)

#print axioms word_laplace_bound

private theorem mean_score_lower {X : Type*} [Fintype X] {P q : X → ℝ} (hP : IsPrior P)
    (hq : IsPrior q) (τ : ℝ) (d : X → X → ℕ) {z : ℝ} (hz : 0<z)
    (avg : mean P (Z τ d q) ≤ z) : -Real.log z ≤ mean P (score τ d q) := by
  have row (x : X) : P x*(-Real.log z+1-Z τ d q x/z) ≤ P x*score τ d q x := by
    apply mul_le_mul_of_nonneg_left _ (hP.1 x)
    have h := Real.log_le_sub_one_of_pos (div_pos (Z_pos τ d hq x) hz)
    rw [Real.log_div (Z_pos τ d hq x).ne' hz.ne'] at h
    unfold score
    linarith
  have summed := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => row x)
  simp only [mul_sub,div_eq_mul_inv,←mul_assoc,Finset.sum_sub_distrib,←Finset.sum_mul,
    hP.2,one_mul] at summed
  have rel := (div_le_one hz).mpr avg
  rw [div_eq_mul_inv] at rel
  unfold mean at rel ⊢
  linarith only [summed,rel]

private theorem penalty_lower {p τ k : ℝ} (hp : 0<p) (ph : p<1/2) (hk : 0≤k)
    (hu : Real.exp (-τ) ≤ 1)
    (coef : let u := Real.exp (-τ)
            (1-u)/2+k*(1-2*p)*((1+u)/2) ≤ k*((1+u)/2+k*(1-2*p)*((1-u)/2)))
    (n : ℕ) :
    let u := Real.exp (-τ)
    let c := (1+u)/2+k*(1-2*p)*((1-u)/2)
    (-Real.log (c^(n+1)) ≤ totalCost p τ (n+1)) := by
  let u := Real.exp (-τ)
  let c := (1+u)/2+k*(1-2*p)*((1-u)/2)
  let q := canonicalPrior p τ n
  let P := mass p n
  let d := distance n
  have hc : 0<c := add_pos_of_pos_of_nonneg (by dsimp [u]; positivity)
    (mul_nonneg (mul_nonneg hk (by linarith)) (by change 0≤(1-Real.exp (-τ))/2; linarith))
  have hq : IsPrior q := (canonical_optimal p τ n).1
  have prob : IsPrior P := ⟨fun x => (mass_pos hp (by linarith) n x).le,mass_sum hp (by linarith) n⟩
  apply mean_score_lower prob hq τ d (pow_pos hc _)
  calc
    _ = ∑ y,q y*mean P (fun x => u^(d x y)) := by
      unfold mean Z
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro x _
      rw [mul_comm (-τ), Real.exp_nat_mul]
      dsimp [u]
      ring
    _ ≤ ∑ y,q y*c^(n+1) := Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left
      (word_laplace_bound ph.le (Real.exp_pos _).le hu hk coef n y) (hq.1 y)
    _ = _ := by rw [←Finset.sum_mul,hq.2,one_mul]

private theorem positive_parameters {p D : ℝ} (hp : 0<p) (ph : p<1/2) (hD : 0<D) (Dh : D<1/2) :
    ∃ τ k : ℝ, 0<τ ∧ 0≤k ∧
      let u := Real.exp (-τ)
      let c := (1+u)/2+k*(1-2*p)*((1-u)/2)
      u≤1 ∧ (1-u)/2+k*(1-2*p)*((1+u)/2) ≤ k*c ∧ 0<c ∧ c<Real.exp (-τ*D) := by
  let k := 1/2-D
  let ρ := 1-2*p
  let s := (1-k*ρ)/2
  have kp : 0<k := sub_pos.mpr Dh
  have rp : 0<ρ := by dsimp [ρ]; linarith
  have r1 : ρ<1 := by dsimp [ρ]; linarith
  have sD : D<s := by
    have pos := mul_pos kp (show 0<2-ρ by linarith)
    dsimp only [s]
    change 0 < (1/2-D)*(2-ρ) at pos
    dsimp only [k]
    nlinarith only [pos]
  let τ := min (k*(1-ρ)) ((s-D)/(2*D))
  have tp : 0<τ := lt_min (mul_pos kp (sub_pos.mpr r1)) (div_pos (sub_pos.mpr sD) (by positivity))
  let u := Real.exp (-τ)
  let α := (1+u)/2
  let δ := (1-u)/2
  let c := α+k*ρ*δ
  have up : 0<u := Real.exp_pos _
  have u1 : u≤1 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (show -τ≤0 by linarith)
  have db : δ ≤ τ/2 := by dsimp [δ,u]; linarith only [Real.add_one_le_exp (-τ)]
  have d0 : 0≤δ := by dsimp [δ]; linarith
  have a0 : 1/2≤α := by dsimp [α]; linarith
  have room : δ ≤ (k*(1-ρ))*α := calc
    _ ≤ τ/2 := db
    _ ≤ (k*(1-ρ))*(1/2) := by linarith only [show τ≤k*(1-ρ) from min_le_left ..]
    _ ≤ _ := mul_le_mul_of_nonneg_left a0 (mul_nonneg kp.le (sub_nonneg.mpr r1.le))
  have ac : α≤c := le_add_of_nonneg_right (mul_nonneg (mul_nonneg kp.le rp.le) d0)
  have coef : δ+k*ρ*α ≤ k*c := (show δ+k*ρ*α ≤ k*α by nlinarith only [room]).trans
    (mul_le_mul_of_nonneg_left ac kp.le)
  refine ⟨τ,k,tp,kp.le,u1,coef,lt_of_lt_of_le (by linarith : 0<α) ac,?_⟩
  have small := (le_div_iff₀ (by positivity : 0<2*D)).mp
    (show τ≤(s-D)/(2*D) from min_le_right ..)
  have gapD : D*(1+τ)<s := by nlinarith only [small,sD]
  have eu : u*(1+τ) ≤ 1 := calc
    _ ≤ u*Real.exp τ := mul_le_mul_of_nonneg_left (by linarith only [Real.add_one_le_exp τ]) up.le
    _ = _ := by dsimp [u]; rw [←Real.exp_add]; simp
  have den : 0<1+τ := by linarith
  have db' : τ/(1+τ) ≤ 1-u := (div_le_iff₀ den).mpr (by nlinarith only [eu])
  have strict : D*τ<s*(1-u) := calc
    _ = (D*(1+τ))*(τ/(1+τ)) := by field_simp
    _ < s*(τ/(1+τ)) := mul_lt_mul_of_pos_right gapD (div_pos tp den)
    _ ≤ _ := mul_le_mul_of_nonneg_left db' (hD.trans sD).le
  have cid : c=1-s*(1-u) := by dsimp [c,α,δ,s]; ring
  change c<Real.exp (-τ*D)
  rw [cid]
  linarith only [strict,Real.add_one_le_exp (-τ*D)]

/-- A positive per-symbol penalized value at every strictly interior distortion.
This supplies a positive limiting slope without a channel-level concentration estimate. -/
theorem exists_positive_objective {p D : ℝ} (hp : 0<p) (ph : p<1/2) (hD : 0<D) (Dh : D<1/2) :
    ∃ τ : ℝ, 0<τ ∧ 0 < commonCost p τ-τ*D := by
  obtain ⟨τ,k,tp,kp,hu,coef,hc,hgap⟩ := positive_parameters hp ph hD Dh
  let u := Real.exp (-τ)
  let c := (1+u)/2+k*(1-2*p)*((1-u)/2)
  have gap : Real.log c < -τ*D := by simpa using Real.log_lt_log hc hgap
  have finite (n : ℕ) : -Real.log c ≤ canonicalCost p n τ := by
    have h := penalty_lower hp ph kp hu coef n
    change -Real.log (c^(n+1)) ≤ totalCost p τ (n+1) at h
    rw [Real.log_pow,Nat.cast_succ] at h
    rw [canonicalCost_eq,le_div_iff₀ (by positivity)]
    linarith only [h]
  have lower := ge_of_tendsto' (cost_redundancy hp ph τ).1 finite
  exact ⟨τ,tp,by linarith only [gap,lower]⟩

#print axioms exists_positive_objective
end BlockHierarchy.VarianceLimit
