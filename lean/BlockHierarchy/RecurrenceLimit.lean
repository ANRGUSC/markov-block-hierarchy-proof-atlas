import BlockHierarchy.RecurrenceCrossing

open Filter Topology

namespace BlockHierarchy.Recurrence

noncomputable def smallerRoot (ρ z : ℝ) :=
  (z*(1+ρ)-Real.sqrt ((z*(1+ρ))^2-4*ρ))/2

theorem orbit_feasible_limit {ρ z : ℝ} (hr : 0<ρ) (hr1 : ρ<1) (hz : 0<z) (hz1 : z<1)
    (threshold : 2*Real.sqrt ρ/(1+ρ) ≤ z) :
    (∀ n, orbit ρ z n < z) ∧ StrictMono (orbit ρ z) ∧
      Tendsto (orbit ρ z) atTop (𝓝 (smallerRoot ρ z)) := by
  let a := z*(1+ρ)
  let d := Real.sqrt (a^2-4*ρ)
  let r := (a-d)/2
  have ha : 0<a := mul_pos hz (by linarith)
  have bound : 2*Real.sqrt ρ ≤ a := (div_le_iff₀ (by linarith)).mp threshold
  have disc : 0 ≤ a^2-4*ρ := by
    nlinarith only [Real.sq_sqrt hr.le, mul_nonneg (sub_nonneg.mpr bound)
      (show 0 ≤ a+2*Real.sqrt ρ by positivity)]
  have ds : d^2 = a^2-4*ρ := Real.sq_sqrt disc
  have dp : 0 ≤ d := Real.sqrt_nonneg _
  have rp : 0 < r := by
    dsimp [r]; by_contra! h
    nlinarith only [ds,hr,mul_nonneg (show 0≤d-a by linarith) (show 0≤d+a by positivity)]
  have rz : r < z := by
    dsimp [r,a] at *
    nlinarith only [dp,mul_pos hz (sub_pos.mpr hr1)]
  have poly : r^2-z*(1+ρ)*r+ρ=0 := by
    change r^2-a*r+ρ=0; dsimp [r]; nlinarith only [ds]
  have fix : r = nextMoment ρ z r := (fixed_point_equation ρ z r rz).2 poly
  have zeroStep : 0 < orbit ρ z 1 := by
    simpa [orbit,nextMoment,div_eq_mul_inv] using div_pos hr hz
  have safe (n : ℕ) : 0≤orbit ρ z n ∧ orbit ρ z n<r := by
    induction n with
    | zero => exact ⟨le_rfl,rp⟩
    | succ n ih =>
      have up := recurrence_strict ρ z _ r hr hz hz1 ih.1 ih.2 rz
      have den := sub_pos.mpr (ih.2.trans rz)
      have num : 0 < 1-z*orbit ρ z n := by
        nlinarith only [mul_pos hz den,mul_pos (sub_pos.mpr hz1) (show 0<1+z by linarith)]
      exact ⟨(mul_pos hr (div_pos num den)).le,lt_of_lt_of_eq up fix.symm⟩
  have mono : StrictMono (orbit ρ z) := by
    apply strictMono_nat_of_lt_succ
    intro n; induction n with
    | zero => exact zeroStep
    | succ n ih => exact recurrence_strict ρ z _ _ hr hz hz1 (safe n).1 ih ((safe (n+1)).2.trans rz)
  refine ⟨fun n => (safe n).2.trans rz,mono,?_⟩
  let l := ⨆ n, orbit ρ z n
  have lb : l ≤ r := ciSup_le (fun n => (safe n).2.le)
  have lim : Tendsto (orbit ρ z) atTop (𝓝 l) :=
    tendsto_atTop_ciSup mono.monotone ⟨r,fun _ ⟨n,hn⟩ => hn ▸ (safe n).2.le⟩
  have cont : ContinuousAt (nextMoment ρ z) l := by
    unfold nextMoment
    fun_prop (disch := exact (sub_pos.mpr (lb.trans_lt rz)).ne')
  have shift : Tendsto (fun n => orbit ρ z (n+1)) atTop (𝓝 l) :=
    lim.comp (tendsto_add_atTop_nat 1)
  have lf : l = nextMoment ρ z l := tendsto_nhds_unique shift (cont.tendsto.comp lim)
  have lp := (fixed_point_equation ρ z l (lb.trans_lt rz)).1 lf
  have lr : l = r := by
    apply le_antisymm lb
    by_contra! h
    have pos : 0 < (r-l)*(a-r-l) := mul_pos (sub_pos.mpr h) (by dsimp [r] at *; linarith only [h,dp])
    change l^2-a*l+ρ=0 at lp
    change r^2-a*r+ρ=0 at poly
    nlinarith only [pos,lp,poly]
  change Tendsto (orbit ρ z) atTop (𝓝 r)
  rwa [← lr]

theorem orbit_below_iff {ρ z : ℝ} (hr : 0<ρ) (hr1 : ρ<1) (hz : 0<z) (hz1 : z<1) :
    (∀ n, orbit ρ z n<z) ↔ 2*Real.sqrt ρ/(1+ρ)≤z := by
  refine ⟨?_,fun h => (orbit_feasible_limit hr hr1 hz hz1 h).1⟩
  intro h; by_contra! below
  have b := (lt_div_iff₀ (show 0<1+ρ by linarith)).mp below
  have g : 0 < 4*ρ-(z*(1+ρ))^2 := by
    nlinarith only [Real.sq_sqrt hr.le,mul_pos (sub_pos.mpr b)
      (show 0 < 2*Real.sqrt ρ+z*(1+ρ) by positivity)]
  obtain ⟨n,hn⟩ := finite_crossing hz g
  exact (h n).not_ge hn

#print axioms orbit_feasible_limit
#print axioms orbit_below_iff
end BlockHierarchy.Recurrence
