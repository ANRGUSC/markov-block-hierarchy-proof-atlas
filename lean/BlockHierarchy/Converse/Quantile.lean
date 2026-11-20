import BlockHierarchy.Converse.Finite

open Filter Topology
namespace BlockHierarchy.Converse

/-- If the limiting tail strictly exceeds the allowed error to the left of q,
every code sequence satisfying the finite converse has lower limit at least q.
The eventual formulation includes diverging sequences of code sizes. -/
theorem quantile_lower {ε q : ℝ} (rate overhead rem : ℕ → ℝ) (tail : ℕ → ℝ → ℝ)
    (Q : ℝ → ℝ) (mono : ∀ n, Antitone (tail n))
    (below : ∀ a<q, ε<Q a) (clt : ∀ a<q, Tendsto (fun n => tail n a) atTop (𝓝 (Q a)))
    (hOver : Tendsto overhead atTop (𝓝 0)) (hRem : Tendsto rem atTop (𝓝 0))
    (finite : ∀ᶠ n in atTop, tail n (rate n+overhead n) ≤ ε+rem n) :
    ∀ a<q, ∀ᶠ n in atTop, a<rate n := by
  intro a ha
  let b := (a+q)/2
  have ab : a<b := by dsimp [b]; linarith
  have bq : b<q := by dsimp [b]; linarith
  have small := hOver.eventually (gt_mem_nhds (sub_pos.mpr ab))
  have right : Tendsto (fun n => ε+rem n) atTop (𝓝 ε) := by
    simpa using tendsto_const_nhds.add hRem
  have gap := Filter.Tendsto.eventually_lt right (clt b bq) (below b bq)
  filter_upwards [small,gap,finite] with n hn hg hf
  by_contra! r
  have step : rate n + overhead n ≤ b := by linarith
  linarith [mono n step]

#print axioms quantile_lower
end BlockHierarchy.Converse
