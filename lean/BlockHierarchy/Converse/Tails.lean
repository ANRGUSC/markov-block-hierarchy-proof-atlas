import BlockHierarchy.Converse.Cylinders
import BlockHierarchy.Converse.Normalized
import BlockHierarchy.Converse.Statement
import Mathlib.MeasureTheory.Measure.Portmanteau

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators
namespace BlockHierarchy.Converse
open Varentropy

private theorem scaled_sum (p : ℝ) (n i : ℕ) (w : ℕ → Bool) :
    (∑ j ∈ Finset.range n, scaledFlip p (w (i+j))) =
      (((flipCount n (prefixAt w i n):ℝ)-(n:ℝ)*p)/Real.sqrt (p*(1-p))) := by
  induction n generalizing i with
  | zero => simp [flipCount]
  | succ n ih =>
    rw [Finset.sum_range_succ']
    have shifted : (∑ j ∈ Finset.range n, scaledFlip p (w (i+(j+1)))) =
        ∑ j ∈ Finset.range n, scaledFlip p (w ((i+1)+j)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [show i+(j+1)=(i+1)+j by omega]
    rw [shifted,ih]
    simp only [prefixAt,flipCount,scaledFlip,Nat.cast_succ,Nat.cast_add,Nat.add_zero]
    by_cases hb : w i = true <;> simp [hb] <;> ring

private theorem finite_event (p : Set.Icc (0:ℝ) 1) (n : ℕ)
    (S : Bits n → Prop) [DecidablePred S] :
    (flipsLaw p).real {w | S (prefixAt w 0 n)} =
      ∑ x : Bits n, if S x then iidFlips p n x else 0 := by
  classical
  let f (x : Bits n) : Set (ℕ → Bool) := if S x then {w | prefixAt w 0 n=x} else ∅
  have union_eq : (⋃ x, f x)={w | S (prefixAt w 0 n)} := by
    ext w
    simp only [Set.mem_iUnion,Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x,hx⟩
      dsimp [f] at hx
      split at hx
      · rename_i hs
        exact hx ▸ hs
      · exact False.elim hx
    · intro hs
      exact ⟨prefixAt w 0 n,by simp [f,hs]⟩
  have disj : Pairwise (fun x y => Disjoint (f x) (f y)) := by
    intro x y xy
    by_cases sx : S x <;> by_cases sy : S y <;> simp [f,sx,sy,Set.disjoint_left]
    intro w h h'
    exact xy (h.symm.trans h')
  have meas (x : Bits n) : MeasurableSet (f x) := by
    by_cases hx : S x
    · simp only [f,if_pos hx,prefix_event]
      exact MeasurableSet.pi (Finset.countable_toSet _) (fun _ _ => measurableSet_singleton _)
    · simp [f,hx]
  rw [← union_eq,measureReal_iUnion_fintype disj meas]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : S x <;> simp [f,hx,cylinder_probability]

/-- Ordinary upper-tail convergence for the finite Markov flip coordinates. -/
theorem normalized_flip_tails (p : Set.Icc (0:ℝ) 1) (hp : 0<(p:ℝ)) (h1 : (p:ℝ)<1) (a : ℝ) :
    Tendsto (fun n : ℕ => ∑ x : Bits n, if a<normalizedFlips p n x then iidFlips p n x else 0)
      atTop (𝓝 (gaussianTail a)) := by
  let F (n : ℕ) (w : ℕ → Bool) := (Real.sqrt n)⁻¹ * ∑ k ∈ Finset.range n, scaledFlip p (w k)
  have h := flips_clt p hp h1
  have boundary : ((gaussianReal 0 1).map (id : ℝ → ℝ)) (frontier (Set.Ioi a)) = 0 := by
    let _ : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
    simp
  have conv := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h.tendsto boundary
  have finite : ((gaussianReal 0 1).map (id : ℝ → ℝ)) (Set.Ioi a) ≠ ⊤ := by
    rw [Measure.map_id]
    exact measure_ne_top _ _
  have re := (ENNReal.tendsto_toReal finite).comp conv
  have eq (n : ℕ) (w : ℕ → Bool) : F n w=normalizedFlips p n (prefixAt w 0 n) := by
    unfold F normalizedFlips
    simpa using congrArg (fun v : ℝ => (Real.sqrt n)⁻¹*v) (scaled_sum p n 0 w)
  have prob (n : ℕ) : ((flipsLaw p).map (F n)).real (Set.Ioi a) =
      ∑ x : Bits n, if a<normalizedFlips p n x then iidFlips p n x else 0 := by
    rw [map_measureReal_apply_of_aemeasurable (h.forall_aemeasurable n) measurableSet_Ioi]
    change (flipsLaw p).real {w | a<F n w}=_
    simp_rw [eq]
    exact finite_event p n (fun x => a<normalizedFlips p n x)
  change Tendsto (fun n : ℕ => ((flipsLaw p).map (F n)).real (Set.Ioi a)) atTop
    (𝓝 (((gaussianReal 0 1).map (id : ℝ → ℝ)).real (Set.Ioi a))) at re
  simpa only [prob,Measure.map_id,gaussianTail] using re

#print axioms normalized_flip_tails
end BlockHierarchy.Converse
