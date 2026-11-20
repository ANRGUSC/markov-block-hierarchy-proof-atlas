import BlockHierarchy.Varentropy.Statement
import Mathlib.Analysis.SpecificLimits.Normed

open scoped BigOperators Topology
open Filter Asymptotics
namespace BlockHierarchy.Varentropy

private theorem persistence_small (m : BinaryModel) : |m.persistence| < 1 := by
  rw [abs_lt]
  unfold BinaryModel.persistence
  constructor <;> linarith [m.apos,m.bpos,m.alt,m.blt]

private theorem geom (r : ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, r^i)*(1-r)=1-r^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, pow_succ]; linarith only [ih]

private theorem weighted (r : ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range (n-1), ((n:ℝ)-(i:ℝ)-1)*r^i)*(1-r)^2 =
      (n:ℝ)*(1-r)-1+r^n := by
  have extend : (∑ i ∈ Finset.range (n-1), ((n:ℝ)-(i:ℝ)-1)*r^i) =
      ∑ i ∈ Finset.range n, ((n:ℝ)-(i:ℝ)-1)*r^i := by
    cases n with
    | zero => simp
    | succ k => simp [Finset.sum_range_succ]
  rw [extend]
  clear extend
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ, pow_succ]
    have step : (∑ i ∈ Finset.range n, (((n:ℝ)+1)-(i:ℝ)-1)*r^i) =
        (∑ i ∈ Finset.range n, ((n:ℝ)-(i:ℝ)-1)*r^i) + ∑ i ∈ Finset.range n, r^i := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [step]
    linear_combination ih + (1-r)*geom r n

noncomputable def remainderCoefficient (m : BinaryModel) :=
  2*gamma m/(1-m.persistence)^2-2*kappa m/(1-m.persistence)

theorem finite_expansion (m : BinaryModel) (n : ℕ) :
    finiteFormula m n = ((n:ℝ)+1)*limitingVariance m+correction m+
      remainderCoefficient m*m.persistence^n := by
  have hn : 1-m.persistence ≠ 0 := sub_ne_zero.mpr (abs_lt.mp (persistence_small m)).2.ne'
  have hg := geom m.persistence n
  have hw := weighted m.persistence n
  have eg := (eq_div_iff hn).2 hg
  have ew := (eq_div_iff (pow_ne_zero 2 hn)).2 hw
  unfold finiteFormula limitingVariance correction remainderCoefficient
  rw [eg,ew]
  field_simp [hn]
  ring

theorem normalized_expansion (m : BinaryModel) (n : ℕ) :
    finiteFormula m n/((n:ℝ)+1)=limitingVariance m+
      (correction m+remainderCoefficient m*m.persistence^n)*(1/((n:ℝ)+1)) := by
  rw [finite_expansion]
  field_simp
  ring

theorem finite_limit (m : BinaryModel) :
    Tendsto (fun n : ℕ => finiteFormula m n/((n:ℝ)+1)) atTop (𝓝 (limitingVariance m)) := by
  simp_rw [normalized_expansion]
  have hr := tendsto_pow_atTop_nhds_zero_of_abs_lt_one (persistence_small m)
  have h := (tendsto_const_nhds (x := limitingVariance m)).add
    (((tendsto_const_nhds (x := correction m)).add
      ((tendsto_const_nhds (x := remainderCoefficient m)).mul hr)).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  simpa using h

theorem finite_remainder (m : BinaryModel) :
    (fun n : ℕ => finiteFormula m n/((n:ℝ)+1)-limitingVariance m-correction m/((n:ℝ)+1))
      =O[atTop] (fun n : ℕ => |m.persistence|^n/((n:ℝ)+1)) := by
  apply isBigO_iff.2
  refine ⟨|remainderCoefficient m|, Filter.Eventually.of_forall fun n => ?_⟩
  have h : finiteFormula m n/((n:ℝ)+1)-limitingVariance m-correction m/((n:ℝ)+1) =
      remainderCoefficient m*(m.persistence^n/((n:ℝ)+1)) := by
    rw [normalized_expansion]
    ring
  rw [h]
  simp [Real.norm_eq_abs, abs_mul, abs_div, abs_pow]

#print axioms finite_expansion
#print axioms finite_limit
#print axioms finite_remainder
end BlockHierarchy.Varentropy