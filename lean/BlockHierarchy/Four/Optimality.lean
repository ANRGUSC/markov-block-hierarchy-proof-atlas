import FiniteChannel

open scoped BigOperators
namespace BlockHierarchy.Four

theorem logarithmic_tangent_bound : ∀ {ι : Type} [Fintype ι] (s z v : ι → ℝ), (∀ i, 0 ≤ s i) → (∀ i, 0 < z i) → (∀ i, 0 < v i) →
  (∑ i, s i/z i*(v i-z i)) ≤ 0 → (∑ i, s i*Real.log (v i)) ≤ ∑ i, s i*Real.log (z i) := by
  intro ι inst s z v hs hz hv bound
  have one (i : ι) : s i*Real.log (v i)-s i*Real.log (z i) ≤ s i/z i*(v i-z i) := by
    have h := Real.log_le_sub_one_of_pos (div_pos (hv i) (hz i))
    rw [Real.log_div (hv i).ne' (hz i).ne'] at h
    have hh := mul_le_mul_of_nonneg_left h (hs i)
    calc
      _ ≤ s i*(v i/z i-1) := by linarith only [hh]
      _ = _ := by field_simp [(hz i).ne']
                  <;> ring
  have total := (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => one i)).trans bound
  rw [Finset.sum_sub_distrib, sub_nonpos] at total
  exact total

theorem mass_transfer_bound : ∀ {ι : Type} [Fintype ι] (gain w v : ι → ℝ) (η : ℝ), (∀ i, 0 ≤ v i) →
  (∀ i, gain i ≤ η) → (∀ i, w i≠0 → gain i=η) → (∑ i, v i)=(∑ i, w i) →
  (∑ i, gain i*(v i-w i)) ≤ 0 := by
  intro ι _ gain w v η hv hle active mass
  have point (i : ι) : gain i*(v i-w i) ≤ η*(v i-w i) := by
    by_cases e : w i=0
    · simpa [e] using mul_le_mul_of_nonneg_right (hle i) (hv i)
    · rw [active i e]
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => point i)
  rwa [← Finset.mul_sum, Finset.sum_sub_distrib, mass,sub_self,mul_zero] at h

theorem empty_prefix_average : ∀ {ι : Type} [Fintype ι] [Nonempty ι] (s : ι → ℝ) (top c : ℝ),
  0 < c → (∀ i, s i ≤ top) → (∑ i, s i)/((Fintype.card ι : ℝ)*c) ≤ top/c := by
  intro ι _ _ s top c hc h
  have n : (0:ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have total : (∑ i, s i) ≤ (Fintype.card ι : ℝ)*top := by
    simpa using (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h i))
  apply (div_le_div_iff₀ (mul_pos n hc) hc).mpr
  nlinarith only [mul_le_mul_of_nonneg_right total hc.le]

end BlockHierarchy.Four
