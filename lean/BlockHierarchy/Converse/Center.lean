import BlockHierarchy.Converse.Paths
import BlockHierarchy.Converse.Normalized
import BlockHierarchy.Converse.Statement
import BlockHierarchy.Converse.Ball

open scoped BigOperators
namespace BlockHierarchy.Converse
open Cut Varentropy

noncomputable def scale (p : ℝ) := Real.sqrt (p*(1-p))*Real.log ((1-p)/p)
noncomputable def center (p D : ℝ) (n : ℕ) :=
  ((n:ℝ)+1)*(binaryEntropyNats p-binaryEntropyNats D)+Real.log 2-binaryEntropyNats p

theorem scale_pos {p : ℝ} (hp : 0<p) (ph : p<1/2) : 0<scale p :=
  mul_pos (Real.sqrt_pos.2 (mul_pos hp (by linarith)))
    (Real.log_pos ((lt_div_iff₀ hp).mpr (by linarith)))

theorem centered_score {p : ℝ} (hp : 0<p) (ph : p<1/2) (D : ℝ) {n : ℕ} (hn : 0<n)
    (a : Bool) (v : Bits n) :
    -Real.log (mass p n (a,flipEquiv a n v))-((n:ℝ)+1)*binaryEntropyNats D =
      center p D n + Real.sqrt n * scale p * normalizedFlips p n v := by
  have h1 : p<1 := by linarith
  have hN : 0<Real.sqrt (n:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hS : 0<Real.sqrt (p*(1-p)) := Real.sqrt_pos.2 (mul_pos hp (by linarith))
  rw [path_information hp h1]
  unfold center scale normalizedFlips
  rw [Real.log_div (sub_pos.mpr h1).ne' hp.ne']
  unfold binaryEntropyNats
  field_simp [hN.ne',hS.ne']
  <;> ring

private theorem mean_flip_indicator (p : ℝ) (n : ℕ) (F : Word n → Prop) [DecidablePred F]
    (S : Bits n → Prop) [DecidablePred S] (incl : ∀ a v, S v → F (a,flipEquiv a n v))
    (hp : 0<p) (ph : p<1/2) :
    (∑ v : Bits n, if S v then iidFlips p n v else 0) ≤
      ∑ x : Word n, if F x then mass p n x else 0 := by
  classical
  have h1 : p<1 := by linarith
  have row (a : Bool) : (1/2:ℝ)*(∑ v, if S v then iidFlips p n v else 0) ≤
      ∑ x : Bits n, if F (a,x) then mass p n (a,x) else 0 := by
    rw [Finset.mul_sum,← (flipEquiv a n).sum_comp (fun x => if F (a,x) then mass p n (a,x) else 0)]
    apply Finset.sum_le_sum
    intro v _
    by_cases hs : S v
    · rw [if_pos hs,if_pos (incl a v hs),path_from_flips]
    · rw [if_neg hs,mul_zero]
      split_ifs
      · exact (mass_pos hp h1 n _).le
      · rfl
  rw [sum_next,Fintype.sum_bool]
  let s := ∑ v : Bits n, if S v then iidFlips p n v else 0
  calc
    _ = (1/2:ℝ)*s + (1/2:ℝ)*s := by change s = _; ring
    _ ≤ _ := add_le_add (row true) (row false)
  apply le_of_eq
  congr 1 <;> apply Finset.sum_congr rfl <;> intro y _ <;> split_ifs <;> rfl

/-- The finite coding inequality in precisely the normalized flip coordinates
used by the central limit theorem. -/
theorem code_tail_bound {p D ε : ℝ} (hp : 0<p) (ph : p<1/2) (hd : 0<D) (dh : D<1/2)
    {n : ℕ} (hn : 0<n) {M : ℕ} (hm : M ∈ feasibleSizes p D ε n) (γ : ℝ) :
    (∑ v : Bits n, if (Real.log M-center p D n)/(Real.sqrt n*scale p)+
      γ/(Real.sqrt n*scale p)<normalizedFlips p n v then iidFlips p n v else 0) ≤ ε+Real.exp (-γ) := by
  obtain ⟨hm,enc,dec,err⟩ := hm
  have den : 0<Real.sqrt (n:ℝ)*scale p :=
    mul_pos (Real.sqrt_pos.2 (by exact_mod_cast hn)) (scale_pos hp ph)
  have cv := shifted_code_converse hp (by linarith) hd dh n γ hm enc dec
  have incl (a : Bool) (v : Bits n)
      (h : (Real.log M-center p D n)/(Real.sqrt n*scale p)+γ/(Real.sqrt n*scale p)<normalizedFlips p n v) :
      Real.log M+γ ≤ -Real.log (mass p n (a,flipEquiv a n v))-((n:ℝ)+1)*binaryEntropyNats D := by
    rw [centered_score hp ph D hn]
    rw [← add_div,div_lt_iff₀ den] at h
    linarith
  have cmp := mean_flip_indicator p n
    (fun x => Real.log M+γ ≤ -Real.log (mass p n x)-((n:ℝ)+1)*binaryEntropyNats D)
    (fun v => (Real.log M-center p D n)/(Real.sqrt n*scale p)+
      γ/(Real.sqrt n*scale p)<normalizedFlips p n v) incl hp ph
  linarith

#print axioms code_tail_bound

end BlockHierarchy.Converse
