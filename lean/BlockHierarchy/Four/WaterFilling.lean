import FiniteChannel
import Mathlib.Tactic.FinCases

open scoped BigOperators
noncomputable section
namespace BlockHierarchy.Four.WaterFilling

def pref (s : ℕ → ℝ) (n : ℕ) := ∑ i ∈ Finset.range n, s i
def ratio (s : ℕ → ℝ) (m c : ℝ) (j : ℕ) := pref s j/(m+(j:ℝ)*c)
def clipped (s : ℕ → ℝ) (r c : ℝ) (i : ℕ) := max 0 (s i/r-c)
def value (s w : ℕ → ℝ) (n : ℕ) (a c : ℝ) := ∑ i ∈ Finset.range n, s i*Real.log (a*(c+w i))

theorem maximal_prefix_bounds (s : ℕ → ℝ) (n k : ℕ) (m c : ℝ) (hm : 0 < m) (hc : 0 < c)
(hk : 1 ≤ k) (hkn : k ≤ n) (hs : ∀ i<n, 0 < s i)
(hsort : ∀ i j, i ≤ j → j<n → s j ≤ s i)
(hbest : ∀ j, 1 ≤ j → j ≤ n → ratio s m c j ≤ ratio s m c k) : (∀ i<k, c*ratio s m c k ≤ s i) ∧ (∀ i, k ≤ i → i<n → s i ≤ c*ratio s m c k) := by
  let r := ratio s m c k
  have den (j : ℕ) : 0 < m+(j:ℝ)*c := by positivity
  have eq : r*(m+(k:ℝ)*c)=pref s k := div_mul_cancel₀ _ (den k).ne'
  have rp : 0 ≤ r := by
    apply div_nonneg _ (den k).le
    exact Finset.sum_nonneg (fun i hi => (hs i (lt_of_lt_of_le (Finset.mem_range.mp hi) hkn)).le)
  have upper (j : ℕ) (hj : j ≤ n) : pref s j ≤ r*(m+(j:ℝ)*c) := by
    by_cases zero : j=0
    · subst j; simpa [pref] using mul_nonneg rp hm.le
    · exact (div_le_iff₀ (den j)).mp (hbest j (by omega) hj)
  have recur (j : ℕ) : pref s (j+1)=pref s j+s j := Finset.sum_range_succ _ _
  constructor
  · intro i hi
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
    have before := upper j (by omega)
    rw [recur] at eq
    push_cast at eq
    exact le_trans (by nlinarith only [before,eq] : c*r ≤ s j) (hsort i j (by omega) (by omega))
  · intro i hki hin
    have after := upper (k+1) (by omega)
    rw [recur] at after
    push_cast at after
    exact (hsort k i hki hin).trans (by nlinarith only [after,eq])

theorem clipped_mass_determines_prefix (s : ℕ → ℝ) (n : ℕ) (m c r : ℝ) (hn : 0 < n)
(hm : 0 < m) (hc : 0 < c) (hr : 0 < r) (hs : ∀ i<n, 0 < s i)
(hsort : ∀ i j, i ≤ j → j<n → s j ≤ s i)
(hmass : (∑ i ∈ Finset.range n, clipped s r c i)=m) : (∀ j, 1 ≤ j → j ≤ n → ratio s m c j ≤ r) ∧
 ∃ k, 1 ≤ k ∧ k ≤ n ∧ ratio s m c k=r ∧
   (∀ i<n, 0 < clipped s r c i ↔ i<k) := by
  have allPrefixes : ∀ j, 1 ≤ j → j ≤ n → ratio s m c j ≤ r := by
    intro j hj hjn
    have leSum : (∑ i ∈ Finset.range j, clipped s r c i) ≤ m := by
      rw [← hmass]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hjn) (fun i _ _ => le_max_left _ _)
    have bound (i : ℕ) : s i ≤ (clipped s r c i+c)*r := by
      apply (div_le_iff₀ hr).mp
      have := le_max_right 0 (s i/r-c)
      unfold clipped; linarith
    have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range j) => bound i)
    rw [← Finset.sum_mul,Finset.sum_add_distrib] at h
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at h
    apply (div_le_iff₀ (by positivity : 0 < m+(j:ℝ)*c)).mpr
    unfold pref
    nlinarith only [h,mul_le_mul_of_nonneg_right leSum hr.le]
  have cutIndex : ∃ k, 1 ≤ k ∧ k ≤ n ∧ (∀ i<n, 0 < clipped s r c i ↔ i<k) := by
    classical
    let active := (Finset.range n).filter (fun i => 0 < clipped s r c i)
    have nonempty : active.Nonempty := by
      by_contra h
      have zero : (∑ i ∈ Finset.range n, clipped s r c i)=0 := by
        apply Finset.sum_eq_zero
        intro i hi
        apply le_antisymm _ (le_max_left _ _)
        apply le_of_not_gt
        intro pos
        exact h ⟨i,Finset.mem_filter.mpr ⟨hi,pos⟩⟩
      linarith
    let a := active.max' nonempty
    have top : a ∈ active := Finset.max'_mem _ _
    obtain ⟨amem,apos⟩ := Finset.mem_filter.mp top
    have an := Finset.mem_range.mp amem
    refine ⟨a+1,by omega,by omega,?_⟩
    intro i hi
    constructor
    · intro ip
      have imem : i ∈ active := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,ip⟩
      exact Nat.lt_succ_of_le (Finset.le_max' _ _ imem)
    · intro h
      have mono := div_le_div_of_nonneg_right (hsort i a (by omega) an) hr.le
      exact apos.trans_le (max_le_max_left _ (sub_le_sub_right mono _))
  obtain ⟨k,hk,hkn,cut⟩ := cutIndex
  refine ⟨allPrefixes,k,hk,hkn,?_,cut⟩
  have massK : (∑ i ∈ Finset.range k, clipped s r c i)=m := by
    rw [← hmass]
    apply Finset.sum_subset (Finset.range_mono hkn)
    intro i hi outside
    apply le_antisymm _ (le_max_left _ _)
    exact le_of_not_gt (fun pos => outside (Finset.mem_range.mpr ((cut i (Finset.mem_range.mp hi)).mp pos)))
  have bound (i : ℕ) (hi : i ∈ Finset.range k) : s i=(clipped s r c i+c)*r := by
    have hik := Finset.mem_range.mp hi
    have pos := (cut i (hik.trans_le hkn)).mpr hik
    have p : 0 < s i/r-c := by
      by_contra! e; simp [clipped,max_eq_left e] at pos
    rw [clipped,max_eq_right p.le,sub_add_cancel,div_mul_cancel₀ _ hr.ne']
  have eq := Finset.sum_congr rfl bound
  rw [← Finset.sum_mul,Finset.sum_add_distrib,massK] at eq
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at eq
  apply (div_eq_iff (show 0 < m+(k:ℝ)*c by positivity).ne').mpr
  exact eq.trans (mul_comm _ _)

theorem four_class_allocation (s : ℕ → ℝ) (k : ℕ) (m c : ℝ) (hm : 0 < m) (hc : 0 < c)
(hk : 1 ≤ k) (hkn : k ≤ 4) (hs : ∀ i<4, 0 < s i)
(hsort : ∀ i j, i ≤ j → j<4 → s j ≤ s i)
(hbest : ∀ j, 1 ≤ j → j ≤ 4 → ratio s m c j ≤ ratio s m c k) (a : ℝ) (ha : 0 < a) : (∑ i ∈ Finset.range 4, clipped s (ratio s m c k) c i)=m ∧
 ∀ v : ℕ → ℝ, (∀ i<4, 0 ≤ v i) → (∑ i ∈ Finset.range 4, v i)=m →
   value s v 4 a c ≤ value s (clipped s (ratio s m c k) c) 4 a c := by
  have candidateMass : (∑ i ∈ Finset.range 4, clipped s (ratio s m c k) c i)=m := by
    let r := ratio s m c k
    have rp : 0 < r := by
      have one : 0 < ratio s m c 1 := by simpa [ratio,pref] using div_pos (hs 0 (by decide)) (add_pos hm hc)
      exact one.trans_le (hbest 1 (by decide) (by decide))
    let w := clipped s r c
    obtain ⟨inc,exc⟩ := maximal_prefix_bounds s 4 k m c hm hc hk hkn hs hsort hbest
    have on (i) (hi : i<k) : w i=s i/r-c := max_eq_right (sub_nonneg.mpr ((le_div_iff₀ rp).mpr (inc i hi)))
    have off (i) (hi : k ≤ i) (h4 : i<4) : w i=0 := max_eq_left (sub_nonpos.mpr ((div_le_iff₀ rp).mpr (exc i hi h4)))
    change ∑ i ∈ Finset.range 4,w i=m
    have small : (∑ i ∈ Finset.range k,w i)=(∑ i ∈ Finset.range 4,w i) := by
      apply Finset.sum_subset (Finset.range_mono hkn)
      intro i h4 hn
      exact off i (by simpa using hn) (Finset.mem_range.mp h4)
    rw [← small,Finset.sum_congr rfl (fun i hi => on i (Finset.mem_range.mp hi))]
    simp only [Finset.sum_sub_distrib,div_eq_mul_inv,←Finset.sum_mul,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    change pref s k/r-(k:ℝ)*c=m
    have den : 0 < m+(k:ℝ)*c := by positivity
    have eq : r*(m+(k:ℝ)*c)=pref s k := div_mul_cancel₀ _ den.ne'
    have H : pref s k/r=m+(k:ℝ)*c := (div_eq_iff rp.ne').mpr (by linarith only [eq])
    rw [H]; ring
  have directional : ∀ v : ℕ → ℝ, (∀ i<4, 0 ≤ v i) → (∑ i ∈ Finset.range 4, v i)=m →
 (∑ i ∈ Finset.range 4, s i/(c+clipped s (ratio s m c k) c i)*(v i-clipped s (ratio s m c k) c i)) ≤ 0 := by
    intro v hv mv
    let r := ratio s m c k
    have rp : 0 < r := by
      have one : 0 < ratio s m c 1 := by simpa [ratio,pref] using div_pos (hs 0 (by decide)) (add_pos hm hc)
      exact one.trans_le (hbest 1 (by decide) (by decide))
    let w := clipped s r c
    have w0 (i) : 0 ≤ w i := le_max_left _ _
    have gain (i) : s i/(c+w i) ≤ r := by
      apply (div_le_iff₀ (add_pos_of_pos_of_nonneg hc (w0 i))).mpr
      have e : s i/r-c ≤ w i := le_max_right _ _
      have h : s i/r ≤ c+w i := by linarith
      nlinarith only [(div_le_iff₀ rp).mp h]
    have active (i) (ne : w i ≠ 0) : s i/(c+w i)=r := by
      have diff : 0 < s i/r-c := by by_contra h; exact ne (max_eq_left (le_of_not_gt h))
      have same : w i=s i/r-c := max_eq_right diff.le
      apply (div_eq_iff (add_pos_of_pos_of_nonneg hc (w0 i)).ne').mpr
      rw [same,add_sub_cancel]
      field_simp [rp.ne']
    have per (i) (hi : i<4) : s i/(c+w i)*(v i-w i) ≤ r*(v i-w i) := by
      by_cases z : w i=0
      · simpa only [z,sub_zero] using mul_le_mul_of_nonneg_right (gain i) (hv i hi)
      · rw [active i z]
    have bound := Finset.sum_le_sum (fun i (hi : i ∈ Finset.range 4) => per i (Finset.mem_range.mp hi))
    have Mw : ∑ i ∈ Finset.range 4,w i=m := candidateMass
    simpa only [← Finset.mul_sum,Finset.sum_sub_distrib,mv,Mw,sub_self,mul_zero] using bound
  refine ⟨candidateMass,?_⟩
  intro v hv mv
  let w := clipped s (ratio s m c k) c
  have w0 (i) : 0 ≤ w i := le_max_left _ _
  have one (i) (hi : i<4) : s i*Real.log (a*(c+v i))-s i*Real.log (a*(c+w i)) ≤ s i/(c+w i)*(v i-w i) := by
    have x := add_pos_of_pos_of_nonneg hc (hv i hi)
    have y := add_pos_of_pos_of_nonneg hc (w0 i)
    have h := Real.log_le_sub_one_of_pos (div_pos x y)
    rw [Real.log_div x.ne' y.ne'] at h
    rw [Real.log_mul ha.ne' x.ne',Real.log_mul ha.ne' y.ne']
    calc
      _ ≤ s i*((c+v i)/(c+w i)-1) := by linarith only [mul_le_mul_of_nonneg_left h (hs i hi).le]
      _ = _ := by field_simp [y.ne']; ring
  have bound := Finset.sum_le_sum (fun i (hi : i ∈ Finset.range 4) => one i (Finset.mem_range.mp hi))
  have H := bound.trans (directional v hv mv)
  rw [Finset.sum_sub_distrib,sub_nonpos] at H
  exact H

end BlockHierarchy.Four.WaterFilling
