import BlockHierarchy.RecurrenceCriterion
import BlockHierarchy.RecurrenceInverse
import BlockHierarchy.RecurrenceOrder
import BlockHierarchy.RecurrenceThresholds

open Set Filter
open scoped Topology

namespace BlockHierarchy.Recurrence

/-- Up to and including a first visit to the pole the observed prefix maxima agree
with the scalar iteration. This does not extend the moment recurrence past its domain. -/
theorem maxima_scalar_iff {ρ z : ℝ} {H : ℕ → ℝ} (initial : H 0=0)
    (step : ∀ n, (∀ j≤n, H j<z) → H (n+1)=peak ρ z (H n)) (n : ℕ) :
    ((∀ j<n, H j<z) ∧ H n≤z) ↔ ScalarFeasible ρ z n := by
  have eq (k : ℕ) (before : ∀ j<k, H j<z) : H k=orbit ρ z k := by
    induction k with
    | zero => exact initial
    | succ k ih =>
      rw [step k (fun j hj => before j (by omega)),orbit,ih (fun j hj => before j (by omega))]
      rfl
  have back (k : ℕ) (before : ∀ j<k, orbit ρ z j<z) : ∀ j<k, H j<z := by
    induction k with
    | zero => omega
    | succ k ih =>
      have prior := ih (fun j hj => before j (by omega))
      intro j hj
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h|rfl
      · exact prior j h
      · rw [eq _ prior]; exact before _ (by omega)
  constructor
  · rintro ⟨before,last⟩
    exact ⟨fun j hj => (eq j (fun i hi => before i (hi.trans hj))) ▸ before j hj,
      (eq n before) ▸ last⟩
  · rintro ⟨before,last⟩
    exact ⟨back n before,(eq n (back n before)).symm ▸ last⟩

theorem inverse_scalar_iff {p z : ℝ} (hp : 0<p) (ph : p<1/2) (hz : 0<z) (zh : z<1) (n : ℕ) :
    InverseNonnegative p z (n+1) ↔ ScalarFeasible (1-2*p) z n := by
  obtain ⟨H,_,initial,step,criterion⟩ := prefix_criterion hp ph hz zh
  exact (criterion n).trans (maxima_scalar_iff initial step n)

theorem gray_interior {p : ℝ} (hp : 0<p) (ph : p<1/2) : grayD p ∈ Ioo (0:ℝ) (1/2) := by
  let ρ := 1-2*p
  have hpos : 0<ρ := by dsimp [ρ]; linarith
  have hlt : ρ<1 := by dsimp [ρ]; linarith
  have rpos := Real.sqrt_pos.mpr hpos
  have rsq := Real.sq_sqrt hpos.le
  have rlt : Real.sqrt ρ<1 := by nlinarith only [rsq,hlt,sq_nonneg (Real.sqrt ρ-1)]
  have den : 0<1+ρ := by positivity
  have l : 0<2*Real.sqrt ρ/(1+ρ) := by positivity
  have u : 2*Real.sqrt ρ/(1+ρ)<1 := (div_lt_one den).mpr (by
    nlinarith only [rsq,sq_pos_of_pos (sub_pos.mpr rlt)])
  change 0<(1-2*Real.sqrt ρ/(1+ρ))/2 ∧ (1-2*Real.sqrt ρ/(1+ρ))/2<1/2
  constructor <;> linarith

theorem finite_block_recurrence : RecurrenceStatement := by
  intro p hp ph
  have rp : 0<1-2*p := by linarith
  have r1 : 1-2*p<1 := by linarith
  refine ⟨?_,critical_distortion_identity p hp ph,?_⟩
  · intro D hd dh
    obtain ⟨H,hH,h0,hrec,criterion⟩ := prefix_criterion hp ph
      (show 0<1-2*D by linarith) (show 1-2*D<1 by linarith)
    exact ⟨H,hH,h0,hrec,fun n => backward_iff_inverse dh _,
      fun n => (backward_iff_inverse dh _).trans (criterion n)⟩
  let P := fun n D => InverseNonnegative p (1-2*D) (n+1)
  have closed (n : ℕ) : IsClosed {t : InteriorDistortion | P n t.val} := finite_feasibility_closed p _
  have down (n : ℕ) (x : ℝ) (hx : x∈Ioo (0:ℝ) (1/2)) (y : ℝ) (hy : y∈Ioo (0:ℝ) (1/2))
      (xy : x≤y) (fy : P n y) : P n x := by
    obtain ⟨xl,xh⟩ := hx
    obtain ⟨yl,yh⟩ := hy
    have yf := (inverse_scalar_iff hp ph (show 0<1-2*y by linarith) (show 1-2*y<1 by linarith) n).mp fy
    apply (inverse_scalar_iff hp ph (show 0<1-2*x by linarith) (show 1-2*x<1 by linarith) n).mpr
    exact feasible_increases_with_z rp (by linarith) (by linarith) (by linarith) n yf
  have nested (n : ℕ) (x : ℝ) (_ : x∈Ioo (0:ℝ) (1/2)) (h : P (n+1) x) : P n x :=
    shorter_nonnegative (Nat.le_succ _) h
  have every (D : ℝ) (hD : D∈Ioo (0:ℝ) (1/2)) : (∀ n, P n D) ↔ D≤grayD p := by
    obtain ⟨hd,dh⟩ := hD
    have hz : 0<1-2*D := by linarith
    have zh : 1-2*D<1 := by linarith
    have scalar := inverse_scalar_iff hp ph hz zh
    have allBelow : (∀ n, P n D) ↔ ∀ j, orbit (1-2*p) (1-2*D) j < 1-2*D :=
      ⟨fun h j => ((scalar (j+1)).mp (h (j+1))).1 j (Nat.lt_succ_self j),
       fun h n => (scalar n).mpr ⟨fun j _ => h j,(h n).le⟩⟩
    rw [allBelow,orbit_below_iff rp r1 hz zh]
    unfold grayD
    constructor <;> intro h <;> linarith only [h]
  obtain ⟨d,range,anti,criterion,lim⟩ := threshold_intervals P (grayD p) (gray_interior hp ph)
    closed down nested every
  exact ⟨d,range,anti,fun n D hd dh => (backward_iff_inverse dh _).trans (criterion n D hd dh),lim⟩

#print axioms finite_block_recurrence

end BlockHierarchy.Recurrence
