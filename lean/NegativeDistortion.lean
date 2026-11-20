import NegativeSupport

namespace BlockHierarchy.NegativeSupport

/-- Signs of the actual four candidate masses, in the distortion variable. -/
def ThresholdAt (A B C d : ℝ) : Prop :=
  0 < d ∧ d < 1/2 ∧
  (∀ D, 0 ≤ D → D < d →
    0 < constantMass A B C D ∧ 0 < constantMass B A C D ∧ 0 < transitionMass A B C D) ∧
  0 ≤ constantMass A B C d ∧ 0 ≤ constantMass B A C d ∧ 0 < transitionMass A B C d ∧
  (constantMass A B C d = 0 ↔ A ≤ B) ∧ (constantMass B A C d = 0 ↔ B ≤ A)

theorem ordered_distortion {A B C : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (order : A ≤ B) (hd : 0 < C^2-A*B) :
    let r := (C-Real.sqrt (C^2-A*B))/B
    ThresholdAt A B C (r/(1+r)) := by
  let r := (C-Real.sqrt (C^2-A*B))/B
  let d := r/(1+r)
  obtain ⟨hr,hr1,slope⟩ := root_bounds hA hB hC order hd
  have hr0 : 0 < r := hr
  have hrlt : r < 1 := hr1
  have one : 0 < 1+r := by linarith
  have hdpos : 0 < d := div_pos hr0 one
  have hdhalf : d < 1/2 := (div_lt_iff₀ one).mpr (by linarith)
  have inv : d/(1-d) = r := by
    apply (div_eq_iff (show 1-d ≠ 0 by linarith)).mpr
    have h : d*(1+r) = r := div_mul_cancel₀ _ one.ne'
    nlinarith only [h]
  have den : 0 < (1-r)^2 := sq_pos_of_pos (sub_pos.mpr hrlt)
  have zero : N A B C r = 0 := smaller_root hB hd
  have gap := constant_gap A B C r
  have hr2 : 0 < 1-r^2 := by nlinarith only [mul_pos (sub_pos.mpr hrlt) one]
  have other : 0 ≤ N B A C r := by linarith [mul_nonneg (sub_nonneg.mpr order) hr2.le]
  have transition := transition_positive hC order hd hr0.le (slope r le_rfl)
  change ThresholdAt A B C d
  unfold ThresholdAt
  refine ⟨hdpos,hdhalf,?_,?_⟩
  · intro D hD hDd
    let u := D/(1-D)
    have h1 : 0 < 1-D := by linarith
    have hu : 0 ≤ u := div_nonneg hD h1.le
    have hur : u < r := by
      apply (div_lt_iff₀ h1).mpr
      have h := (lt_div_iff₀ one).mp hDd
      nlinarith only [h]
    have hu1 : u < 1 := hur.trans hrlt
    have pos := positive_before_root hB zero (slope r le_rfl) hur
    have gapu := constant_gap A B C u
    have hu2 : 0 < 1-u^2 := by
      nlinarith only [mul_pos (sub_pos.mpr hu1) (show 0 < 1+u by linarith)]
    have pos' : 0 < N B A C u := by linarith [mul_nonneg (sub_nonneg.mpr order) hu2.le]
    have denom := sq_pos_of_pos (sub_pos.mpr hu1)
    exact ⟨div_pos pos denom, div_pos pos' denom,
      div_pos (transition_positive hC order hd hu (slope u hur.le)) denom⟩
  · unfold constantMass transitionMass
    simp only [inv]
    change 0 ≤ N A B C r / _ ∧ 0 ≤ N B A C r / _ ∧ _ ∧
      (N A B C r / _ = 0 ↔ _) ∧ (N B A C r / _ = 0 ↔ _)
    have tie := constant_tie hr0.le hrlt zero
    refine ⟨div_nonneg (le_of_eq zero.symm) den.le, div_nonneg other den.le,
      div_pos transition den, ?_, ?_⟩
    · simp [zero, order]
    · simpa [div_eq_zero_iff, den.ne'] using tie.trans
        (show B = A ↔ B ≤ A from ⟨fun h => h.le, fun h => le_antisymm h order⟩)

theorem exchange {A B C d : ℝ} (h : ThresholdAt B A C d) : ThresholdAt A B C d := by
  have swap (D : ℝ) : transitionMass A B C D = transitionMass B A C D := by
    unfold transitionMass
    rw [add_comm A B]
  obtain ⟨h0,h1,before,b,a,t,zB,zA⟩ := h
  refine ⟨h0,h1,?_,a,b,(swap d).symm ▸ t,zA,zB⟩
  intro D hn hD
  obtain ⟨pb,pa,pt⟩ := before D hn hD
  exact ⟨pa,pb,(swap D).symm ▸ pt⟩

theorem negative_distortion {A B C : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hd : 0 < C^2-A*B) :
    let r := (C-Real.sqrt (C^2-A*B))/max A B
    ThresholdAt A B C (r/(1+r)) := by
  rcases le_total A B with h | h
  · simpa only [max_eq_right h] using ordered_distortion hA hB hC h hd
  · have hd' : 0 < C^2-B*A := by rwa [mul_comm B A]
    simpa only [max_eq_left h, mul_comm B A] using exchange (ordered_distortion hB hA hC h hd')

end BlockHierarchy.NegativeSupport
