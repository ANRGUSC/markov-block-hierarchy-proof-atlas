import BlockHierarchy.Four.Channel

open scoped BigOperators
namespace BlockHierarchy.Four

noncomputable def baseline (u : ℝ) (a : Class → ℝ) (i : Class) :=
  u^2*groupMass a i+((u+u^3)/2)*otherMass a i

noncomputable def coefficient (u : ℝ) (i : Class) :=
  (((1+u^4)/2-u^2)/(cardinal i/2))

theorem affine_Z (u : ℝ) (a : Class → ℝ) (i : Class) :
    Z u a i=baseline u a i+coefficient u i*a i := by
  simp only [Z,classKernel,baseline,coefficient,pow_zero,pow_one]

noncomputable def evenMass (w : Class → ℝ) := w 0+w 1+w 2+w 3
noncomputable def oddMass (w : Class → ℝ) := w 4+w 5

theorem mass_partition (w : Class → ℝ) : (∑ i, w i)=evenMass w+oddMass w := by
  rw [class_sum]; unfold evenMass oddMass; ring

theorem group_active {w : Class → ℝ} (hw : ∀ i, 0 ≤ w i) (i : Class) (h : w i ≠ 0) :
    (evenGroup i → 0 < evenMass w) ∧ (¬evenGroup i → 0 < oddMass w) := by
  have : 0 < w i := lt_of_le_of_ne (hw i) h.symm
  fin_cases i <;> norm_num [evenGroup,evenMass,oddMass]
  all_goals
    first | change 0 < w 0 at this | change 0 < w 1 at this | change 0 < w 2 at this
          | change 0 < w 3 at this | change 0 < w 4 at this | change 0 < w 5 at this
    linarith only [this,hw 0,hw 1,hw 2,hw 3,hw 4,hw 5]

theorem weighted_columns {p u : ℝ} (w : Class → ℝ)
    (hz : ∀ x, 0 < Z u w (orbit x)) :
    (∑ y, prior w y*Z u (ratio p u w) (orbit y))=1 := by
  simp_rw [← columns]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have row (x : Word) : ∑ y, prior w y*FiniteRD.kernel (source p)
      (fun x => Z u w (orbit x)) distance u x y=source p x := by
    change ∑ y, prior w y*(source p x/Z u w (orbit x)*u^distance x y)=_
    simp_rw [mul_left_comm (prior w _) (source p x/Z u w (orbit x)),←Finset.mul_sum,class_normalizer]
    exact div_mul_cancel₀ _ (hz x).ne'
  simp_rw [row]
  exact source_mass p

theorem column_test_of_common_bound {p u : ℝ} (w : Class → ℝ) (v : ℝ)
    (total : ∑ i, w i=1) (hz : ∀ x, 0 < Z u w (orbit x))
    (bound : ∀ i, Z u (ratio p u w) i ≤ v) (onSupport : ∀ i, w i≠0 → Z u (ratio p u w) i=v) :
    ∀ i, Z u (ratio p u w) i ≤ 1 ∧ (w i≠0 → Z u (ratio p u w) i=1) := by
  have term (y : Word) : prior w y*Z u (ratio p u w) (orbit y)=prior w y*v := by
    by_cases e : w (orbit y)=0
    · simp [prior,e]
    · rw [onSupport _ e]
  have eq := weighted_columns (p := p) w hz
  simp_rw [term] at eq
  rw [← Finset.sum_mul,group_weight,total,one_mul] at eq
  exact fun i => ⟨(bound i).trans_eq eq,fun e => (onSupport i e).trans eq⟩

/-- Moving one unit of mass from the odd to the even group yields the
difference of the two group multipliers, including the baseline terms. -/
noncomputable def paritySlope (u : ℝ) (a : Class → ℝ) (ηE ηO : ℝ) :=
  ηE-ηO+(u^2-(u+u^3)/2)*(evenMass a-oddMass a)

theorem parity_columns {p u : ℝ} (w : Class → ℝ) (ηE ηO : ℝ) (hu : 0 < u)
    (hw : ∀ i, 0 ≤ w i) (unit : ∑ i, w i=1)
    (gains : ∀ i, let g := coefficient u i*ratio p u w i; let η := if evenGroup i then ηE else ηO
                   g ≤ η ∧ (w i≠0 → g=η))
    (choice : let G := paritySlope u (ratio p u w) ηE ηO
              (evenMass w=0 ∧ G≤0) ∨ (oddMass w=0 ∧ 0≤G) ∨ G=0) :
    ∀ i, Z u (ratio p u w) i ≤ 1 ∧ (w i≠0 → Z u (ratio p u w) i=1) := by
  let a := ratio p u w
  let E := u^2*evenMass a+((u+u^3)/2)*oddMass a+ηE
  let O := u^2*oddMass a+((u+u^3)/2)*evenMass a+ηO
  have diff : E-O=paritySlope u a ηE ηO := by unfold E O paritySlope; ring
  have localBound (i : Class) : Z u a i ≤ (if evenGroup i then E else O) ∧
      (w i≠0 → Z u a i=(if evenGroup i then E else O)) := by
    obtain ⟨bound,eq⟩ := gains i
    rw [affine_Z]
    by_cases e : evenGroup i <;>
      simp only [e,if_true,if_false] at bound eq ⊢ <;>
      simp only [baseline,groupMass,otherMass,e,if_true,if_false,E,O,evenMass,oddMass] <;>
      exact ⟨add_le_add_right bound _,fun h => by rw [eq h]⟩
  apply column_test_of_common_bound w (max E O) unit (Z_pos hu w hw unit)
  · intro i
    exact (localBound i).1.trans (by split <;> simp)
  · intro i active
    rw [(localBound i).2 active]
    obtain ⟨pe,po⟩ := group_active hw i active
    rcases choice with ⟨empty,sign⟩ | ⟨empty,sign⟩ | eq
    · have odd : ¬evenGroup i := fun e => (pe e).ne' empty
      rw [if_neg odd,max_eq_right (by linarith only [diff,sign])]
    · have even : evenGroup i := by by_contra h; exact (po h).ne' empty
      rw [if_pos even,max_eq_left (by linarith only [diff,sign])]
    · have same : E=O := by linarith only [diff,eq]
      simp [same]

end BlockHierarchy.Four
