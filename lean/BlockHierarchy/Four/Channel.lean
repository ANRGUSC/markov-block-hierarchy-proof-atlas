import BlockHierarchy.Four.Classes
import BlockHierarchy.Four.AllocationIdentities
import BlockHierarchy.FiniteRD

open scoped BigOperators
namespace BlockHierarchy.Four

theorem cardinal_pos (i : Class) : 0 < cardinal i := by
  unfold cardinal
  split <;> norm_num

theorem source_classes_pos {p : ℝ} (hp : 0 < p) (ph : p < 1/2) (i : Class) :
    0 < sourceClasses p i := by
  have h : 0 < 1-p := by linarith
  fin_cases i <;> norm_num [sourceClasses] <;> positivity

theorem source_mass (p : ℝ) : ∑ x, source p x=1 := by
  simp_rw [source_probability,group_weight,class_sum]
  simpa [sourceClasses] using class_totals.1 p

theorem distance_comm (x y : Word) : distance x y=distance y x := by
  simp only [distance,Three.hamming_comm x.2,eq_comm]

noncomputable def ratio (p u : ℝ) (w : Class → ℝ) (i : Class) := sourceClasses p i / Z u w i

theorem columns (p u : ℝ) (w : Class → ℝ) (y : Word) :
    ∑ x, FiniteRD.kernel (source p) (fun x => Z u w (orbit x)) distance u x y =
      Z u (ratio p u w) (orbit y) := by
  have each (x : Word) : FiniteRD.kernel (source p) (fun x => Z u w (orbit x)) distance u x y =
      prior (ratio p u w) x*u^distance y x := by
    rw [FiniteRD.kernel,source_probability,distance_comm x y]
    unfold prior ratio
    ring
  simp_rw [each]
  exact class_normalizer .. 

theorem normalized_cost (p u : ℝ) (w : Class → ℝ) :
    Channel.cost (fun x y => (distance x y : ℝ))
      (FiniteRD.joint (source p) (fun x => Z u w (orbit x)) (prior w) distance u) =
      ∑ i, sourceClasses p i*(costNumerator u w i/Z u w i) := by
  have row (x : Word) :
      (∑ y, FiniteRD.joint (source p) (fun x => Z u w (orbit x)) (prior w) distance u x y*(distance x y:ℝ)) =
      source p x*(costNumerator u w (orbit x)/Z u w (orbit x)) := by
    rw [← class_cost_numerator u w x]
    simp only [div_eq_mul_inv,Finset.sum_mul,Finset.mul_sum,FiniteRD.joint,FiniteRD.kernel]
    apply Finset.sum_congr rfl
    intro y _
    ring
  unfold Channel.cost
  simp_rw [row]
  exact class_expectation p (fun i => costNumerator u w i/Z u w i)

theorem Z_pos {u : ℝ} (hu : 0 < u) (w : Class → ℝ) (hw : ∀ i, 0 ≤ w i)
    (unit : ∑ i, w i=1) (x : Word) : 0 < Z u w (orbit x) := by
  rw [← class_normalizer u w x]
  have q (y) : 0 ≤ prior w y := div_nonneg (hw _) (cardinal_pos _).le
  have pos : 0 < ∑ y, prior w y := by rw [group_weight,unit]; norm_num
  obtain ⟨y,_,hy⟩ := (Finset.sum_pos_iff_of_nonneg (fun y _ => q y)).mp pos
  apply (Finset.sum_pos_iff_of_nonneg (fun y _ => mul_nonneg (q y) (pow_nonneg hu.le _))).mpr
  exact ⟨y,Finset.mem_univ _,mul_pos hy (pow_pos hu _)⟩

noncomputable def classTiltVariance (p u : ℝ) (w : Class → ℝ) :=
  variance (sourceClasses p) (fun i => -logTwo (Z u w i))

theorem rate_and_variance {p u D : ℝ} (hp : 0 < p) (ph : p < 1/2)
    (hu : 0 < u) (uh : u ≤ 1) (w : Class → ℝ) (hw : ∀ i, 0 ≤ w i) (unit : ∑ i, w i=1)
    (dual : ∀ i, Z u (ratio p u w) i ≤ 1 ∧ (w i ≠ 0 → Z u (ratio p u w) i=1))
    (budget : (∑ i, sourceClasses p i*(costNumerator u w i/Z u w i))=4*D) :
    let z := fun x => Z u w (orbit x)
    let J := FiniteRD.joint (source p) z (prior w) distance u
    FiniteRD.Optimal (source p) (prior w) distance J (4*D) ∧
    Channel.info (source p) (prior w) J / Real.log 2 =
      4*D*logTwo u - ∑ i, sourceClasses p i*logTwo (Z u w i) ∧
    variance (source p) (fun x => 4*D*logTwo u-logTwo (z x))=classTiltVariance p u w := by
  have src (x) : 0 < source p x := by
    rw [source_probability]; exact div_pos (source_classes_pos hp ph _) (cardinal_pos _)
  have q (y) : 0 ≤ prior w y := div_nonneg (hw _) (cardinal_pos _).le
  have cols (y : Word) : (∑ x, FiniteRD.kernel (source p) (fun x => Z u w (orbit x)) distance u x y) ≤ 1 ∧
      (prior w y ≠ 0 → ∑ x, FiniteRD.kernel (source p) (fun x => Z u w (orbit x)) distance u x y=1) := by
    rw [columns]
    exact ⟨(dual _).1,fun active => (dual _).2 (fun e => active (by simp [prior,e]))⟩
  have cert := FiniteRD.certificate (d := distance) src (Z_pos hu w hw unit) q hu uh
    (class_normalizer u w) cols ((normalized_cost p u w).trans budget)
  refine ⟨cert.1,cert.2.trans ?_,?_⟩
  · rw [mean,class_expectation p (fun i => logTwo (Z u w i))]
  · simp only [sub_eq_add_neg]
    rw [variance_shift _ _ (source_mass p)]
    unfold classTiltVariance variance mean
    rw [class_expectation p (fun i => -logTwo (Z u w i))]
    exact class_expectation p (fun i => (-logTwo (Z u w i)-∑ j, sourceClasses p j*(-logTwo (Z u w j)))^2)

end BlockHierarchy.Four
