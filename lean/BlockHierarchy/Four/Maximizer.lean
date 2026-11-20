import BlockHierarchy.Four.Channel
import Mathlib.Analysis.Convex.StdSimplex

open scoped BigOperators
namespace BlockHierarchy.Four

def representative : Class → Word := ![(false,false,false,false),(false,false,true,true),
  (false,true,true,false),(false,true,false,true),(false,false,false,true),(false,false,true,false)]

theorem orbit_rep (i : Class) : orbit (representative i)=i := by fin_cases i <;> rfl

noncomputable def objective (p u : ℝ) (w : Class → ℝ) :=
  ∑ i, sourceClasses p i * Real.log (Z u w i)

theorem Z_continuous (i : Class) : Continuous (fun t : ℝ × (Class → ℝ) => Z t.1 t.2 i) := by
  unfold Z classKernel groupMass otherMass
  by_cases e : evenGroup i <;> simp only [e,if_true,if_false] <;> fun_prop

theorem objective_continuous (p : ℝ) {u : ℝ} (hu : 0 < u) :
    ContinuousOn (objective p u) (stdSimplex ℝ Class) := by
  intro w hw
  apply ContinuousAt.continuousWithinAt
  have entry (i : Class) : ContinuousAt (fun v => sourceClasses p i * Real.log (Z u v i)) w := by
    apply continuousAt_const.mul
    have cont : Continuous (fun v : Class → ℝ => Z u v i) :=
      (Z_continuous i).comp (continuous_const.prodMk continuous_id)
    have pos := Z_pos hu w hw.1 hw.2 (representative i)
    rw [orbit_rep] at pos
    exact cont.continuousAt.log pos.ne'
  unfold objective
  simp_rw [class_sum]
  exact (((((entry 0).add (entry 1)).add (entry 2)).add (entry 3)).add (entry 4)).add (entry 5)

theorem exists_optimal_prior (p : ℝ) {u : ℝ} (hu : 0 < u) :
    ∃ w ∈ stdSimplex ℝ Class, IsMaxOn (objective p u) (stdSimplex ℝ Class) w :=
  (isCompact_stdSimplex ℝ Class).exists_isMaxOn ⟨_,single_mem_stdSimplex ℝ (0:Class)⟩
    (objective_continuous p hu)

def paritySlice (θ : ℝ) :=
  (stdSimplex ℝ Class) ∩ {w | w 0+w 1+w 2+w 3=θ}

theorem slice_nonempty {θ : ℝ} (lo : 0 ≤ θ) (hi : θ ≤ 1) : (paritySlice θ).Nonempty := by
  let w (i : Class) : ℝ := match i.val with
    | 0 => θ
    | 4 => 1-θ
    | _ => 0
  refine ⟨w,⟨?_,?_⟩,?_⟩
  · intro i
    fin_cases i <;> first | exact lo | exact sub_nonneg.mpr hi | exact le_rfl
  · rw [class_sum]
    change θ+0+0+0+(1-θ)+0=1
    ring
  · change θ+0+0+0=θ
    ring

theorem exists_optimal_slice (p : ℝ) {u θ : ℝ} (hu : 0 < u) (lo : 0 ≤ θ) (hi : θ ≤ 1) :
    ∃ w ∈ paritySlice θ, IsMaxOn (objective p u) (paritySlice θ) w := by
  have cont : Continuous (fun w : Class → ℝ => w 0+w 1+w 2+w 3) := by fun_prop
  have compact : IsCompact (paritySlice θ) :=
    (isCompact_stdSimplex ℝ Class).inter_right (isClosed_eq cont continuous_const)
  exact compact.exists_isMaxOn (slice_nonempty lo hi)
    ((objective_continuous p hu).mono (fun _ h => h.1))

end BlockHierarchy.Four
