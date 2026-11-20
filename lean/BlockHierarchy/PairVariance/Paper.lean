import BlockHierarchy.PairVariance.Generic
import BlockHierarchy.Four.Maximizer

open scoped BigOperators
namespace BlockHierarchy.PairVariance

theorem three_display : ThreeDisplayStatement := by
  intro p D u Z pos
  let s := threeWeights p
  have total : ∑ i, s i=1 := by simp [s,threeWeights,Fin.sum_univ_three]; ring
  rw [Three.class_tilt]
  have classes : Three.classVariance p (-logTwo (Z 0)) (-logTwo (Z 1)) (-logTwo (Z 2)) =
      variance s (fun i => (0:ℝ)-logTwo (Z i)) := by
    simp [variance,mean,s,threeWeights,Fin.sum_univ_three,Three.classVariance,Three.classMean]
    ac_rfl
  exact classes.trans (shifted_log_variance s Z total pos 0)

theorem four_display : FourDisplayStatement := by
  intro p D u w hu hw total
  have pos (i : Four.Class) : 0<Four.Z u w i := by
    simpa only [Four.orbit_rep] using Four.Z_pos hu w hw total (Four.representative i)
  let f (i : Four.Class) := 4*D*logTwo u-logTwo (Four.Z u w i)
  have agg : variance (Four.source p) (fun x => f (Four.orbit x)) = variance (Four.sourceClasses p) f := by
    unfold variance mean
    rw [Four.class_expectation p f]
    exact Four.class_expectation p (fun i => (f i-(∑ j, Four.sourceClasses p j*f j))^2)
  have unit : ∑ i, Four.sourceClasses p i=1 := by
    have same := Four.class_expectation p (fun _ => 1)
    simpa only [mul_one,Four.source_mass] using same.symm
  exact agg.trans (shifted_log_variance _ _ unit pos (4*D*logTwo u))

theorem three_four_pair_variance : ThreeFourDisplayStatement := ⟨three_display,four_display⟩

#print axioms shifted_log_variance
#print axioms three_four_pair_variance
end BlockHierarchy.PairVariance
