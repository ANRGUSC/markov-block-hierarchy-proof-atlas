import ReducedPair.ZeroInformation
import FirstChange

open scoped BigOperators
namespace BlockHierarchy
open PairChannel

theorem model_total (m : BinaryModel) : ∑ x, m.source x=1 := by
  rw [word_sum]
  change m.A+m.C+m.C+m.B=1
  linarith only [m.left_mass,m.right_mass,m.normalized]

theorem constant_distortion (m : BinaryModel) (y : Word) :
    ∑ x, m.source x*(hamming x y : ℝ) = law (2*m.q) (2*m.p) 1 y := by
  rw [word_sum]
  obtain ⟨i,j⟩ := y
  cases i <;> cases j <;> norm_num [BinaryModel.source,law,hamming] <;>
    linarith only [m.left_mass,m.right_mass,m.normalized]

theorem product_cost (m : BinaryModel) (q : Word → ℝ) :
    jointCost (fun x y => q y*m.source x) = ∑ y, q y*law (2*m.q) (2*m.p) 1 y := by
  unfold jointCost Channel.cost
  rw [Finset.sum_comm]
  simp only [mul_assoc,← Finset.mul_sum,constant_distortion]

theorem zero_rate (m : BinaryModel) (D : ℝ) (budget : min m.p m.q ≤ D) :
    RateAt m.source D 0 ∧
    GibbsPoint m.source (pointMass (majorityWord m)) D 1 (fun _ => 1) ∧
    tiltedVariance m.source D 1 (fun _ => 1) = 0 := by
  let q := pointMass (majorityWord m)
  let J (x y : Word) := q y*m.source x
  have hq (y : Word) : 0 ≤ q y := by simp [q,pointMass]; split <;> norm_num
  have norm : ∑ y, q y = 1 := by simp [q,pointMass]
  have cap : jointCost J = 2*min m.p m.q := by
    rw [show jointCost J = _ from product_cost m q]
    by_cases h : m.q ≤ m.p
    · simp [q,pointMass,majorityWord,h,ite_mul,law]
    · simp [q,pointMass,majorityWord,h,ite_mul,law,min_eq_left (le_of_not_ge h)]
  have valid : MinimizesAt m.source q J D := by
    refine ⟨fun x y => mul_nonneg (hq y) (m.positive_source x).le,?_,?_,by linarith only [cap,budget],?_⟩
    · intro x; dsimp [J]; rw [←Finset.sum_mul,norm,one_mul]
    · intro y; dsimp [J]; rw [←Finset.mul_sum,model_total,mul_one]
    · intro t L hL _ dst _
      rw [show Channel.info m.source q J = 0 from Channel.independent_info _ _ m.positive_source]
      exact Channel.info_nonnegative _ _ _ hL dst m.positive_source (model_total m)
  refine ⟨⟨q,J,valid,by rw [show Channel.info m.source q J = 0 from
    Channel.independent_info _ _ m.positive_source,zero_div]⟩,⟨?_,?_⟩,?_⟩
  · intro x; simpa using norm.symm
  · simpa [J] using valid
  · simp [tiltedVariance,variance,mean,logTwo]

theorem unique_biased_zero_rate (m : BinaryModel) (biased : m.p ≠ m.q)
    (t : Word → ℝ) (L : Word → Word → ℝ) (hL : ∀ x y, 0 ≤ L x y)
    (src : ∀ x, ∑ y, L x y=m.source x) (dst : ∀ y, ∑ x, L x y=t y)
    (bound : jointCost L ≤ 2*min m.p m.q) (zero : Channel.info m.source t L = 0) :
    t = pointMass (majorityWord m) := by
  have prod := Channel.zero_info_independent m.source t L hL src dst m.positive_source (model_total m) zero
  have ht (y : Word) : 0 ≤ t y := by rw [←dst]; exact Finset.sum_nonneg (fun x _ => hL x y)
  have tot : ∑ y, t y=1 := by simp_rw [←dst]; rw [Finset.sum_comm]; simp_rw [src]; exact model_total m
  have lawcost : (∑ y, t y*law (2*m.q) (2*m.p) 1 y) ≤ 2*min m.p m.q := by
    rw [←product_cost m t,←show L = _ from funext (fun x => funext (prod x))]
    exact bound
  have residual (y : Word) : 0 ≤ t y*(law (2*m.q) (2*m.p) 1 y-2*min m.p m.q) := by
    apply mul_nonneg (ht y)
    obtain ⟨a,b⟩ := y
    cases a <;> cases b <;> simp only [law] <;>
      linarith only [min_le_left m.p m.q,min_le_right m.p m.q,m.normalized]
  have allzero : ∀ y, t y*(law (2*m.q) (2*m.p) 1 y-2*min m.p m.q)=0 := by
    intro y
    have ub := Finset.single_le_sum (fun i _ => residual i) (Finset.mem_univ y)
    simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,tot,one_mul] at ub
    exact le_antisymm (by linarith only [ub,lawcost]) (residual y)
  have off (y : Word) (hy : y ≠ majorityWord m) : t y = 0 := by
    have diff : law (2*m.q) (2*m.p) 1 y ≠ 2*min m.p m.q := by
      obtain ⟨a,b⟩ := y
      by_cases h : m.q ≤ m.p
      · have lt := lt_of_le_of_ne h biased.symm
        cases a <;> cases b <;> simp_all [majorityWord,law] <;> linarith [m.normalized]
      · have lt := lt_of_not_ge h
        cases a <;> cases b <;> simp_all [majorityWord,law,min_eq_left lt.le] <;> linarith [m.normalized]
    exact (mul_eq_zero.mp (allzero y)).resolve_right (sub_ne_zero.mpr diff)
  have on : t (majorityWord m) = 1 := by
    rw [Finset.sum_eq_single (majorityWord m)] at tot
    · exact tot
    · intro y _ hy; exact off y hy
    · simp
  funext y
  by_cases e : y=majorityWord m <;> simp [pointMass,e,on,off]

#print axioms zero_rate
#print axioms unique_biased_zero_rate
end BlockHierarchy
