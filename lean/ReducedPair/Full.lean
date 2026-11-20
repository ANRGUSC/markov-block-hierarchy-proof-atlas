import ReducedPair.GibbsValue
import FirstChange

open scoped BigOperators
namespace BlockHierarchy
open PairChannel

theorem full_point {m : BinaryModel} {D : ℝ} (pos : 0 < D) (half : D < 1/2)
    (feasible : ∀ y, 0 ≤ PairChannel.prior m.A m.B m.C (D/(1-D)) y) :
    let u := D/(1-D)
    let Z := fun x => (1+u)^2*m.source x
    let q := PairChannel.prior m.A m.B m.C u
    GibbsPoint m.source q D u Z ∧ jointCost (fun x y => q y*(m.source x*u^hamming x y/Z x)) = 2*D := by
  let u := D/(1-D)
  let Z := fun x => (1+u)^2*m.source x
  let q := PairChannel.prior m.A m.B m.C u
  have hd : 0 < 1-D := by linarith
  have hu : 0 < u := div_pos pos hd
  have h1 : u < 1 := (div_lt_iff₀ hd).mpr (by linarith)
  have plus : 0 < 1+u := by linarith
  have mass : m.A+2*m.C+m.B=1 := by linarith only [m.left_mass,m.right_mass,m.normalized]
  have norm := prior_total m.A m.B m.C u h1 mass
  have sumP : ∑ x, m.source x=1 := by rw [word_sum]; change m.A+m.C+m.C+m.B=1; linarith
  have rows := inverse m.A m.B m.C u hu.le h1
  have cols := column_sum u hu.le
  have ker (x y : Word) : m.source x*u^hamming x y/Z x = backward u x y := by
    dsimp [Z,backward]
    field_simp [plus.ne',(m.positive_source x).ne']
  have hK (x y : Word) : 0 < backward u x y := div_pos (pow_pos hu _) (sq_pos_of_pos plus)
  have logs (x y : Word) : Real.log (backward u x y) =
      Real.log u*(hamming x y : ℝ)-2*Real.log (1+u) := by
    rw [backward,Real.log_div (pow_pos hu _).ne' (sq_pos_of_pos plus).ne',Real.log_pow,Real.log_pow]
    push_cast
    ring
  have cap : jointCost (fun x y => q y*backward u x y) = 2*D := by
    rw [show jointCost _ = _ from joint_cost u hu.le q norm]
    apply (div_eq_iff plus.ne').mpr
    have h : u*(1-D)=D := div_mul_cancel₀ _ hd.ne'
    nlinarith only [h]
  change GibbsPoint m.source q D u Z ∧ _
  unfold GibbsPoint
  change ((_ ∧ MinimizesAt m.source q (fun x y => q y*(m.source x*u^hamming x y/Z x)) D) ∧
    jointCost (fun x y => q y*(m.source x*u^hamming x y/Z x)) = 2*D)
  simp_rw [ker]
  refine ⟨⟨?_,fun x y => mul_nonneg (feasible y) (hK x y).le,rows,?_,cap.le,?_⟩,cap⟩
  · intro x
    have hx : (∑ y, q y*u^hamming x y)/(1+u)^2 = m.source x := by
      have h := rows x
      simpa only [q,BinaryModel.source,backward,div_eq_mul_inv,←mul_assoc,←Finset.sum_mul] using h
    exact (mul_comm _ _).trans ((div_eq_iff (sq_pos_of_pos plus).ne').mp hx).symm
  · intro y; rw [←Finset.mul_sum,cols,mul_one]
  · intro t J hJ src dst bound
    exact Channel.backward_optimal _ q t _ J _ _ _ (Real.log_nonpos hu.le h1.le) hK hJ rows sumP cols
      logs src dst (bound.trans_eq cap.symm)

theorem full_values {m : BinaryModel} {D : ℝ} (pos : 0 < D) (half : D < 1/2)
    (feasible : ∀ y, 0 ≤ PairChannel.prior m.A m.B m.C (D/(1-D)) y) :
    let u := D/(1-D)
    let Z := fun x => (1+u)^2*m.source x
    RateAt m.source D ((-mean m.source (fun x => Real.log (m.source x))-2*binaryEntropyNats D)/Real.log 2) ∧
      tiltedVariance m.source D u Z = variance m.source (fun x => -logTwo (m.source x)) := by
  let u := D/(1-D)
  let Z := fun x => (1+u)^2*m.source x
  have hd : 0 < 1-D := by linarith
  have hu : 0 < u := div_pos pos hd
  have plus : 0 < 1+u := by linarith
  have sumP : ∑ x, m.source x=1 := by
    rw [word_sum]; change m.A+m.C+m.C+m.B=1
    linarith only [m.left_mass,m.right_mass,m.normalized]
  obtain ⟨point,cost⟩ := full_point pos half feasible
  have hz (x : Word) : 0 < Z x := mul_pos (sq_pos_of_pos plus) (m.positive_source x)
  have zlog (x : Word) : Real.log (Z x) = 2*Real.log (1+u)+Real.log (m.source x) := by
    dsimp [Z]
    rw [Real.log_mul (sq_pos_of_pos plus).ne' (m.positive_source x).ne',Real.log_pow]
    norm_num
  have l1 : Real.log (1+u) = -Real.log (1-D) := by
    have h : 1+u = 1/(1-D) := by dsimp [u]; field_simp [hd.ne']; ring
    rw [h,Real.log_div one_ne_zero hd.ne',Real.log_one,zero_sub]
  have lu : Real.log u = Real.log D-Real.log (1-D) := Real.log_div pos.ne' hd.ne'
  have value := gibbs_rate point hu m.positive_source hz cost
  have avg : mean m.source (fun x => Real.log (Z x)) =
      2*Real.log (1+u)+mean m.source (fun x => Real.log (m.source x)) := by
    simp [mean,zlog,mul_add,Finset.sum_add_distrib,←Finset.sum_mul,sumP]
  have id : 2*D*Real.log u-mean m.source (fun x => Real.log (Z x)) =
      -mean m.source (fun x => Real.log (m.source x))-2*binaryEntropyNats D := by
    rw [avg,lu,l1]; unfold binaryEntropyNats; ring
  refine ⟨?_,?_⟩
  · rwa [id] at value
  · change variance m.source (fun x => 2*D*logTwo u-logTwo (Z x)) = _
    have tilt (x : Word) : 2*D*logTwo u-logTwo (Z x) =
        (2*D*logTwo u-2*logTwo (1+u))+(-logTwo (m.source x)) := by unfold logTwo; rw [zlog]; ring
    simp_rw [tilt]
    exact variance_shift _ _ sumP _

end BlockHierarchy
