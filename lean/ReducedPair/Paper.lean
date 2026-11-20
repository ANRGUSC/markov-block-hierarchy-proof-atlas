import ReducedPair.PaperStatement
import ReducedPair.Middle
import ReducedPair.Full
import ReducedPair.ZeroRate
import ReducedPair.LosslessValue
import ReducedPair.Unique

namespace BlockHierarchy
open PairChannel

theorem persistent_pair : PersistentPairStatement := by
  intro m pos
  let r := (1-Real.sqrt (1-4*m.C))/2
  have hA := m.positive_source (false,false)
  have hB := m.positive_source (true,true)
  have hC := m.positive_source (false,true)
  change 0 < m.A at hA
  change 0 < m.B at hB
  change 0 < m.C at hC
  have mass : m.A+2*m.C+m.B=1 := by linarith only [m.left_mass,m.right_mass,m.normalized]
  have rho : m.persistence < 1 := by unfold BinaryModel.persistence; linarith [m.apos,m.bpos]
  have h := positive_first_change m.p m.q m.persistence m.ppos m.qpos m.normalized pos rho
  dsimp only at h
  rw [m.trans_mass,←m.left_mass,←m.right_mass] at h
  obtain ⟨hr,half,atD⟩ := h
  change 0 < r at hr
  change r < 1/2 at half
  have cq : m.C < m.p*m.q := by
    nlinarith only [m.trans_mass,mul_pos (mul_pos pos m.ppos) m.qpos]
  have disc : 0 < 1-4*m.C := by
    have hsq : (m.p+m.q)^2=1 := by rw [m.normalized]; norm_num
    nlinarith only [hsq,sq_nonneg (m.p-m.q),cq]
  have root : r*(1-r)=m.C := by dsimp [r]; nlinarith only [Real.sq_sqrt disc.le]
  have less (a b : ℝ) (norm : a+b=1) (prod : m.C<a*b) : r<a := by
    by_contra! le
    have hpos : 0 ≤ 1-r-a := by linarith only [half,le]
    nlinarith only [mul_nonneg (sub_nonneg.mpr le) hpos,root,congrArg (fun v : ℝ => a*v) norm,prod]
  have endpt : r < min m.p m.q := lt_min (less m.p m.q m.normalized cq)
    (less m.q m.p (by linarith only [m.normalized]) (by rwa [mul_comm]))
  have minEq : m.C+min m.A m.B=min m.p m.q := by
    rw [m.left_mass,m.right_mass]
    rcases le_total m.p m.q with h | h
    · rw [min_eq_left (sub_le_sub_right h _),min_eq_left h]; ring
    · rw [min_eq_right (sub_le_sub_right h _),min_eq_right h]; ring
  refine ⟨hr,endpt,?_,?_,fun D b => zero_rate m D b,?_⟩
  · intro D hn hi
    have hhalf := lt_of_le_of_lt hi half
    obtain ⟨ca,cb,pt,zt⟩ := atD D hn hhalf
    have tr : 0 ≤ transitionMass m.A m.B m.C D := by
      rcases lt_or_eq_of_le hi with lt | eq
      · exact (pt.mpr lt).le
      · exact (zt.mpr eq).symm.le
    have feasible (w : Word) : 0 ≤ PairChannel.prior m.A m.B m.C (D/(1-D)) w := by
      obtain ⟨a,b⟩ := w
      cases a <;> cases b <;> first | exact ca.le | exact cb.le | exact tr
    rcases eq_or_lt_of_le hn with hz | positive
    · subst D
      have q : PairChannel.prior m.A m.B m.C 0 = m.source := by
        funext ⟨a,b⟩; cases a <;> cases b <;> simp [PairChannel.prior,BinaryModel.source,law]
      simpa [q,binaryEntropyNats,tiltedVariance,logTwo] using
        (show RateAt m.source 0 ((-mean m.source (fun x => Real.log (m.source x)))/Real.log 2) ∧
          GibbsPoint m.source m.source 0 0 m.source ∧
          variance m.source (fun x => -(Real.log (m.source x)/Real.log 2)) =
            variance m.source (fun x => -(Real.log (m.source x)/Real.log 2)) from
          ⟨lossless_value m.source (fun x => (m.positive_source x).le),lossless_point m,rfl⟩)
    · obtain ⟨rate,var⟩ := full_values positive hhalf feasible
      exact ⟨rate,(full_point positive hhalf feasible).1,var⟩
  · intro D first last
    obtain ⟨rate,point,support,var⟩ := ReducedPair.middle_branch hA hB hC mass hr half root first (minEq.symm ▸ last)
    exact ⟨rate,point,support,fun t J => ReducedPair.middle_unique hA hB hC mass hr half root first
      (minEq.symm ▸ last) t J,var⟩
  · exact unique_biased_zero_rate m

#print axioms persistent_pair
end BlockHierarchy
