import FirstChangeStatement
import Lossless
import NegativeDistortion
import IndependentSupport
import PairUniqueness

namespace BlockHierarchy
open PairChannel

namespace BinaryModel

theorem left_mass (m : BinaryModel) : m.A = m.p-m.C := by unfold A C; ring
theorem right_mass (m : BinaryModel) : m.B = m.q-m.C := by
  unfold B C
  linarith only [m.balanced, mul_sub m.q 1 m.b, mul_one m.q]

theorem trans_mass (m : BinaryModel) : (1-m.persistence)*m.p*m.q = m.C := by
  have h : (m.p+m.q)*m.a = m.a := by rw [m.normalized,one_mul]
  have k : (m.a+m.b)*m.q = m.a := by nlinarith only [h,m.balanced]
  unfold persistence C
  nlinarith only [congrArg (fun v : ℝ => m.p*v) k]

theorem positive_source (m : BinaryModel) (w : Word) : 0 < m.source w := by
  obtain ⟨a,b⟩ := w
  cases a <;> cases b <;> first
    | exact mul_pos m.ppos (sub_pos.mpr m.alt)
    | exact mul_pos m.qpos (sub_pos.mpr m.blt)
    | exact mul_pos m.ppos m.apos

end BinaryModel

private theorem support_from_masses (m : BinaryModel) (D : ℝ) (hD : 0 ≤ D) (half : D < 1/2)
    (active : Word → Prop) (h0 : 0 ≤ constantMass m.A m.B m.C D)
    (h1 : 0 ≤ constantMass m.B m.A m.C D) (ht : 0 ≤ transitionMass m.A m.B m.C D)
    (signs : ∀ w, 0 < prior m.A m.B m.C (D/(1-D)) w ↔ active w) :
    SupportAt m D active := by
  let q := prior m.A m.B m.C (D/(1-D))
  have feasible (w : Word) : 0 ≤ q w := by
    obtain ⟨a,b⟩ := w
    cases a <;> cases b <;> first | exact h0 | exact h1 | exact ht
  have mass : m.A+2*m.C+m.B=1 := by linarith only [m.left_mass,m.right_mass,m.normalized]
  refine ⟨q,?_,feasible,signs,?_⟩
  · rcases eq_or_lt_of_le hD with z | pos
    · subst D
      have eq : q = m.source := by
        funext w
        obtain ⟨a,b⟩ := w
        cases a <;> cases b <;> simp [q,prior,law,BinaryModel.source]
      rw [eq]
      exact lossless_optimal _ (fun w => (m.positive_source w).le)
    · exact optimal_prior _ _ _ _ mass pos half feasible
  · intro t opt
    rcases eq_or_lt_of_le hD with z | pos
    · subst D
      obtain ⟨J,hJ,src,dst,cost,_⟩ := opt
      rw [(zero_cost_marginals _ _ _ hJ src dst cost.le).2]
      funext ⟨a,b⟩
      cases a <;> cases b <;> simp [q,prior,law,BinaryModel.source]
    · exact unique_positive _ _ _ _ mass pos half feasible t opt

private theorem full_support (m : BinaryModel) (D : ℝ) (hD : 0 ≤ D) (half : D < 1/2)
    (p0 : 0 < constantMass m.A m.B m.C D) (p1 : 0 < constantMass m.B m.A m.C D)
    (pt : 0 < transitionMass m.A m.B m.C D) : SupportAt m D (fun _ => True) := by
  apply support_from_masses m D hD half _ p0.le p1.le pt.le
  rintro ⟨a,b⟩
  simp only [iff_true]
  cases a <;> cases b <;> first | exact p0 | exact p1 | exact pt

theorem first_change : FirstChangeStatement := by
  intro m
  refine ⟨?_,?_,?_⟩
  · intro pos
    have rho : m.persistence < 1 := by unfold BinaryModel.persistence; linarith [m.apos,m.bpos]
    have h := positive_first_change m.p m.q m.persistence m.ppos m.qpos m.normalized pos rho
    dsimp only at h
    rw [m.trans_mass, ← m.left_mass, ← m.right_mass] at h
    obtain ⟨dpos,half,atD⟩ := h
    refine ⟨?_,?_⟩
    · intro D hD before
      obtain ⟨h0,h1,ht,_⟩ := atD D hD (before.trans half)
      exact full_support m D hD (before.trans half) h0 h1 (ht.mpr before)
    · obtain ⟨h0,h1,_,hz⟩ := atD _ dpos.le half
      have z := hz.mpr rfl
      apply support_from_masses m _ dpos.le half _ h0.le h1.le (le_of_eq z.symm)
      rintro ⟨a,b⟩
      cases a <;> cases b
      · exact iff_of_true h0 rfl
      · exact iff_of_false (by change ¬ 0 < transitionMass _ _ _ _; rw [z]; exact lt_irrefl _) (by decide)
      · exact iff_of_false (by change ¬ 0 < transitionMass _ _ _ _; rw [z]; exact lt_irrefl _) (by decide)
      · exact iff_of_true h1 rfl
  · intro neg
    have hn : 1-m.a-m.b < 0 := neg
    have disc := NegativeSupport.markov_discriminant m.ppos m.qpos m.balanced
      (show 1 < m.a+m.b by linarith)
    have h := NegativeSupport.negative_distortion (mul_pos m.ppos (sub_pos.mpr m.alt))
      (mul_pos m.qpos (sub_pos.mpr m.blt)) (mul_pos m.ppos m.apos) disc
    obtain ⟨dp,half,before,a,b,t,zA,zB⟩ := h
    refine ⟨?_,?_⟩
    · intro D hD hd
      obtain ⟨pa,pb,pt⟩ := before D hD hd
      exact full_support m D hD (hd.trans half) pa pb pt
    · apply support_from_masses m _ dp.le half _ a b t.le
      let u := (m.C-Real.sqrt (m.C^2-m.A*m.B))/max m.A m.B
      let d := u/(1+u)
      have sa : 0 < constantMass m.A m.B m.C d ↔ m.q < m.p := by
        rw [lt_iff_le_and_ne]
        constructor
        · rintro ⟨_,hn⟩
          by_contra! le
          exact hn ((zA.mpr (by change m.A ≤ m.B; linarith only [m.left_mass,m.right_mass,le])).symm)
        · intro lt
          refine ⟨a,fun eq => ?_⟩
          have le : m.A ≤ m.B := zA.mp eq.symm
          linarith only [m.left_mass,m.right_mass,le,lt]
      have sb : 0 < constantMass m.B m.A m.C d ↔ m.p < m.q := by
        constructor
        · intro hp
          by_contra! le
          exact hp.ne' (zB.mpr (by change m.B ≤ m.A; linarith only [m.left_mass,m.right_mass,le]))
        · intro lt
          refine lt_of_le_of_ne b (fun eq => ?_)
          have le : m.B ≤ m.A := zB.mp eq.symm
          linarith only [m.left_mass,m.right_mass,le,lt]
      rintro ⟨i,j⟩
      have st : 0 < transitionMass m.A m.B m.C d := t
      cases i <;> cases j
      · change (0 < constantMass m.A m.B m.C d) ↔ _
        simpa using sa
      · change (0 < transitionMass m.A m.B m.C d) ↔ _
        exact iff_of_true st (Or.inl (by decide))
      · change (0 < transitionMass m.A m.B m.C d) ↔ _
        exact iff_of_true st (Or.inl (by decide))
      · change (0 < constantMass m.B m.A m.C d) ↔ _
        simpa using sb
  · intro hz D hD hd
    have c : m.C = m.p*m.q := by simpa [hz] using m.trans_mass.symm
    obtain ⟨_,_,_,_,_,_,pa,pt,pb⟩ := independent_full_support m.p m.q D m.ppos m.qpos m.normalized hD hd
    rw [← c, ← m.left_mass, ← m.right_mass] at pa pt pb
    apply full_support m D hD _ pa pb pt
    linarith only [lt_of_lt_of_le hd (min_le_left _ _),lt_of_lt_of_le hd (min_le_right _ _),m.normalized]

end BlockHierarchy
