import BlockHierarchy.Varentropy.Covariance

open scoped BigOperators
namespace BlockHierarchy.Varentropy

private theorem affine_cov {X : Type*} [Fintype X] (P f g : X → ℝ)
    (mass : ∑ i, P i=1) (a b : ℝ) :
    covariance P f (fun i => a+b*g i)=b*covariance P f g := by
  have avg : mean P (fun i => a+b*g i)=a+b*mean P g := by
    unfold mean
    simp only [mul_add,Finset.sum_add_distrib,←Finset.sum_mul,mass,one_mul]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold covariance
  rw [avg,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The source of a prefix observable can be any finite history. Only its terminal
state is relevant for predicting the edge h transitions later. -/
noncomputable def extendedLaw {X : Type*} (m : BinaryModel) (P : X → ℝ) (last : X → Bool)
    (h : ℕ) (w : X × Bits (h+1)) := P w.1 * tailLaw m (last w.1) (h+1) w.2

theorem prefix_edge_covariance {X : Type*} [Fintype X] (m : BinaryModel)
    (P f : X → ℝ) (last : X → Bool) (mass : ∑ i, P i=1) (h : ℕ) :
    covariance (extendedLaw m P last h) (fun w => f w.1)
        (fun w => lastEdge m (last w.1) h w.2) =
      m.persistence^h * covariance P f (fun x => rowReward m (last x)) := by
  let Q := extendedLaw m P last h
  let G (w : X × Bits (h+1)) := lastEdge m (last w.1) h w.2
  let g (x : X) := iterate m (rowReward m) h (last x)
  have parent : mean Q (fun w => f w.1)=mean P f := by
    unfold mean
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    change ∑ w, (P x*tailLaw m (last x) (h+1) w)*f x=P x*f x
    simp_rw [mul_right_comm (P x) _ (f x),← Finset.mul_sum,tail_mass,mul_one]
  have future : mean Q G=mean P g := by
    unfold mean
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    change ∑ w, (P x*tailLaw m (last x) (h+1) w)*lastEdge m (last x) h w=P x*g x
    simp only [mul_assoc,← Finset.mul_sum,last_edge_conditional,g]
  have collapse : covariance Q (fun w => f w.1) G=covariance P f g := by
    unfold covariance
    rw [parent,future,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    let c := P x*(f x-mean P f)
    let M := mean P g
    have point (w : Bits (h+1)) : Q (x,w)*(f x-mean P f)*(G (x,w)-M) =
        c*(tailLaw m (last x) (h+1) w*lastEdge m (last x) h w)-
          (c*M)*tailLaw m (last x) (h+1) w := by dsimp [Q,extendedLaw,G,c]; ring
    change ∑ w, Q (x,w)*(f x-mean P f)*(G (x,w)-M)=c*(g x-M)
    simp_rw [point,Finset.sum_sub_distrib,← Finset.mul_sum,tail_mass,last_edge_conditional]
    dsimp [g]; ring
  let μ := mean (pi m) (rowReward m)
  have form : g=fun x => (1-m.persistence^h)*μ + m.persistence^h*rowReward m (last x) := by
    funext x; dsimp only [g]; rw [iterate_formula]; dsimp [μ]; ring
  change covariance Q (fun w => f w.1) G=_
  rw [collapse,form,affine_cov _ _ _ mass]

theorem initial_lag (m : BinaryModel) (h : ℕ) :
    covariance (pathLaw m (h+1)) (fun w => B m w.1)
      (fun w => lastEdge m w.1 h w.2)=m.persistence^h*kappa m := by
  have base := prefix_edge_covariance m (pi m) (B m) id (pi_mass m) 0
  change kappa m=m.persistence^0*covariance (pi m) (B m) (rowReward m) at base
  rw [pow_zero,one_mul] at base
  rw [base]
  exact prefix_edge_covariance m (pi m) (B m) id (pi_mass m) h

private theorem covariance_assoc {X Y T : Type*} [Fintype X] [Fintype Y] [Fintype T]
    (P f g : (X × Y) × T → ℝ) :
    covariance (fun z : X × Y × T => P ((z.1,z.2.1),z.2.2))
      (fun z => f ((z.1,z.2.1),z.2.2)) (fun z => g ((z.1,z.2.1),z.2.2))=covariance P f g := by
  unfold covariance mean
  simp only [Fintype.sum_prod_type]

private noncomputable def edgeLaw (m : BinaryModel) (e : Bool × Bool) :=
  pi m e.1 * transition m e.1 e.2

private theorem edge_lag_aux (m : BinaryModel) (h : ℕ) :
    covariance (pathLaw m (h+2)) (fun w => A m w.1 w.2.1)
      (fun w => lastEdge m w.2.1 h w.2.2)=
      m.persistence^h*covariance (edgeLaw m) (fun e => A m e.1 e.2) (fun e => rowReward m e.2) := by
  have em : ∑ e, edgeLaw m e=1 := by
    rw [Fintype.sum_prod_type]
    unfold edgeLaw
    simp only [← Finset.mul_sum]
    have row (x : Bool) : ∑ y, transition m x y=1 := by simpa only [step,mul_one] using step_const m 1 x
    simp only [row,mul_one,pi_mass]
  let Q := extendedLaw m (edgeLaw m) Prod.snd h
  let f := fun w : (Bool × Bool) × Bits (h+1) => A m w.1.1 w.1.2
  let g := fun w : (Bool × Bool) × Bits (h+1) => lastEdge m w.1.2 h w.2
  have eQ : pathLaw m (h+2)=(fun z : Bits (h+3) => Q ((z.1,z.2.1),z.2.2)) := by
    funext z
    change pi m z.1*(transition m z.1 z.2.1*tailLaw m z.2.1 (h+1) z.2.2)=
      (pi m z.1*transition m z.1 z.2.1)*tailLaw m z.2.1 (h+1) z.2.2
    ring
  rw [eQ]
  exact (covariance_assoc (X := Bool) (Y := Bool) (T := Bits (h+1)) Q f g).trans
    (prefix_edge_covariance (X := Bool × Bool) m (edgeLaw m)
      (fun e => A m e.1 e.2) Prod.snd em h)

theorem edge_lag (m : BinaryModel) (h : ℕ) :
    covariance (pathLaw m (h+2)) (fun w => A m w.1 w.2.1)
      (fun w => lastEdge m w.2.1 h w.2.2)=m.persistence^h*gamma m := by
  have base := edge_lag_aux m 0
  change gamma m=m.persistence^0*_ at base
  rw [pow_zero,one_mul] at base
  rw [base]
  exact edge_lag_aux m h

#print axioms prefix_edge_covariance
#print axioms initial_lag
#print axioms edge_lag
end BlockHierarchy.Varentropy
