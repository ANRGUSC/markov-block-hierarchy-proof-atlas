import BlockHierarchy.Cut.Existence
import Mathlib.Topology.Maps.Proper.Basic

open scoped BigOperators
open Set
namespace BlockHierarchy.Cut

/-- The canonical score varies continuously with the distortion multiplier
even if the chosen optimal probability law jumps at a support change. -/
theorem continuous_optimal_score {X : Type*} [Fintype X]
    {P : X → ℝ} (hp : ∀ x, 0 < P x) (d : X → X → ℕ)
    (q : ℝ → X → ℝ) (hq : ∀ t, Optimal P t d (q t)) (x : X) :
    Continuous (fun t => score t d (q t) x) := by
  classical
  let S := stdSimplex ℝ X
  let G (w : ℝ × S) (y : X) := score w.1 d w.2.val y
  let F (w : ℝ × S) := mean P (G w)
  have gc (y : X) : Continuous (fun w => G w y) := by
    have cz : Continuous (fun w : ℝ × S => Z w.1 d w.2.val y) := by
      have term (a : X) : Continuous (fun w : ℝ × S => w.2.val a * Real.exp (-w.1*(d y a : ℝ))) :=
        ((continuous_apply a).comp (continuous_subtype_val.comp continuous_snd)).mul
          (Real.continuous_exp.comp (continuous_fst.neg.mul continuous_const))
      have part (s : Finset X) : Continuous (fun w : ℝ × S =>
          ∑ a ∈ s, w.2.val a * Real.exp (-w.1*(d y a : ℝ))) := by
        induction s using Finset.induction_on with
        | empty => simp only [Finset.sum_empty]; exact continuous_const
        | @insert a s ha ih => simp only [Finset.sum_insert ha]; exact (term a).add ih
      exact part Finset.univ
    exact (cz.log (fun w => (Z_pos w.1 d w.2.property y).ne')).neg
  have fc : Continuous F := by
    have part (s : Finset X) : Continuous (fun w => ∑ y ∈ s, P y*G w y) := by
      induction s using Finset.induction_on with
      | empty => simp only [Finset.sum_empty]; exact continuous_const
      | @insert a s ha ih =>
        simp only [Finset.sum_insert ha]
        exact (continuous_const.mul (gc a)).add ih
    exact part Finset.univ
  let graph : Set (ℝ × S) := {w | ∀ u : S, F w ≤ F (w.1,u)}
  have graph_closed : IsClosed graph := by
    change IsClosed {w : ℝ × S | ∀ u : S, F w ≤ F (w.1,u)}
    simp only [ofPred_forall]
    exact isClosed_iInter fun u => isClosed_le fc
      (fc.comp (continuous_fst.prodMk (continuous_const (y := u))))
  apply continuous_iff_isClosed.2
  intro C hc
  let T := graph ∩ (fun w => G w x) ⁻¹' C
  have closed : IsClosed (Prod.fst '' T) :=
    isClosedMap_fst_of_compactSpace T (graph_closed.inter (hc.preimage (gc x)))
  have eq : (fun t => score t d (q t) x) ⁻¹' C = Prod.fst '' T := by
    ext t
    constructor
    · intro ht
      let u : S := ⟨q t,(hq t).1⟩
      exact ⟨(t,u),⟨fun v => (hq t).2 v v.property,ht⟩,rfl⟩
    · rintro ⟨⟨_,u⟩, ⟨hu, inC⟩, rfl⟩
      have opt : Optimal P _ d u.val := ⟨u.property,fun v hv => hu ⟨v,hv⟩⟩
      have same := congrFun (optimal_Z_eq hp (hq _) opt) x
      change -Real.log _ ∈ C
      rw [same]
      exact inC
  rwa [eq]


/-- Finite-block normalized score standard deviation as a function of the multiplier. -/
theorem continuous_optimal_sd {X : Type*} [Fintype X]
    {P : X → ℝ} (hp : ∀ x, 0 < P x) (d : X → X → ℕ) (k : ℕ)
    (q : ℝ → X → ℝ) (hq : ∀ t, Optimal P t d (q t)) :
    Continuous (fun t => Real.sqrt (variance P (score t d (q t))) / Real.sqrt k) := by
  classical
  let f (t : ℝ) := score t d (q t)
  have fc (y : X) : Continuous (fun t => f t y) := continuous_optimal_score hp d q hq y
  have expected (g : ℝ → X → ℝ) (h : ∀ y, Continuous (fun t => g t y)) :
      Continuous (fun t => mean P (g t)) := by
    have part (s : Finset X) : Continuous (fun t => ∑ y ∈ s, P y*g t y) := by
      induction s using Finset.induction_on with
      | empty => simp only [Finset.sum_empty]; exact continuous_const
      | @insert a s ha ih => simp only [Finset.sum_insert ha]; exact (continuous_const.mul (h a)).add ih
    exact part Finset.univ
  have vc : Continuous (fun t => variance P (f t)) :=
    expected (fun t y => (f t y-mean P (f t))^2) (fun y => ((fc y).sub (expected f fc)).pow 2)
  exact (Real.continuous_sqrt.comp vc).div_const _

#print axioms continuous_optimal_sd
end BlockHierarchy.Cut
