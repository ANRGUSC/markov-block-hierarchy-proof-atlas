import BlockHierarchy.RecurrenceStatement

open Set
open scoped BigOperators
namespace BlockHierarchy.Recurrence

private theorem continuous_expectation {T : Type*} [TopologicalSpace T]
    (p : ℝ) (n : ℕ) (a : Bool) (f : T → List Bool → Bool → ℝ)
    (hf : ∀ xs b, Continuous (fun t => f t xs b)) :
    Continuous (fun t => expectFrom p a n (f t)) := by
  induction n generalizing a f with
  | zero => exact hf [] a
  | succ n ih =>
    change Continuous (fun t => ∑ b : Bool, Three.step p a b *
      expectFrom p b n (fun xs q => f t (a::xs) q))
    apply continuous_finsetSum
    intro b _
    exact continuous_const.mul (ih b _ (fun xs q => hf (a::xs) q))

abbrev InteriorDistortion := Ioo (0:ℝ) (1/2)

theorem continuous_inverse_mass (p : ℝ) (ys : List Bool) :
    Continuous (fun t : InteriorDistortion => mass p (1-2*t.val) ys) := by
  have bit (x y : Bool) : Continuous (fun t : InteriorDistortion => invWeight (1-2*t.val) x y) := by
    unfold invWeight
    fun_prop (disch := intro t; have hi := t.property.2; linarith)
  have word (xs zs : List Bool) :
      Continuous (fun t : InteriorDistortion => wordWeight (invWeight (1-2*t.val)) xs zs) := by
    induction xs generalizing zs with
    | nil => cases zs <;> exact continuous_const
    | cons x xs ih =>
      cases zs with
      | nil => exact continuous_const
      | cons y zs => exact (bit x y).mul (ih zs)
  unfold mass markovExpect
  apply Continuous.div_const
  apply continuous_finsetSum
  intro a _
  exact continuous_expectation p ys.length a _ (fun xs _ => word xs ys)

theorem finite_feasibility_closed (p : ℝ) (n : ℕ) :
    IsClosed {t : InteriorDistortion | InverseNonnegative p (1-2*t.val) n} := by
  change IsClosed {t : InteriorDistortion | ∀ ys : List Bool, ∀ _ : ys.length=n, 0≤mass p (1-2*t.val) ys}
  simp only [setOf_forall]
  apply isClosed_iInter
  intro ys
  apply isClosed_iInter
  intro _
  exact isClosed_le continuous_const (continuous_inverse_mass p ys)

end BlockHierarchy.Recurrence
