import BlockHierarchy.Converse.Paths
import BlockHierarchy.Converse.Gaussian

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
namespace BlockHierarchy.Converse
open Varentropy

def prefixAt (w : ℕ → Bool) (i : ℕ) : (n : ℕ) → Bits n
  | 0 => ()
  | n+1 => (w i,prefixAt w (i+1) n)

def bitAt : (n : ℕ) → Bits n → ℕ → Bool
  | 0, _, _ => false
  | _+1, w, 0 => w.1
  | n+1, w, k+1 => bitAt n w.2 k

private theorem prefix_iff (w : ℕ → Bool) (i n : ℕ) (x : Bits n) :
    prefixAt w i n=x ↔ ∀ j<n, w (i+j)=bitAt n x j := by
  induction n generalizing i with
  | zero => cases x; simp [prefixAt] <;> rfl
  | succ n ih =>
    obtain ⟨b,x⟩ := x
    change (w i,prefixAt w (i+1) n)=(b,x) ↔ _
    rw [Prod.mk.injEq,ih]
    constructor
    · rintro ⟨first,rest⟩ j hj
      cases j with
      | zero => simpa [bitAt] using first
      | succ j =>
        simpa [bitAt,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using rest j (by omega)
    · intro h
      refine ⟨by simpa [bitAt] using h 0 (by omega),?_⟩
      intro j hj
      simpa [bitAt,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h (j+1) (by omega)

theorem prefix_event (n : ℕ) (x : Bits n) :
    {w : ℕ → Bool | prefixAt w 0 n=x} =
    Set.pi (Finset.range n : Set ℕ) (fun j => ({bitAt n x j} : Set Bool)) := by
  ext w
  simpa [Set.mem_pi,Finset.mem_range] using prefix_iff w 0 n x

private theorem coin_single (p : Set.Icc (0:ℝ) 1) (b : Bool) :
    (coin p).real {b} = if b then (p:ℝ) else 1-p := by
  cases b <;> simp [coin,bernoulliMeasure_real_apply p (measurableSet_singleton _)]

private theorem iid_product (p : ℝ) (n : ℕ) (x : Bits n) :
    (∏ j ∈ Finset.range n, if bitAt n x j then p else 1-p)=iidFlips p n x := by
  induction n with
  | zero => simp [iidFlips]
  | succ n ih =>
    obtain ⟨b,x⟩ := x
    rw [Finset.prod_range_succ']
    simp only [bitAt,iidFlips]
    exact (congrArg (fun z : ℝ => z*(if b then p else 1-p)) (ih x)).trans (mul_comm _ _)

/-- The probability of each exact finite prefix of the CLT's infinite stream
is precisely the finite Bernoulli product used for Markov paths. -/
theorem cylinder_probability (p : Set.Icc (0:ℝ) 1) (n : ℕ) (x : Bits n) :
    (flipsLaw p).real {w | prefixAt w 0 n=x} = iidFlips p n x := by
  rw [prefix_event]
  unfold flipsLaw Measure.real
  rw [Measure.infinitePi_pi _ (fun i _ => measurableSet_singleton _),ENNReal.toReal_prod]
  change (∏ j ∈ Finset.range n, (coin p).real {bitAt n x j})=_
  simp_rw [coin_single]
  exact iid_product _ _ _

#print axioms cylinder_probability
end BlockHierarchy.Converse
