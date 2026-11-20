import BlockHierarchy.VarianceLimit.EndpointDeletion
import BlockHierarchy.VarianceLimit.EndpointSymmetry

namespace BlockHierarchy.VarianceLimit
open Cut

/-- A single choice of the endpoint correlations supplies both gain estimates.
Index n of b is the correlation for a physical block of length n+1. -/
theorem exists_endpoint_profile {p τ : ℝ} (hp : 0<p) (ph : p<1) :
    ∃ b : ℕ → ℝ,
      (∀ n, τ*(1-b n)/2 ≤ totalCost p τ (n+1)-totalCost p τ n) ∧
      ∀ i j, ((1-2*p)*b i*b j)^2/2 ≤
        totalCost p τ (i+1)+totalCost p τ (j+1)-totalCost p τ ((i+1)+(j+1)) := by
  classical
  choose q opt comp rev using (fun n => symmetric_choice hp ph n (canonical_optimal p τ n))
  let b (n : ℕ) := endpointCorrelation p τ n (q n) (firstSpin n)
  refine ⟨b,fun n => endpoint_increment hp ph n (opt n),?_⟩
  intro i j
  let k := (j+1)+i
  let e : Word i × Word j ≃ Word k := concatEquiv (j+1) (i+1)
  let u := fun w => canonicalPrior p τ k (e w)
  let d := jointDistance i j
  let P := adjacent p i j
  have hd : (fun x y => distance k (e x) (e y))=d := by funext x y; exact concat_distance i j x y
  have hP : (fun w => mass p k (e w))=P := by funext w; exact concat_mass p i j w
  have J : Optimal P τ d u := by rw [←hP,←hd]; exact optimal_pull e (canonical_optimal p τ k)
  have value : mean P (score τ d u)=totalCost p τ (k+1) := by
    rw [←hP,←hd,show score τ (fun x y => distance k (e x) (e y)) u =
        (fun w => blockScore p τ k (e w)) from funext (score_pull e τ (distance k) (canonicalPrior p τ k))]
    exact mean_pull e _ _
  have raw := gain_lower_adjacent hp ph (opt i) (opt j) J
    (symmetric_centered (comp i) (rev i)).1 (symmetric_centered (comp j) (rev j)).2
  rw [symmetric_endpoints (rev i),totalCost_optimal i (opt i),totalCost_optimal j (opt j),value] at raw
  rw [show i+1+(j+1)=k+1 by dsimp [k]; omega]
  exact raw

#print axioms exists_endpoint_profile
end BlockHierarchy.VarianceLimit
