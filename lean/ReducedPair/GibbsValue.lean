import ReducedPair.RateStatement

open scoped BigOperators
namespace BlockHierarchy
open PairChannel

theorem gibbs_information {P q Z : Word → ℝ} {D u : ℝ}
    (point : GibbsPoint P q D u Z) (hu : 0 < u) (hp : ∀ x, 0 < P x)
    (hz : ∀ x, 0 < Z x)
    (cost : jointCost (fun x y => q y*(P x*u^hamming x y/Z x)) = 2*D) :
    Channel.info P q (fun x y => q y*(P x*u^hamming x y/Z x)) =
      2*D*Real.log u - mean P (fun x => Real.log (Z x)) := by
  let J (x y : Word) := q y*(P x*u^hamming x y/Z x)
  have row (x : Word) : ∑ y, J x y = P x := point.2.2.1 x
  have term (x y : Word) : J x y*(Real.log (J x y)-Real.log (P x)-Real.log (q y)) =
      (J x y*(hamming x y : ℝ))*Real.log u - J x y*Real.log (Z x) := by
    by_cases e : q y = 0
    · simp [J,e]
    · have pw := pow_pos hu (hamming x y)
      have pk := mul_pos (hp x) pw
      change J x y*(Real.log (q y*(P x*u^hamming x y/Z x))-Real.log (P x)-Real.log (q y)) = _
      rw [Real.log_mul e (div_pos pk (hz x)).ne',Real.log_div pk.ne' (hz x).ne',
        Real.log_mul (hp x).ne' pw.ne',Real.log_pow]
      ring
  change Channel.info P q J = _
  unfold Channel.info
  simp_rw [term]
  simp only [Finset.sum_sub_distrib, ← Finset.sum_mul,row]
  change jointCost J*Real.log u - mean P (fun x => Real.log (Z x)) = _
  rw [show jointCost J = 2*D from cost]

theorem gibbs_rate {P q Z : Word → ℝ} {D u : ℝ} (point : GibbsPoint P q D u Z)
    (hu : 0 < u) (hp : ∀ x, 0 < P x) (hz : ∀ x, 0 < Z x)
    (cost : jointCost (fun x y => q y*(P x*u^hamming x y/Z x)) = 2*D) :
    RateAt P D ((2*D*Real.log u - mean P (fun x => Real.log (Z x)))/Real.log 2) :=
  ⟨q,_,point.2,congrArg (fun v => v/Real.log 2) (gibbs_information point hu hp hz cost)⟩

end BlockHierarchy
