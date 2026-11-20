import BlockHierarchy.Three.Entropy
import BlockHierarchy.Three.Unique

open scoped BigOperators
namespace BlockHierarchy.Four

open BlockHierarchy
abbrev W4 := Bool × Three.Word
noncomputable def P4 (p : ℝ) (x : W4) := Three.step p x.1 x.2.1 * Three.markov p x.2
def d4 (x y : W4) := (if x.1=y.1 then 0 else 1)+Three.hamming x.2 y.2

theorem source_entropy : ∀ p : ℝ, 0 < p → p < 1/2 → -mean (P4 p) (fun x => logTwo (P4 p x)) = 1+3*Three.binaryEntropy p := by
  intro p hp ph
  have pos : 0 < 1-p := by linarith
  have trans (a b : Bool) : 0 < Three.step p a b := by unfold Three.step; split <;> assumption
  have term (a : Bool) (x : Three.Word) : logTwo (P4 p (a,x)) =
      logTwo (Three.step p a x.1)+logTwo (Three.markov p x) := by
    unfold P4 logTwo
    rw [Real.log_mul (trans a x.1).ne' (Three.source_pos hp ph x).ne',add_div]
  have one (x : Three.Word) : (∑ a : Bool, P4 p (a,x)*logTwo (P4 p (a,x))) =
      (Three.markov p x)*logTwo (Three.markov p x)-Three.markov p x*Three.binaryEntropy p := by
    simp_rw [term]
    rw [Fintype.sum_bool]
    unfold P4 Three.binaryEntropy
    cases h : x.1 <;> simp [Three.step,h] <;> ring
  have val := (Three.source_moments hp ph).1
  unfold mean at val ⊢
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  simp_rw [one,Finset.sum_sub_distrib,← Finset.sum_mul,Three.markov_mass,one_mul]
  linarith only [val]

theorem source_varentropy : ∀ p : ℝ, 0 < p → p < 1/2 → variance (P4 p) (fun x => -logTwo (P4 p x)) = 3*Three.nu p := by
  intro p hp hhalf
  have m : 0 < 1-p := by linarith
  let H := Three.binaryEntropy p
  let I := fun x => -logTwo (Three.markov p x)
  let M := mean (Three.markov p) I
  have stepP (i j : Bool) : 0 < Three.step p i j := by unfold Three.step; split <;> assumption
  have lp (b : Bool) (x : Three.Word) : -logTwo (P4 p (b,x)) = -logTwo (Three.step p b x.1)+I x := by
    unfold P4 logTwo I
    rw [Real.log_mul (stepP _ _).ne' (Three.source_pos hp hhalf x).ne',add_div]
    change -(Real.log (Three.step p b x.1)/Real.log 2+Real.log (Three.markov p x)/Real.log 2)=_
    unfold logTwo
    ring
  have avgBit (x : Three.Word) :
      (∑ b : Bool, P4 p (b,x)*(-logTwo (P4 p (b,x)))) = Three.markov p x*I x+Three.markov p x*H := by
    simp only [Fintype.sum_bool,lp]
    cases e : x.1 <;> simp [P4,Three.step,e,H,Three.binaryEntropy] <;> ring
  have mean4 : mean (P4 p) (fun x => -logTwo (P4 p x))=M+H := by
    unfold mean
    rw [Fintype.sum_prod_type,Finset.sum_comm]
    simp_rw [avgBit]
    rw [Finset.sum_add_distrib,← Finset.sum_mul,Three.markov_mass,one_mul]
    rfl
  have rat : logTwo ((1-p)/p)=logTwo (1-p)-logTwo p := by
    unfold logTwo; rw [Real.log_div m.ne' hp.ne',sub_div]
  have second (x : Three.Word) :
      (∑ b : Bool, P4 p (b,x)*(-logTwo (P4 p (b,x))-(M+H))^2) =
        Three.markov p x*(I x-M)^2+Three.markov p x*Three.nu p := by
    simp only [Fintype.sum_bool,lp,Three.nu,rat]
    cases e : x.1 <;> simp [P4,Three.step,e,H,Three.binaryEntropy] <;> ring
  unfold variance
  rw [mean4,Fintype.sum_prod_type,Finset.sum_comm]
  simp_rw [second]
  rw [Finset.sum_add_distrib,← Finset.sum_mul,Three.markov_mass,one_mul]
  change variance (Three.markov p) I + Three.nu p = _
  rw [(Three.source_moments hp hhalf).2]
  ring

theorem hamming_inverse : ∀ (u : ℝ) (x z : W4), (∑ y : W4, (-u)^d4 x y*u^d4 y z) = if x=z then (1-u^2)^4 else 0 := by
  intro u ⟨a,x⟩ ⟨b,z⟩
  rw [Fintype.sum_prod_type]
  have part (c : Bool) : (∑ y : Three.Word, (-u)^d4 (a,x) (c,y)*u^d4 (c,y) (b,z)) =
      ((-u)^(if a=c then 0 else 1 : ℕ)*u^(if c=b then 0 else 1 : ℕ))*
        (if x=z then (1-u^2)^3 else 0) := by
    rw [← Three.cube_inverse x z,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    simp only [d4,pow_add]
    ring
  simp_rw [part]
  rw [Fintype.sum_bool]
  cases a <;> cases b <;> by_cases e : x=z <;> simp [e] <;> ring

end BlockHierarchy.Four
