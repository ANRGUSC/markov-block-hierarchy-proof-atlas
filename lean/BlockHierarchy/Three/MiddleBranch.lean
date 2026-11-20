import BlockHierarchy.Three.MiddleColumns
import BlockHierarchy.Three.OperatingPoint
import BlockHierarchy.Three.Inverse

open scoped BigOperators
namespace BlockHierarchy.Three

theorem middle_cost {p u : ℝ} (hp : 0 < p) (half : p < 1/2) (hu : 0 < u) :
    Channel.cost (fun x y => (hamming x y : ℝ))
      (FiniteRD.joint (markov p) (sixNormal p u) (sixPrior p u) hamming u)=middleCost p u := by
  have Hpos : 0 < middleH u := by unfold middleH; positivity
  have bpos : 0 < beta u := by unfold beta; positivity
  have mpos : 0 < 1-p := by linarith
  have ppos : 0 < 1+p := by positivity
  let w := pairWeight p u
  let M := fun a => betaCost u+(alphaCost u-betaCost u)*a
  let z0 := (1-p)*middleH u/(1+p)
  let z1 := p*middleH u/(1+p)
  have val (x : Word) : weightedDistance (sixPrior p u) u x/sixNormal p u x =
      classValue (M (1-2*w)/z0) (M w/z1) (betaCost u/beta u) x := by
    rw [sixPrior,class_distance,show 1-2*pairWeight p u+2*pairWeight p u+0=1 by ring]
    obtain ⟨i,j,k⟩ := x
    cases i <;> cases j <;> cases k <;> simp [sixNormal,classValue,M,w,z0,z1]
  rw [operating_cost]
  simp_rw [val]
  rw [class_expectation]
  calc
    _ = (1-p^2)/middleH u*(alphaCost u+2*betaCost u)+p^2*(betaCost u/beta u) := by
      dsimp [M,z0,z1]
      field_simp [hp.ne',mpos.ne',ppos.ne',Hpos.ne',bpos.ne']
      <;> ring
    _ = middleCost p u := by
      unfold middleCost middleH alphaCost betaCost beta
      field_simp [show 0 < 1+u by positivity,show 0 < 1+u+u^2 by positivity,
        show 0 < u+u^2 by positivity]
      <;> ring

theorem middle_branch {p D : ℝ} (hp : 0 < p) (half : p < 1/2)
    (lower : criticalD p < D) (upper : D < secondD p) :
    ∃ u, u ∈ Set.Ioo (firstU p) (secondU p) ∧ middleCost p u=3*D ∧
      let q := sixPrior p u
      let z := sixNormal p u
      let J := FiniteRD.joint (markov p) z q hamming u
      (∀ x, normalizer q u x=z x) ∧ (∀ y, 0 < q y ↔ flips y < 2) ∧
      FiniteRD.Optimal (markov p) q hamming J (3*D) ∧
      Channel.info (markov p) q J/Real.log 2 =
        3*D*logTwo u-classMean p (logTwo ((1-p)*middleH u/(1+p)))
          (logTwo (p*middleH u/(1+p))) (logTwo (beta u)) ∧
      tilted p (3*D) u z = classVariance p (-logTwo ((1-p)*middleH u/(1+p)))
        (-logTwo (p*middleH u/(1+p))) (-logTwo (beta u)) := by
  obtain ⟨u,⟨hu,eq⟩,_⟩ := middle_inverse hp half lower upper
  obtain ⟨_,_,_,hf,_,h1,_,_⟩ := thresholds hp half
  have up := hf.trans hu.1
  have uh := hu.2.trans h1
  obtain ⟨wpos,worder⟩ := six_weights hp half up.le hu.2
  have wz := wpos.trans worder
  have support (y : Word) : 0 < sixPrior p u y ↔ flips y < 2 := by
    obtain ⟨i,j,k⟩ := y
    cases i <;> cases j <;> cases k <;>
      norm_num [sixPrior,prior,classValue,flips] <;> first | linarith | positivity
  have hq (y : Word) : 0 ≤ sixPrior p u y := by
    obtain ⟨i,j,k⟩ := y
    cases i <;> cases j <;> cases k <;>
      norm_num [sixPrior,prior,classValue] <;> first | linarith | positivity
  have Hpos : 0 < middleH u := by unfold middleH; positivity
  have bpos : 0 < beta u := by unfold beta; positivity
  have mpos : 0 < 1-p := by linarith
  have hz (x : Word) : 0 < sixNormal p u x := by
    unfold sixNormal classValue
    split <;> split <;> positivity
  have norm := six_normalizer hp up.le uh
  have cert := FiniteRD.certificate (d := hamming) (source_pos hp half) hz hq up uh.le
    norm (middle_columns hp half hu.1.le uh) ((middle_cost hp half up).trans eq)
  exact ⟨u,hu,eq,norm,support,cert.1,cert.2.trans (by rw [sixNormal,class_log_mean]),class_tilt ..⟩

end BlockHierarchy.Three
