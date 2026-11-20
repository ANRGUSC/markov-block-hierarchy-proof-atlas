import BlockHierarchy.Three.FullPoint
import BlockHierarchy.Three.MiddleBranch
import BlockHierarchy.Three.ConstantBranch

open scoped BigOperators
namespace BlockHierarchy.Three

private theorem active_six {q : Word → ℝ} (h : ∀ y, 0 < q y ↔ flips y < 2) : supportSize q=6 := by
  unfold supportSize
  rw [Finset.filter_congr (fun y _ => h y)]
  decide

private theorem active_eight {q : Word → ℝ} (h : ∀ y, 0 < q y) : supportSize q=8 := by
  unfold supportSize
  have e : Finset.univ.filter (fun y => 0 < q y) = Finset.univ := Finset.filter_true_of_mem (fun y _ => h y)
  rw [e]; decide

private theorem constant_profile : (∀ y, prior 1 0 0 y=(if flips y=0 then 1/2 else 0)) ∧
    supportSize (prior 1 0 0)=2 := by
  have profile (y : Word) : prior 1 0 0 y=(if flips y=0 then 1/2 else 0) := by
    obtain ⟨i,j,k⟩ := y
    cases i <;> cases j <;> cases k <;> norm_num [prior,classValue,flips]
  refine ⟨profile,?_⟩
  unfold supportSize
  have e (y : Word) : 0 < prior 1 0 0 y ↔ flips y=0 := by
    rw [profile]; split <;> simp_all
  rw [Finset.filter_congr (fun y _ => e y)]
  decide

theorem three_symbol : ThreeSymbolStatement := by
  intro p hp ph
  dsimp only
  obtain ⟨hd,_,_,hfirst,h12,h1,_,_⟩ := thresholds hp ph
  obtain ⟨e1,e2,e3⟩ := endpoint_costs hp ph
  have firstlt := middleCost_strict hp ph hfirst.le h12
  have secondlt := constantCost_strict hp ph (hfirst.trans h12).le h1
  have eqD : constantCost p (secondU p)=3*secondD p := by unfold secondD; ring
  refine ⟨⟨hd,by linarith,by linarith,hfirst,h12,h1⟩,
    fun _ _ ha hab => ⟨middleCost_strict hp ph ha hab,constantCost_strict hp ph ha hab⟩,
    fun _ _ hu => ⟨middle_cubic hu,constant_cubic hu⟩,?_,?_,?_⟩
  · intro D hD upper
    have support := (full_support hp ph upper).2
    refine ⟨support,?_,full_paper_point hp ph hD upper⟩
    by_cases h : D < criticalD p
    · rw [if_pos h]
      exact active_eight (fun y => (support y).mpr (Or.inr h))
    · rw [if_neg h]
      exact active_six (fun y => by simpa [h] using support y)
  · intro D lower upper
    obtain ⟨u,hu,eq,norm,supp,opt,rate,var⟩ := middle_branch hp ph lower upper
    have inv := middle_inverse hp ph lower upper
    have up := hfirst.trans hu.1
    have uh := hu.2.trans h1
    have mpos : 0 < 1-p := by linarith
    have ppos : 0 < 1+p := by linarith
    have hS : (1-p)^2+2*p*(1-p)=(1-p)*(1+p) := by ring
    have a : (1-p)^2*middleH u/((1-p)^2+2*p*(1-p))=(1-p)*middleH u/(1+p) := by
      rw [hS]; field_simp [mpos.ne',ppos.ne']
    have b : 2*p*(1-p)*middleH u/(2*((1-p)^2+2*p*(1-p)))=p*middleH u/(1+p) := by
      rw [hS]; field_simp [mpos.ne',ppos.ne']
    have Hpos : 0 < middleH u := by unfold middleH; positivity
    have bpos : 0 < beta u := by unfold beta; positivity
    have hz (x : Word) : 0 < sixNormal p u x := by
      unfold sixNormal classValue; split <;> split <;> positivity
    have cap := (middle_cost hp ph up).trans eq
    refine ⟨u,hu,eq,fun v hv he => inv.unique ⟨hv,he⟩ ⟨hu,eq⟩,supp,active_six supp,?_⟩
    rw [a,b]
    refine ⟨norm,cap,opt,?_,rate,var⟩
    exact unique_gibbs hp ph up uh hz (fun y => (middle_columns hp ph hu.1.le uh y).1) opt cap
  · intro D lower upper
    obtain ⟨u,hu,eq,norm,opt,rate,var⟩ := constant_branch hp ph lower upper
    have inv := constant_inverse hp ph lower upper
    have up := (hfirst.trans h12).trans_le hu.1
    have ha : 0 < alpha u := by unfold alpha; positivity
    have hb : 0 < beta u := by unfold beta; positivity
    have hz (x : Word) : 0 < twoNormal u x := by
      unfold twoNormal classValue; split <;> split <;> assumption
    have cap := (constant_cost p up).trans eq
    refine ⟨u,hu,eq,fun v hv he => inv.unique ⟨hv,he⟩ ⟨hu,eq⟩,
      constant_profile.1,constant_profile.2,?_,var⟩
    refine ⟨norm,cap,opt,?_,rate,class_tilt ..⟩
    exact unique_gibbs hp ph up hu.2 hz (fun y => (constant_columns hp ph hu.1 hu.2 y).1) opt cap

#print axioms three_symbol

end BlockHierarchy.Three
