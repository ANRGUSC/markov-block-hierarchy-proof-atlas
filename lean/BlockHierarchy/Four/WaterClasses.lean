import BlockHierarchy.Four.WaterEndpoint
import BlockHierarchy.Four.ParityOptimality

open scoped BigOperators
namespace BlockHierarchy.Four.WaterClasses
open WaterFilling

noncomputable def evenS (p : ℝ) : ℕ → ℝ
  | 0 => (1-p)^3
  | 1 => p*(1-p)^2
  | 2 => p^2*(1-p)
  | _ => p^3

noncomputable def oddS (p : ℝ) : ℕ → ℝ
  | 0 => 2*p*(1-p)^2
  | _ => 2*p^2*(1-p)

noncomputable def kE (u : ℝ) := (1+u^4)/2-u^2
noncomputable def base (u m : ℝ) := u^2*m+(u+u^3)/2*(1-m)
noncomputable def join (e o : ℕ → ℝ) (i : Class) :=
  if evenGroup i then e i.val else o (i.val-4)

def PrefixMaximum (s : ℕ → ℝ) (n : ℕ) (m c r : ℝ) : Prop :=
  ∃ k, 1 ≤ k ∧ k ≤ n ∧ r=WaterFilling.ratio s m c k ∧
    (∀ j, 1≤j → j≤n → WaterFilling.ratio s m c j≤r) ∧ (m=0 → k=1)

theorem group_solution {s : ℕ → ℝ} {n : ℕ} {m c : ℝ} (hn : 0<n)
    (hm : 0≤m) (hc : 0<c) (hs : ∀ i<n, 0<s i)
    (sort : ∀ i j, i≤j → j<n → s j≤s i) :
    ∃ r, PrefixMaximum s n m c r ∧ 0<r ∧ (∑ i ∈ Finset.range n, clipped s r c i)=m := by
  rcases eq_or_lt_of_le hm with h|h
  · subst m
    obtain ⟨r,best,zero⟩ := empty_group hn hc (hs 0 hn) (fun i hi => sort 0 i (Nat.zero_le i) hi)
    refine ⟨_,⟨1,le_rfl,hn,rfl,best,fun _ => rfl⟩,r.symm ▸ div_pos (hs 0 hn) hc,?_⟩
    exact Finset.sum_eq_zero (fun i hi => zero i (Finset.mem_range.mp hi))
  · obtain ⟨k,hk,hkn,best⟩ := prefix_maximum s n hn m c
    exact ⟨_,⟨k,hk,hkn,rfl,best,fun e => (h.ne' e).elim⟩,positive_ratio hk hkn hm hc hs,
      clipped_total h hc hk hkn hs sort best⟩

theorem class_data {p : ℝ} (hp : 0<p) (ph : p<1/2) :
    (∀ i<4, 0<evenS p i) ∧ (∀ i j, i≤j → j<4 → evenS p j≤evenS p i) ∧
    (∀ i<2, 0<oddS p i) ∧ (∀ i j, i≤j → j<2 → oddS p j≤oddS p i) := by
  obtain ⟨a,b,c,d⟩ := Coefficients.class_order_and_kernel_gaps.1 p hp ph
  have m : 0<1-p := by linarith
  refine ⟨?_,?_,?_,?_⟩
  · intro i h
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases hi with rfl|rfl|rfl|rfl
    · exact pow_pos m 3
    · exact mul_pos hp (sq_pos_of_pos m)
    · exact mul_pos (sq_pos_of_pos hp) m
    · exact pow_pos hp 3
  · intro i j ij j4; have i4 := ij.trans_lt j4
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases hi with rfl|rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl|rfl <;> norm_num [evenS] at * <;> linarith
  · intro i h
    have hi : i=0 ∨ i=1 := by omega
    rcases hi with rfl|rfl
    · exact mul_pos (mul_pos (by norm_num) hp) (sq_pos_of_pos m)
    · exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hp)) m
  · intro i j ij j2; have i2 := ij.trans_lt j2
    have hi : i=0 ∨ i=1 := by omega
    have hj : j=0 ∨ j=1 := by omega
    rcases hi with rfl|rfl <;> rcases hj with rfl|rfl <;> norm_num [oddS] at * <;> linarith

theorem allocation {p u θ : ℝ} (hp : 0<p) (ph : p<1/2) (hu : 0<u) (uh : u<1)
    (hθ : 0≤θ) (θh : θ≤1) :
    let cE := base u θ/kE u
    let cO := base u (1-θ)/(kE u/2)
    ∃ e o, PrefixMaximum (evenS p) 4 θ cE e ∧ PrefixMaximum (oddS p) 2 (1-θ) cO o ∧
      let w := join (clipped (evenS p) e cE) (clipped (oddS p) o cO)
      (∀ i, 0≤w i) ∧ evenMass w=θ ∧ oddMass w=1-θ ∧ (∑ i, w i)=1 ∧
      ∀ i, let g := coefficient u i*Four.ratio p u w i
           let η := if evenGroup i then e else o
           g≤η ∧ (w i≠0 → g=η) := by
  obtain ⟨χ0,χβ,βα,_⟩ := Coefficients.class_order_and_kernel_gaps.2 u hu uh
  have kp : 0<kE u := sub_pos.mpr (χβ.trans βα)
  have bp {m : ℝ} (h1 : m≤1) : 0<base u m := by
    change 0 < u^2*m+(u+u^3)/2*(1-m)
    have diff : 0 < (u+u^3)/2-u^2 := sub_pos.mpr χβ
    nlinarith only [sq_pos_of_pos hu, mul_nonneg diff.le (sub_nonneg.mpr h1)]
  let cE := base u θ/kE u
  let cO := base u (1-θ)/(kE u/2)
  have ce : 0<cE := div_pos (bp θh) kp
  have co : 0<cO := div_pos (bp (by linarith)) (by positivity)
  obtain ⟨hse,soe,hso,soo⟩ := class_data hp ph
  obtain ⟨e,em,ep,esum⟩ := group_solution (by decide : 0<4) hθ ce hse soe
  obtain ⟨o,om,op,osum⟩ := group_solution (by decide : 0<2) (sub_nonneg.mpr θh) co hso soo
  let E := clipped (evenS p) e cE
  let O := clipped (oddS p) o cO
  let w := join E O
  have et : evenMass w=θ := by simpa [evenMass,w,join,evenGroup,Finset.sum_range_succ,E] using esum
  have ot : oddMass w=1-θ := by simpa [oddMass,w,join,evenGroup,Finset.sum_range_succ,O] using osum
  refine ⟨e,o,em,om,?_,et,ot,?_,?_⟩
  · intro i; dsimp only [join]; split <;> exact le_max_left _ _
  · change (∑ i, w i)=1; rw [mass_partition,et,ot]; ring
  · intro i
    have rescale (s k b w' : ℝ) (k0 : 0<k) (b0 : 0<b) (w0 : 0≤w') :
        k*(s/(b+k*w'))=s/(b/k+w') := by
      have d1 : 0<b+k*w' := add_pos_of_pos_of_nonneg b0 (mul_nonneg k0.le w0)
      have d2 : 0<b/k+w' := add_pos_of_pos_of_nonneg (div_pos b0 k0) w0
      field_simp [k0.ne',d1.ne',d2.ne']
    have bg : baseline u w i = if evenGroup i then base u θ else base u (1-θ) := by
      unfold baseline groupMass otherMass
      change _*(if evenGroup i then evenMass w else oddMass w)+_*(if evenGroup i then oddMass w else evenMass w)=_
      rw [et,ot]
      by_cases h : evenGroup i <;> simp [h,base]
    have ke : coefficient u i = if evenGroup i then kE u else kE u/2 := by
      by_cases h : evenGroup i <;> norm_num [coefficient,cardinal,h,kE]
    have sc : sourceClasses p i=join (evenS p) (oddS p) i := by
      fin_cases i <;> rfl
    change coefficient u i*Four.ratio p u w i ≤ _ ∧ (w i≠0 → coefficient u i*Four.ratio p u w i = _)
    rw [Four.ratio,affine_Z,bg,ke,sc]
    by_cases h : evenGroup i
    · simp only [h,if_true,join,w] at *
      rw [rescale _ _ _ (E i.val) kp (bp θh) (le_max_left ..)]
      exact clipped_gain ep ce _
    · simp only [h,if_false,join,w] at *
      rw [rescale _ _ (base u (1-θ)) (O (i.val-4)) (half_pos kp) (bp (by linarith)) (le_max_left ..)]
      exact clipped_gain op co _

#print axioms allocation
end BlockHierarchy.Four.WaterClasses
