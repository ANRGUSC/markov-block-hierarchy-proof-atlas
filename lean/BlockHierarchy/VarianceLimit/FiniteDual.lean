import BlockHierarchy.VarianceLimit.Gibbs
import BlockHierarchy.VarianceLimit.ChannelConvex
import BlockHierarchy.VarianceLimit.SupportingSlope
import BlockHierarchy.VarianceLimit.Redundancy

open scoped BigOperators
namespace BlockHierarchy.VarianceLimit
open Cut

private theorem dist_self (n : ℕ) (x : Word n) : distance n x x=0 := by
  have aux (k : ℕ) (w : Varentropy.Bits k) : Varentropy.hamming k w w=0 := by
    induction k with
    | zero => rfl
    | succ k ih => simp [Varentropy.hamming,ih]
  exact aux _ _

private theorem channel_mix {X : Type*} [Fintype X] {W V : X → X → ℝ} (hW : IsChannel W)
    (hV : IsChannel V) {a : ℝ} (h0 : 0≤a) (h1 : a≤1) :
    IsChannel (fun x y => a*W x y+(1-a)*V x y) := by
  intro x
  refine ⟨fun y => add_nonneg (mul_nonneg h0 ((hW x).1 y)) (mul_nonneg (sub_nonneg.mpr h1) ((hV x).1 y)),?_⟩
  simp [Finset.sum_add_distrib,←Finset.mul_sum,(hW x).2,(hV x).2]

private theorem distortion_mix {X : Type*} [Fintype X] (P : X → ℝ) (d : X → X → ℕ)
    (W V : X → X → ℝ) (a : ℝ) :
    totalDistortion P d (fun x y => a*W x y+(1-a)*V x y) =
      a*totalDistortion P d W+(1-a)*totalDistortion P d V := by
  unfold totalDistortion
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem finite_duality {p D : ℝ} (hp : 0<p) (ph : p<1/2) (hD : 0<D) (n : ℕ) :
    (∀ t, 0≤t → canonicalCost p n t-t*D ≤ constrainedRate p n D*Real.log 2) ∧
    (∃ t, MaximizingSlope p D n t) ∧
    ∀ t, MaximizingSlope p D n t → constrainedRate p n D*Real.log 2=canonicalCost p n t-t*D := by
  classical
  let P := mass p n
  let d := distance n
  let N : ℝ := (n:ℝ)+1
  let C := {W : Word n → Word n → ℝ // IsChannel W}
  let f := fun W : C => informationNats P W.val/N
  let g := fun W : C => totalDistortion P d W.val/N
  let v := constrainedRate p n D*Real.log 2
  have hn : 0<N := by dsimp [N]; positivity
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hp' : p<1 := by linarith
  have law : IsPrior P := ⟨fun x => (mass_pos hp hp' n x).le,mass_sum hp hp' n⟩
  let : Nonempty (Word n) := by
    rcases isEmpty_or_nonempty (Word n) with e | ne
    · have := e
      have := law.2
      simp at this
    · exact ne
  have cost (t : ℝ) (W : C) : canonicalCost p n t ≤ f W+t*g W := by
    rw [canonicalCost_eq]
    change mean P (score t d (canonicalPrior p t n))/N ≤ _/N+t*(_/N)
    rw [←mul_div_assoc,←add_div]
    exact div_le_div_of_nonneg_right (gibbs_variational law (mass_pos hp hp' n)
      (canonical_optimal p t n) W.val W.property) hn.le
  let G (t : ℝ) : C := ⟨gibbsChannel t d (canonicalPrior p t n),gibbs_isChannel _ _ (canonical_optimal p t n).1⟩
  have attain (t : ℝ) : canonicalCost p n t=f (G t)+t*g (G t) := by
    rw [canonicalCost_eq]
    change mean P (score t d (canonicalPrior p t n))/N = _/N+t*(_/N)
    rw [←mul_div_assoc,←add_div,gibbs_attains law (canonical_optimal p t n)]
  have c0 : canonicalCost p n 0=0 := by
    rw [canonicalCost_eq]
    simp [totalCost,blockScore,score,Z,(canonical_optimal p 0 n).1.2,mean]
  have fnn (W : C) : 0≤f W := by simpa [c0] using cost 0 W
  let Self : C := ⟨fun x y => if x=y then 1 else 0,fun x =>
    ⟨fun y => by by_cases z : x=y <;> simp [z], by simp⟩⟩
  have gself : g Self=0 := by
    dsimp [g,Self,totalDistortion,d]
    simp [mul_ite,ite_mul,dist_self]
  let E := {r : ℝ | ∃ W : Word n → Word n → ℝ, IsChannel W ∧ totalDistortion P d W ≤ N*D ∧
        r=informationNats P W/(N*Real.log 2)}
  have ne : E.Nonempty := by
    refine ⟨_,Self.val,Self.property,?_,rfl⟩
    have := hD.le
    apply (div_le_iff₀' hn).mp
    change g Self ≤ D
    simpa only [gself]
  have bdd : BddBelow E := by
    refine ⟨0,?_⟩
    rintro z ⟨W,hW,_,rfl⟩
    rw [← div_div]
    exact div_nonneg (fnn ⟨W,hW⟩) hl.le
  have lower (W : C) (hw : g W≤D) : v≤f W := by
    apply (le_div_iff₀ hl).mp
    change sInf E ≤ (informationNats P W.val/N)/Real.log 2
    apply csInf_le bdd
    exact ⟨W.val,W.property,(div_le_iff₀' hn).mp hw,div_div ..⟩
  have mix (W V : C) (a : ℝ) (ha : 0≤a) (hb : a≤1) (hd : a*g W+(1-a)*g V≤D) :
      v≤a*f W+(1-a)*f V := by
    let M : C := ⟨_,channel_mix W.property V.property ha hb⟩
    have dM : g M=a*g W+(1-a)*g V := by
      dsimp [M,g]
      rw [distortion_mix]
      ring
    apply (lower M (dM.trans_le hd)).trans
    dsimp [M,f]
    rw [←mul_div_assoc,←mul_div_assoc,←add_div]
    exact div_le_div_of_nonneg_right (information_mix law W.property V.property ha hb) hn.le
  obtain ⟨t,ht,support⟩ := supporting_slope f g D v ⟨Self,by rw [gself]; exact hD⟩ lower mix
  have weak (s : ℝ) (hs : 0≤s) : canonicalCost p n s-s*D ≤ v := by
    apply (div_le_iff₀ hl).mp
    change _ ≤ sInf E
    apply le_csInf ne
    rintro z ⟨W,hW,hd,rfl⟩
    rw [←div_div]
    apply div_le_div_of_nonneg_right _ hl.le
    have hw : g (⟨W,hW⟩ : C)≤D := (div_le_iff₀' hn).2 hd
    have H := cost s ⟨W,hW⟩
    have H' := mul_le_mul_of_nonneg_left hw hs
    change _ ≤ f (⟨W,hW⟩ : C)
    linarith
  have eq : v=canonicalCost p n t-t*D := by
    apply le_antisymm _ (weak t ht)
    rw [attain]
    linarith only [support (G t)]
  have opt : MaximizingSlope p D n t := ⟨ht, fun s hs => (weak s hs).trans eq.le⟩
  refine ⟨weak,⟨t,opt⟩,?_⟩
  intro z hz
  exact le_antisymm (eq.le.trans (hz.2 t ht)) (weak z hz.1)

#print axioms finite_duality
end BlockHierarchy.VarianceLimit