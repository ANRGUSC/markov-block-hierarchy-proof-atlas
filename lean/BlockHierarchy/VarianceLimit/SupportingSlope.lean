import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace BlockHierarchy.VarianceLimit

/-- A strictly feasible point bounds the slopes of all chords that cross the
constraint. Their supremum supports the constrained value on every channel. -/
theorem supporting_slope {X : Type*} (f d : X → ℝ) (D v : ℝ)
    (strict : ∃ y, d y<D) (lower : ∀ y, d y≤D → v≤f y)
    (mix : ∀ x y (a : ℝ), 0≤a → a≤1 → a*d x+(1-a)*d y≤D → v≤a*f x+(1-a)*f y) :
    ∃ t : ℝ, 0≤t ∧ ∀ x, v≤f x+t*(d x-D) := by
  let S : Set ℝ := insert 0 {z | ∃ x, D<d x ∧ z=(v-f x)/(d x-D)}
  have zS : 0∈S := Set.mem_insert ..
  have chord (y : X) (hy : d y<D) : (f y-v)/(D-d y) ∈ upperBounds S := by
    intro z hz
    rcases hz with h | ⟨x,hx,rfl⟩
    · subst z
      exact div_nonneg (sub_nonneg.mpr (lower y hy.le)) (sub_nonneg.mpr hy.le)
    have hd : 0<d x-d y := sub_pos.mpr (hy.trans hx)
    let a := (D-d y)/(d x-d y)
    have ha : 0≤a := div_nonneg (sub_nonneg.mpr hy.le) hd.le
    have ha' : a≤1 := (div_le_iff₀ hd).2 (by linarith)
    have b : 1-a=(d x-D)/(d x-d y) := by dsimp [a]; field_simp [hd.ne']; ring
    have feasible : a*d x+(1-a)*d y=D := by rw [b]; dsimp [a]; field_simp [hd.ne']; ring
    have h := mix x y a ha ha' feasible.le
    rw [b] at h
    dsimp only [a] at h
    have c : (D-d y)/(d x-d y)*f x+(d x-D)/(d x-d y)*f y =
        ((D-d y)*f x+(d x-D)*f y)/(d x-d y) := by ring
    rw [c,le_div_iff₀ hd] at h
    apply (div_le_div_iff₀ (sub_pos.mpr hx) (sub_pos.mpr hy)).2
    linarith only [h]
  obtain ⟨y,hy⟩ := strict
  have bdd : BddAbove S := ⟨_,chord y hy⟩
  refine ⟨sSup S,le_csSup bdd zS,?_⟩
  intro x
  rcases lt_trichotomy (d x) D with hx | hx | hx
  · have h := csSup_le ⟨0,zS⟩ (chord x hx)
    rw [le_div_iff₀ (sub_pos.mpr hx)] at h
    linarith only [h]
  · simpa [hx] using lower x hx.le
  · have mem : (v-f x)/(d x-D) ∈ S := Or.inr ⟨x,hx,rfl⟩
    have h := le_csSup bdd mem
    rw [div_le_iff₀ (sub_pos.mpr hx)] at h
    linarith

end BlockHierarchy.VarianceLimit