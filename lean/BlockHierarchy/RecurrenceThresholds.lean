import BlockHierarchy.RecurrenceClosed
import BlockHierarchy.RecurrenceLimit

open Set Filter
open scoped Topology
namespace BlockHierarchy.Recurrence

/-- Closed, nested feasibility intervals have endpoints converging to the largest
distortion feasible at every length. Distortions zero and one half need no
extension of the inverse channel. -/
theorem threshold_intervals (P : ℕ → ℝ → Prop) (c : ℝ) (hc : c ∈ Ioo (0:ℝ) (1/2))
    (closed : ∀ n, IsClosed {x : InteriorDistortion | P n x.val})
    (down : ∀ n, ∀ x ∈ Ioo (0:ℝ) (1/2), ∀ y ∈ Ioo (0:ℝ) (1/2), x≤y → P n y → P n x)
    (nested : ∀ n x, x ∈ Ioo (0:ℝ) (1/2) → P (n+1) x → P n x)
    (all : ∀ x ∈ Ioo (0:ℝ) (1/2), (∀ n, P n x) ↔ x≤c) :
    ∃ d : ℕ → ℝ, (∀ n, 0≤d n ∧ d n≤1/2) ∧ Antitone d ∧
      (∀ n x, 0<x → x<1/2 → (P n x ↔ x≤d n)) ∧ Tendsto d atTop (𝓝 c) := by
  let S (n : ℕ) := Subtype.val '' {t : InteriorDistortion | P n t.val}
  let d (n : ℕ) := sSup (S n)
  have mem (n : ℕ) (x : ℝ) : x ∈ S n ↔ x ∈ Ioo 0 (1/2) ∧ P n x := by
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y.property,hy⟩
    · rintro ⟨hx,hp⟩
      exact ⟨⟨x,hx⟩,hp,rfl⟩
  have cm (n : ℕ) : c ∈ S n := (mem n c).2 ⟨hc,(all c hc).2 le_rfl n⟩
  have bound (n : ℕ) : (1/2:ℝ) ∈ upperBounds (S n) := fun x hx => ((mem n x).1 hx).1.2.le
  have lo (n : ℕ) : c≤d n := le_csSup ⟨_,bound n⟩ (cm n)
  have hi (n : ℕ) : d n≤1/2 := csSup_le ⟨c,cm n⟩ (bound n)
  have anti : Antitone d := antitone_nat_of_succ_le (fun n => csSup_le ⟨c,cm (n+1)⟩ (by
    intro x hx
    obtain ⟨hx,hp⟩ := (mem (n+1) x).1 hx
    exact le_csSup ⟨_,bound n⟩ ((mem n x).2 ⟨hx,nested n x hx hp⟩)))
  have eqv (n : ℕ) (x : ℝ) (lx : 0<x) (ux : x<1/2) : P n x ↔ x≤d n := by
    have hx : x ∈ Ioo 0 (1/2) := ⟨lx,ux⟩
    constructor
    · exact fun h => le_csSup ⟨_,bound n⟩ ((mem n x).2 ⟨hx,h⟩)
    · intro h
      rcases eq_or_lt_of_le h with equal|strict
      · have cl : x∈closure (S n) := equal ▸ csSup_mem_closure ⟨c,cm n⟩ ⟨_,bound n⟩
        have sub : (⟨x,hx⟩ : InteriorDistortion) ∈ closure {t : InteriorDistortion | P n t.val} :=
          closure_subtype.mpr cl
        rw [(closed n).closure_eq] at sub
        exact sub
      · obtain ⟨y,sy,xy⟩ := exists_lt_of_lt_csSup ⟨c,cm n⟩ strict
        obtain ⟨hy,py⟩ := (mem n y).1 sy
        exact down n x hx y hy xy.le py
  have lower : BddBelow (range d) := ⟨c,fun _ ⟨n,e⟩ => e ▸ lo n⟩
  have lim : iInf d=c := by
    apply le_antisymm _ (le_ciInf lo)
    by_contra! h
    let x := (c+iInf d)/2
    have top := (ciInf_le lower 0).trans (hi 0)
    have cx : c<x := by dsimp [x]; linarith
    have xl : x < iInf d := by dsimp [x]; linarith
    have hx : x ∈ Ioo 0 (1/2) := ⟨hc.1.trans cx,xl.trans_le top⟩
    exact (not_le_of_gt cx) ((all x hx).1 (fun n => (eqv n x hx.1 hx.2).2 (xl.le.trans (ciInf_le lower n))))
  exact ⟨d,fun n => ⟨hc.1.le.trans (lo n),hi n⟩,anti,eqv,lim ▸ tendsto_atTop_ciInf anti lower⟩

end BlockHierarchy.Recurrence
