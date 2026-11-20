import PairPrior
import FirstSupport

namespace BlockHierarchy

theorem independent_full_support : IndependentSupportContract := by
  intro p q D _hp _hq hpq _hD hD
  have hDp := lt_of_lt_of_le hD (min_le_left p q)
  have hDq := lt_of_lt_of_le hD (min_le_right p q)
  have hden : 0 < 1-2*D := by linarith
  have hd : 1-D ≠ 0 := by linarith
  have hu : 1-D/(1-D) = (1-2*D)/(1-D) := by
    field_simp [hd]
    ring
  have hs : 0 < (p-D)/(1-2*D) := div_pos (sub_pos.mpr hDp) hden
  have ht : 0 < (q-D)/(1-2*D) := div_pos (sub_pos.mpr hDq) hden
  let A := p-p*q
  let B := q-p*q
  have hq' : q = 1-p := by linarith
  have h00 : constantMass A B (p*q) D = ((p-D)/(1-2*D))^2 := by
    simp only [constantMass, A, B, hu, hq']
    field_simp [hd, hden.ne']
    ring
  have h11 : constantMass B A (p*q) D = ((q-D)/(1-2*D))^2 := by
    simp only [constantMass, A, B, hu, hq']
    field_simp [hd, hden.ne']
    ring
  have h01 : transitionMass A B (p*q) D = (p-D)/(1-2*D) * ((q-D)/(1-2*D)) := by
    simp only [transitionMass, A, B, hu, hq']
    field_simp [hd, hden.ne']
    ring
  refine ⟨?_, hs, ht, h00, h01, h11, ?_, ?_, ?_⟩
  · rw [← add_div, div_eq_iff hden.ne']
    linarith
  · exact h00.symm ▸ sq_pos_of_pos hs
  · exact h01.symm ▸ mul_pos hs ht
  · exact h11.symm ▸ sq_pos_of_pos ht

end BlockHierarchy
