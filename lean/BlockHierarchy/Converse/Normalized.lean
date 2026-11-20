import BlockHierarchy.Converse.Paths

namespace BlockHierarchy.Converse
open Varentropy

noncomputable def normalizedFlips (p : ℝ) (n : ℕ) (v : Bits n) :=
  (Real.sqrt n)⁻¹ * (((flipCount n v : ℝ)-(n:ℝ)*p)/Real.sqrt (p*(1-p)))

end BlockHierarchy.Converse
