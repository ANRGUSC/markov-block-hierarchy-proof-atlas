import BlockHierarchy.Cut.Flips

open scoped BigOperators
namespace BlockHierarchy.Converse
open Varentropy

noncomputable def bsc (D : ℝ) : (n : ℕ) → Bits n → Bits n → ℝ
  | 0, _, _ => 1
  | n+1, x, y => (if x.1=y.1 then 1-D else D)*bsc D n x.2 y.2

end BlockHierarchy.Converse
