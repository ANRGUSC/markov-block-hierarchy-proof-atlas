import PairChannel

namespace BlockHierarchy
open PairChannel

/-- Stationary probabilities and transition probabilities in Section 2.
Flow balance means that the two off-diagonal word probabilities coincide. -/
structure BinaryModel where
  p : ℝ
  q : ℝ
  a : ℝ
  b : ℝ
  ppos : 0 < p
  qpos : 0 < q
  normalized : p+q=1
  apos : 0 < a
  alt : a < 1
  bpos : 0 < b
  blt : b < 1
  balanced : p*a=q*b

namespace BinaryModel
def persistence (m : BinaryModel) := 1-m.a-m.b
def A (m : BinaryModel) := m.p*(1-m.a)
def B (m : BinaryModel) := m.q*(1-m.b)
def C (m : BinaryModel) := m.p*m.a
def source (m : BinaryModel) := law m.A m.B m.C
end BinaryModel

/-- At each distortion listed below a minimizing reproduction marginal has
exactly the specified support. Minimization compares all finite joint laws. -/
def SupportAt (m : BinaryModel) (D : ℝ) (active : Word → Prop) : Prop :=
  ∃ q, IsOptimalAt m.source q D ∧ (∀ w, 0 ≤ q w) ∧ (∀ w, 0 < q w ↔ active w) ∧
    ∀ t, IsOptimalAt m.source t D → t = q

/-- Proposition 1, with the support at the first zero specified word by word. -/
def FirstChangeStatement : Prop :=
  ∀ m : BinaryModel,
    (0 < m.persistence →
      let d := (1-Real.sqrt (1-4*m.C))/2
      (∀ D, 0 ≤ D → D < d → SupportAt m D (fun _ => True)) ∧
      SupportAt m d (fun w => w.1 = w.2)) ∧
    (m.persistence < 0 →
      let u := (m.C-Real.sqrt (m.C^2-m.A*m.B))/max m.A m.B
      let d := u/(1+u)
      (∀ D, 0 ≤ D → D < d → SupportAt m D (fun _ => True)) ∧
      SupportAt m d (fun w => w.1 ≠ w.2 ∨
        (w = (false,false) ∧ m.q < m.p) ∨ (w = (true,true) ∧ m.p < m.q))) ∧
    (m.persistence = 0 → ∀ D, 0 ≤ D → D < min m.p m.q → SupportAt m D (fun _ => True))

end BlockHierarchy
