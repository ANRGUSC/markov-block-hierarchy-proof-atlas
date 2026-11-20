import BlockHierarchy.Four.Preliminaries
import BlockHierarchy.Three.Classes

open scoped BigOperators
namespace BlockHierarchy.Four

abbrev Word := Bool × Three.Word
abbrev Class := Fin 6

/-- In each parity group the order agrees with the source probabilities in Table 1. -/
def orbit : Word → Class
  | (false,false,false,false) => 0
  | (false,false,false,true) => 4
  | (false,false,true,false) => 5
  | (false,false,true,true) => 1
  | (false,true,false,false) => 5
  | (false,true,false,true) => 3
  | (false,true,true,false) => 2
  | (false,true,true,true) => 4
  | (true,false,false,false) => 4
  | (true,false,false,true) => 2
  | (true,false,true,false) => 3
  | (true,false,true,true) => 5
  | (true,true,false,false) => 1
  | (true,true,false,true) => 5
  | (true,true,true,false) => 4
  | (true,true,true,true) => 0

def evenGroup (i : Class) : Prop := i.val < 4
instance (i : Class) : Decidable (evenGroup i) := inferInstanceAs (Decidable (i.val < 4))

def cardinal (i : Class) : ℝ := if evenGroup i then 2 else 4

noncomputable def prior (w : Class → ℝ) (y : Word) := w (orbit y)/cardinal (orbit y)
noncomputable def source (p : ℝ) (x : Word) := Three.step p x.1 x.2.1 * Three.markov p x.2
def distance (x y : Word) := (if x.1=y.1 then 0 else 1)+Three.hamming x.2 y.2

def sourceClasses (p : ℝ) (i : Class) : ℝ :=
  match i.val with
  | 0 => (1-p)^3
  | 1 => p*(1-p)^2
  | 2 => p^2*(1-p)
  | 3 => p^3
  | 4 => 2*p*(1-p)^2
  | _ => 2*p^2*(1-p)

theorem word_sum (f : Word → ℝ) : ∑ x, f x =
    f (false,false,false,false) +
    f (false,false,false,true) +
    f (false,false,true,false) +
    f (false,false,true,true) +
    f (false,true,false,false) +
    f (false,true,false,true) +
    f (false,true,true,false) +
    f (false,true,true,true) +
    f (true,false,false,false) +
    f (true,false,false,true) +
    f (true,false,true,false) +
    f (true,false,true,true) +
    f (true,true,false,false) +
    f (true,true,false,true) +
    f (true,true,true,false) +
    f (true,true,true,true) := by
  simp only [Fintype.sum_prod_type,Fintype.sum_bool]
  ring

theorem class_sum (f : Class → ℝ) : (∑ i, f i)=f 0+f 1+f 2+f 3+f 4+f 5 := by
  simp [Fin.sum_univ_succ]
  ring

theorem group_weight (w : Class → ℝ) : ∑ x, prior w x=∑ i, w i := by
  rw [word_sum,class_sum]
  norm_num [prior,orbit,cardinal,evenGroup]
  ring

theorem class_expectation (p : ℝ) (f : Class → ℝ) :
    ∑ x, source p x*f (orbit x)=∑ i, sourceClasses p i*f i := by
  rw [word_sum,class_sum]
  norm_num [sourceClasses,orbit,source,Three.markov,Three.step]
  ring

theorem source_probability (p : ℝ) (x : Word) : source p x=prior (sourceClasses p) x := by
  obtain ⟨a,b,c,d⟩ := x
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [source,Three.markov,Three.step,prior,sourceClasses,orbit,cardinal,evenGroup] <;> ring

def groupMass (w : Class → ℝ) (i : Class) :=
  if evenGroup i then w 0+w 1+w 2+w 3 else w 4+w 5

def otherMass (w : Class → ℝ) (i : Class) :=
  if evenGroup i then w 4+w 5 else w 0+w 1+w 2+w 3

noncomputable def classKernel (f : ℕ → ℝ) (w : Class → ℝ) (i : Class) :=
  f 2*groupMass w i+((f 1+f 3)/2)*otherMass w i+
  (((f 0+f 4)/2-f 2)/(cardinal i/2))*w i

/-- Shared orbit reduction for the Hamming normalizer and its distortion numerator. -/
theorem reduce_kernel (f : ℕ → ℝ) (w : Class → ℝ) (x : Word) :
    ∑ y, prior w y*f (distance x y)=classKernel f w (orbit x) := by
  rw [word_sum]
  obtain ⟨a,b,c,d⟩ := x
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [classKernel,groupMass,otherMass,distance,Three.hamming,prior,orbit,cardinal,evenGroup] <;> ring

noncomputable def Z (u : ℝ) := classKernel (fun d => u^d)
noncomputable def costNumerator (u : ℝ) := classKernel (fun d => u^d*(d:ℝ))

theorem class_normalizer (u : ℝ) (w : Class → ℝ) (x : Word) :
    ∑ y, prior w y*u^distance x y=Z u w (orbit x) := reduce_kernel _ _ _

theorem class_cost_numerator (u : ℝ) (w : Class → ℝ) (x : Word) :
    ∑ y, prior w y*(u^distance x y*(distance x y : ℝ))=costNumerator u w (orbit x) :=
  reduce_kernel (fun d : ℕ => u^d*(d:ℝ)) w x

end BlockHierarchy.Four
