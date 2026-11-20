import BlockHierarchy.RecurrenceStatement

open scoped BigOperators
namespace BlockHierarchy.Recurrence

private theorem expect_scalar (p c : ℝ) (n : ℕ) (a : Bool) (f : List Bool → Bool → ℝ) :
    expectFrom p a n (fun xs t => c*f xs t)=c*expectFrom p a n f := by
  induction n generalizing a f with
  | zero => rfl
  | succ n ih =>
    simp only [expectFrom]
    calc
      _ = ∑ b : Bool, Three.step p a b * (c*expectFrom p b n (fun xs t => f (a::xs) t)) := by
        apply Finset.sum_congr rfl
        intro b _
        rw [ih b (fun xs t => f (a::xs) t)]
      _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring

/-- Conditional expectation of the product of signed factors times a function of the
next spin, with the Markov transition taken after each factor. -/
noncomputable def foldPrefix (p z : ℝ) (a : Bool) : List Bool → (Bool → ℝ) → ℝ
  | [], f => f a
  | y::ys, f => invWeight z a y * ∑ b : Bool, Three.step p a b*foldPrefix p z b ys f

theorem expect_prefix (p z : ℝ) (ys : List Bool) (a : Bool) (f : Bool → ℝ) :
    expectFrom p a ys.length (fun xs t => wordWeight (invWeight z) xs ys*f t)=
      foldPrefix p z a ys f := by
  induction ys generalizing a with
  | nil => simp [expectFrom,foldPrefix,wordWeight]
  | cons y ys ih =>
    simp only [List.length_cons,expectFrom,wordWeight,foldPrefix]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    simp_rw [mul_assoc,expect_scalar,ih]
    ring

noncomputable def filtered (p z : ℝ) (ys : List Bool) (f : Bool → ℝ) :=
  (∑ a : Bool, foldPrefix p z a ys f)/2

theorem mass_eq_filtered (p z : ℝ) (ys : List Bool) :
    mass p z ys=filtered p z ys (fun _ => 1) := by
  unfold mass markovExpect filtered
  simp only [← expect_prefix,mul_one]

theorem firstMoment_eq_filtered (p z : ℝ) (ys : List Bool) :
    firstMoment p z ys=filtered p z ys spin := by
  unfold firstMoment markovExpect filtered
  simp only [← expect_prefix]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  funext xs t
  exact mul_comm _ _

theorem filtered_append (p z : ℝ) (ys : List Bool) (b : Bool) (f : Bool → ℝ) :
    filtered p z (ys++[b]) f =
      filtered p z ys (fun a => invWeight z a b* ∑ t : Bool, Three.step p a t*f t) := by
  have go (seq : List Bool) (a : Bool) : foldPrefix p z a (seq++[b]) f =
      foldPrefix p z a seq (fun x => invWeight z x b*∑ t : Bool, Three.step p x t*f t) := by
    induction seq generalizing a with
    | nil => rfl
    | cons y tail ih => simp only [List.cons_append,foldPrefix,ih]
  unfold filtered
  simp_rw [go]

theorem filtered_linear (p z c d : ℝ) (ys : List Bool) (f g : Bool → ℝ) :
    filtered p z ys (fun x => c*f x+d*g x) =
      c*filtered p z ys f+d*filtered p z ys g := by
  have h (a : Bool) : foldPrefix p z a ys (fun x => c*f x+d*g x) =
      c*foldPrefix p z a ys f+d*foldPrefix p z a ys g := by
    induction ys generalizing a with
    | nil => rfl
    | cons y tail ih => simp only [foldPrefix,Fintype.sum_bool,ih]; ring
  unfold filtered
  simp only [Fintype.sum_bool,h]
  ring

theorem empty_mass_moment (p z : ℝ) : mass p z []=1 ∧ firstMoment p z []=0 := by
  norm_num [mass_eq_filtered,firstMoment_eq_filtered,filtered,foldPrefix,Fintype.sum_bool,spin]

theorem children (p z : ℝ) (ys : List Bool) (b : Bool) :
    mass p z (ys++[b])=(mass p z ys+spin b*firstMoment p z ys/z)/2 ∧
    firstMoment p z (ys++[b])=(1-2*p)*(firstMoment p z ys+spin b*mass p z ys/z)/2 := by
  have row (a : Bool) : ∑ t : Bool, Three.step p a t*(1:ℝ)=1 := by
    cases a <;> simp [Three.step]
  have pred (a : Bool) : ∑ t : Bool, Three.step p a t*spin t=(1-2*p)*spin a := by
    cases a <;> simp [Three.step,spin] <;> ring
  have one (a : Bool) : invWeight z a b * (∑ t : Bool, Three.step p a t*(1:ℝ)) =
      (1/2:ℝ)*1 + (spin b/(2*z))*spin a := by rw [row]; unfold invWeight; ring
  have two (a : Bool) : invWeight z a b * (∑ t : Bool, Three.step p a t*spin t) =
      ((1-2*p)*spin b/(2*z))*1 + ((1-2*p)/2)*spin a := by
    rw [pred]
    cases a <;> cases b <;> simp [invWeight,spin] <;> ring
  rw [mass_eq_filtered p z (ys++[b]),firstMoment_eq_filtered p z (ys++[b]),filtered_append,filtered_append]
  simp_rw [one,two]
  have h₁ := filtered_linear p z (1/2) (spin b/(2*z)) ys (fun _ => 1) spin
  have h₂ := filtered_linear p z ((1-2*p)*spin b/(2*z)) ((1-2*p)/2) ys (fun _ => 1) spin
  rw [h₁,h₂,← mass_eq_filtered,← firstMoment_eq_filtered]
  constructor <;> ring

theorem split_mass (p z : ℝ) (ys : List Bool) :
    mass p z (ys++[false])+mass p z (ys++[true])=mass p z ys := by
  rw [(children p z ys false).1,(children p z ys true).1]
  simp [spin]; ring

theorem normalized_child {p z : ℝ} (ys : List Bool) (b : Bool)
    (hz : 0 < z) (hm : 0 < mass p z ys) (hchild : 0 < mass p z (ys++[b])) :
    moment p z (ys++[b])=signedChild (1-2*p) z (moment p z ys) (spin b) := by
  let m := mass p z ys
  let t := firstMoment p z ys
  obtain ⟨child,next⟩ := children p z ys b
  have pos : 0 < m+spin b*t/z := by dsimp only [m,t]; linarith only [child,hchild]
  have mpos : 0 < m := hm
  have den : 0 < 1+spin b*(t/m)/z := by
    have h : (1+spin b*(t/m)/z)*m=m+spin b*t/z := by field_simp [hm.ne',hz.ne',mpos.ne']
    exact pos_of_mul_pos_left (h.symm ▸ pos) mpos.le
  unfold moment signedChild
  rw [next,child]
  change ((1-2*p)*(t+spin b*m/z)/2)/((m+spin b*t/z)/2)=_
  change _=(1-2*p)*((t/m+spin b/z)/(1+spin b*(t/m)/z))
  field_simp [hz.ne',mpos.ne',pos.ne',den.ne']
  <;> ring

/-- The zero-mass child of a positive prefix cannot be discarded before the final
symbol: its next signed first moment is nonzero and a grandchild has negative mass. -/
theorem zero_child {p z : ℝ} (hp : 0 < p) (ph : p < 1/2) (hz : 0 < z) (zh : z < 1)
    (ys : List Bool) (b : Bool) (hm : 0 < mass p z ys) (zero : mass p z (ys++[b])=0) :
    firstMoment p z (ys++[b]) ≠ 0 ∧ ∃ c : Bool, mass p z ((ys++[b])++[c]) < 0 := by
  let m := mass p z ys
  let t := firstMoment p z ys
  let v := firstMoment p z (ys++[b])
  have mpos : 0 < m := hm
  have rho : 0 < 1-2*p := by linarith
  have h := (children p z ys b).1
  rw [zero] at h
  have h' : m*z+spin b*t=0 := by
    have small : m+spin b*t/z=0 := by linarith only [h]
    have scaled := congrArg (fun a : ℝ => a*z) small
    simpa [add_mul,div_mul_cancel₀ _ hz.ne'] using scaled
  have mnext : v=(1-2*p)*(t+spin b*m/z)/2 := (children p z ys b).2
  have nonzero : v ≠ 0 := by
    intro e
    have q : t+spin b*m/z=0 := by
      have hprod : (1-2*p)*(t+spin b*m/z)=0 := by linarith only [e,mnext]
      exact (mul_eq_zero.mp hprod).resolve_left rho.ne'
    have eq : t*z+spin b*m=0 := by
      have scaled := congrArg (fun a : ℝ => a*z) q
      simpa [add_mul,div_mul_cancel₀ _ hz.ne'] using scaled
    have d := mul_pos mpos (mul_pos (sub_pos.mpr zh) (show 0<1+z by linarith))
    cases b <;> norm_num [spin] at h' eq <;> nlinarith only [eq,congrArg (fun a : ℝ => a*z) h',d]
  refine ⟨nonzero,?_⟩
  rcases lt_or_gt_of_ne nonzero with neg|pos
  · refine ⟨true,?_⟩
    rw [(children p z (ys++[b]) true).1,zero]
    simpa [spin] using div_neg_of_neg_of_pos (div_neg_of_neg_of_pos neg hz) (by norm_num : (0:ℝ)<2)
  · refine ⟨false,?_⟩
    rw [(children p z (ys++[b]) false).1,zero]
    simpa [spin] using div_neg_of_neg_of_pos (div_neg_of_neg_of_pos (neg_neg_of_pos pos) hz) (by norm_num : (0:ℝ)<2)

theorem extension_tests {p z : ℝ} (ys : List Bool) (hz : 0 < z) (hm : 0 < mass p z ys) :
    ((∀ b : Bool, 0 ≤ mass p z (ys++[b])) ↔ |moment p z ys| ≤ z) ∧
    ((∀ b : Bool, 0 < mass p z (ys++[b])) ↔ |moment p z ys| < z) := by
  let m := mass p z ys
  let t := firstMoment p z ys
  have factor (b : Bool) : mass p z (ys++[b])*(2*z)=m*z+spin b*t := by
    rw [(children p z ys b).1]
    dsimp [m,t]
    field_simp [hz.ne']
    <;> ring
  have two : 0 < 2*z := by positivity
  have weak (b : Bool) : 0 ≤ mass p z (ys++[b]) ↔ 0 ≤ m*z+spin b*t := by
    rw [← factor,mul_nonneg_iff_of_pos_right two]
  have strong (b : Bool) : 0 < mass p z (ys++[b]) ↔ 0 < m*z+spin b*t := by
    rw [← factor,mul_pos_iff_of_pos_right two]
  change ((∀ b : Bool, 0 ≤ mass p z (ys++[b])) ↔ |t/m| ≤ z) ∧
    ((∀ b : Bool, 0 < mass p z (ys++[b])) ↔ |t/m| < z)
  have mpos : 0 < m := hm
  simp only [Bool.forall_bool,weak,strong,spin,ite_true,ite_false,Bool.false_eq_true,
    abs_le,abs_lt,le_div_iff₀ mpos,div_le_iff₀ mpos,lt_div_iff₀ mpos,div_lt_iff₀ mpos]
  constructor <;> constructor <;> rintro ⟨h₁,h₂⟩ <;>
    constructor <;> norm_num at h₁ h₂ ⊢ <;> linarith only [h₁,h₂]

#print axioms children
#print axioms zero_child
#print axioms extension_tests
end BlockHierarchy.Recurrence
