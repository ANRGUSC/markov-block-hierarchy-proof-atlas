import BlockHierarchy.RecurrencePrefix

open scoped BigOperators
namespace BlockHierarchy.Recurrence

private def layer : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n+1 => (layer n).image (fun xs => false::xs) ∪ (layer n).image (fun xs => true::xs)

private theorem mem_layer (y : List Bool) (n : ℕ) : y ∈ layer n ↔ y.length=n := by
  induction n generalizing y with
  | zero => simp [layer]
  | succ n ih =>
    cases y with
    | nil => simp [layer]
    | cons a tail => cases a <;> simp [layer,ih]

private theorem snoc_form {xs : List Bool} {n : ℕ} (h : xs.length=n+1) :
    ∃ y b, y.length=n ∧ xs=y++[b] := by
  induction xs using List.reverseRecOn generalizing n with
  | nil => simp at h
  | append_singleton ys b _ => exact ⟨ys,b,by simpa using h,rfl⟩

private theorem positive_exists (p z : ℝ) (n : ℕ) : ∃ ys, ys.length=n ∧ 0 < mass p z ys := by
  induction n with
  | zero => exact ⟨[],rfl,(empty_mass_moment p z).1.symm ▸ zero_lt_one⟩
  | succ n ih =>
    obtain ⟨ys,len,h⟩ := ih
    have e := split_mass p z ys
    by_cases pos : 0 < mass p z (ys++[true])
    · exact ⟨ys++[true],by simp [len],pos⟩
    · exact ⟨ys++[false],by simp [len],by linarith⟩

private theorem exists_maximum (p z : ℝ) (n : ℕ) : ∃ h, MaximumAt p z n h := by
  classical
  let s := (layer n).filter (fun ys => 0 < mass p z ys)
  have member (ys : List Bool) : ys ∈ s ↔ ys.length=n ∧ 0<mass p z ys := by simp [s,mem_layer]
  obtain ⟨ys,len,pos⟩ := positive_exists p z n
  have ne : s.Nonempty := ⟨ys,(member _).mpr ⟨len,pos⟩⟩
  obtain ⟨a,ha,top⟩ := Finset.exists_max_image s (fun x => |moment p z x|) ne
  obtain ⟨hn,hp⟩ := (member a).mp ha
  refine ⟨|moment p z a|,⟨a,hn,hp,rfl⟩,?_⟩
  rintro _ ⟨x,l,xp,rfl⟩
  exact top x ((member x).mpr ⟨l,xp⟩)

private theorem layer_positive {p z : ℝ} {H : ℕ → ℝ} (hz : 0<z)
    (top : ∀ n, MaximumAt p z n (H n)) (n : ℕ) (before : ∀ j<n, H j<z) :
    ∀ y : List Bool, y.length=n → 0<mass p z y := by
  induction n with
  | zero => intro y l; have e : y=[] := List.length_eq_zero_iff.mp l; subst y; rw [(empty_mass_moment p z).1]; norm_num
  | succ k ih =>
    intro x len
    obtain ⟨ys,b,lp,rfl⟩ := snoc_form len
    have pos := ih (fun j hj => before j (by omega)) _ lp
    have bound : |moment p z ys| ≤ H k := (top k).2 ⟨ys,lp,pos,rfl⟩
    exact (extension_tests ys hz pos).2.mpr (bound.trans_lt (before k (by omega))) b

private theorem update_maximum {p z : ℝ} {H : ℕ → ℝ} (hr : 0<1-2*p) (hz : 0<z) (zh : z<1)
    (top : ∀ n, MaximumAt p z n (H n)) (n : ℕ) (before : ∀ j≤n, H j<z) :
    H (n+1)=peak (1-2*p) z (H n) := by
  have parentPos := layer_positive hz top n (fun j hj => before j hj.le)
  have childPos := layer_positive hz top (n+1) (fun j hj => before j (by omega))
  have inZ (ys) (len : ys.length=n) : |moment p z ys| < z :=
    ((top n).2 ⟨ys,len,parentPos ys len,rfl⟩).trans_lt (before n le_rfl)
  obtain ⟨ys,ly,hp,eq⟩ := (top n).1
  obtain ⟨ub,witness⟩ := signed_child_max hr hz zh (inZ ys ly)
  let b := decide (moment p z ys < 0)
  have spinEq : spin b=(if 0 ≤ moment p z ys then -1 else 1) := by
    by_cases h : 0≤moment p z ys
    · simp [spin,b,h,not_lt.mpr h]
    · simp [spin,b,h,lt_of_not_ge h]
  have len : (ys++[b]).length=n+1 := by simp [ly]
  have eqc := normalized_child ys b hz hp (childPos _ len)
  rw [spinEq] at eqc
  apply le_antisymm
  · obtain ⟨xs,lx,_,hx⟩ := (top (n+1)).1
    obtain ⟨w,a,lw,rfl⟩ := snoc_form lx
    have amax := (signed_child_max hr hz zh (inZ w lw)).1
    have localLe : |signedChild (1-2*p) z (moment p z w) (spin a)| ≤ peak (1-2*p) z |moment p z w| := by
      rw [←amax]; cases a <;> first | exact le_max_left .. | exact le_max_right ..
    have lower : |moment p z w|≤H n := (top n).2 ⟨w,lw,parentPos w lw,rfl⟩
    rw [hx, normalized_child w a hz (parentPos w lw) (childPos _ lx)]
    apply localLe.trans
    rcases eq_or_lt_of_le lower with e|h
    · rw [e]
    · exact (recurrence_strict _ _ _ _ hr hz zh (abs_nonneg _) h (before n le_rfl)).le
  · have value : peak (1-2*p) z (H n)=|moment p z (ys++[b])| := by rw [eq,eqc,witness]
    exact (top (n+1)).2 ⟨ys++[b],len,childPos _ len,value⟩

theorem shorter_nonnegative {p z : ℝ} {n k : ℕ} (hk : k≤n) (feasible : InverseNonnegative p z n) :
    InverseNonnegative p z k := by
  induction n, hk using Nat.le_induction with
  | base => exact feasible
  | succ n _ ih =>
    apply ih
    intro y ly
    rw [← split_mass p z y]
    exact add_nonneg (feasible _ (by simp [ly])) (feasible _ (by simp [ly]))

/-- The paper's maxima are taken over actual positive-mass prefixes at every length,
including those reached after the first infeasible layer. -/
theorem prefix_criterion {p z : ℝ} (hp : 0<p) (ph : p<1/2) (hz : 0<z) (zh : z<1) :
    ∃ H : ℕ → ℝ, (∀ n, MaximumAt p z n (H n)) ∧ H 0=0 ∧
      (∀ n, (∀ j≤n, H j<z) → H (n+1)=peak (1-2*p) z (H n)) ∧
      (∀ n, InverseNonnegative p z (n+1) ↔ (∀ j<n, H j<z) ∧ H n≤z) := by
  classical
  choose H top using exists_maximum p z
  have zero : H 0=0 := by
    obtain ⟨y,ly,_,h⟩ := (top 0).1
    have e : y=[] := List.length_eq_zero_iff.mp ly
    simpa [e,moment,(empty_mass_moment p z).1,(empty_mass_moment p z).2] using h
  refine ⟨H,top,zero,update_maximum (by linarith) hz zh top,?_⟩
  intro n
  constructor
  · intro feas
    constructor
    · intro j hj
      obtain ⟨y,ly,pos,e⟩ := (top j).1
      rw [e]
      apply (extension_tests y hz pos).2.mp
      intro b
      have len : (y++[b]).length=j+1 := by simp [ly]
      have weak := shorter_nonnegative (show j+1 ≤ n+1 by omega) feas _ len
      apply lt_of_le_of_ne weak
      intro eq
      obtain ⟨_,c,neg⟩ := zero_child hp ph hz zh y b pos eq.symm
      have cap := shorter_nonnegative (show j+2 ≤ n+1 by omega) feas ((y++[b])++[c]) (by simp [ly])
      exact (not_lt_of_ge cap) neg
    · obtain ⟨y,ly,pos,e⟩ := (top n).1
      rw [e]
      exact (extension_tests y hz pos).1.mp (fun b => feas _ (by simp [ly]))
  · rintro ⟨before,last⟩ x len
    obtain ⟨ys,b,ly,rfl⟩ := snoc_form len
    have pos := layer_positive hz top n before ys ly
    exact (extension_tests ys hz pos).1.mpr (((top n).2 ⟨ys,ly,pos,rfl⟩).trans last) b

#print axioms prefix_criterion
end BlockHierarchy.Recurrence
