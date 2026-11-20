import BlockHierarchy.Converse.BlockRate
import BlockHierarchy.Converse.Backward

open Filter Topology
namespace BlockHierarchy.Converse
open Cut Varentropy VarianceLimit

theorem rateBits_low {p D : ℝ} (hp : 0<p) (ph : p<1/2) (hd : 0<D) (hD : D≤Recurrence.grayD p) :
    rateBits p D=(binaryEntropyNats p-binaryEntropyNats D)/Real.log 2 := by
  have dh : D<1/2 := hD.trans_lt (Recurrence.gray_interior hp ph).2
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let c := (Real.log 2-binaryEntropyNats p)/Real.log 2
  let r := (binaryEntropyNats p-binaryEntropyNats D)/Real.log 2
  have finite (n : ℕ) : constrainedRate p n D=r+c/((n:ℝ)+1) := by
    obtain ⟨q,hq,src⟩ := exists_backward hp ph hd hD n
    rw [rate_backward hp (by linarith) hd dh n hq src]
    dsimp [r,c]
    have hn : (n:ℝ)+1≠0 := by positivity
    field_simp [hn,l2.ne']
    <;> ring
  have van : Tendsto (fun n : ℕ => c/((n:ℝ)+1)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      (tendsto_add_atTop_iff_nat 1).mpr (tendsto_const_div_atTop_nhds_zero_nat c)
  have H : Tendsto (fun n => constrainedRate p n D) atTop (𝓝 r) := by
    simp_rw [finite]
    simpa using (tendsto_const_nhds (x := r)).add van
  exact H.limUnder_eq

#print axioms rateBits_low
end BlockHierarchy.Converse
