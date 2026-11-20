**⟨1⟩1.** Assume the hypotheses of the frozen statement. Prove the stated result under those hypotheses.

**⟨2⟩1. Center the one-path score.** The path score $J_n$ has mean $R_n(nD)$. The rate bracket gives $0\le EJ_n-nR(D)\le I_0$.

**⟨2⟩2. Apply the nonasymptotic converse to a whole word.** Any code of size $M$ has excess-distortion probability at least $\Pr[J_n\ge\log_2 M+\gamma]-2^{-\gamma}$.

**⟨2⟩3. Use the low-distortion distribution.** Proposition 5 keeps every length on the entropy-equality branch including $D=D_c$. The centered score equals $(T-(n-1)p)\log_2((1-p)/p)$ with $T$ binomial. Dividing by $\sqrt{n\nu(p)}$ gives a standard normal limit.

**⟨2⟩4. Exclude a violating subsequence.** If the liminf were smaller, some subsequence would place the normalized log code size at least $2\delta$ below $Q^{-1}(\epsilon)$. Choose $\gamma=\log_2 n$. Eventually the tested threshold is at most $Q^{-1}(\epsilon)-\delta$.

**⟨2⟩5. Q.E.D.** By ⟨2⟩4 under the assumptions of ⟨1⟩1.

**⟨1⟩2. Q.E.D.** By ⟨1⟩1.
