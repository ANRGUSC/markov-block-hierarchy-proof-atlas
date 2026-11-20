**⟨1⟩1.** Assume the hypotheses of the frozen statement. Prove the stated result under those hypotheses.

**⟨2⟩1. Decompose the information.** The lossless score is $B_0+\sum_{t=1}^{K-1}A_t$. On the stated branch the tilted score differs only by a deterministic constant.

**⟨2⟩2. Propagate the two covariances.** Condition at the end of the first edge. For $h\ge1$, $\operatorname{Cov}(A_1,A_{1+h})=\rho^{h-1}\gamma$. For $h\ge0$, $\operatorname{Cov}(B_0,A_{1+h})=\rho^h\kappa$.

**⟨2⟩3. Count pairs at each lag.** Set $N=K-1$. Obtain $\operatorname{Var}B_0+Ns^2+2\gamma\sum_{h=1}^{N-1}(N-h)\rho^{h-1}+2\kappa\sum_{h=0}^{N-1}\rho^h$.

**⟨2⟩4. Extract the limit and correction.** The limit is $\sigma_X^2=s^2+2\gamma/(1-\rho)$. For nonzero $\rho$, expanding the two sums gives $c_*=\operatorname{Var}B_0-s^2+2\kappa/(1-\rho)-2\gamma[(1-\rho)^{-1}+(1-\rho)^{-2}]$.

**⟨2⟩5. Q.E.D.** By ⟨2⟩1, ⟨2⟩3, ⟨2⟩4 under the assumptions of ⟨1⟩1.

**⟨1⟩2. Q.E.D.** By ⟨1⟩1.
