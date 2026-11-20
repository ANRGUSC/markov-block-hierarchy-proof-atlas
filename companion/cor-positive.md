**⟨1⟩1.** Assume the hypotheses of the frozen statement. Prove the stated result under those hypotheses.

**⟨2⟩1. Describe the two boundary spins.** Let $b_k=E[X_kY_k]$ under the optimal length-$k$ channel. Reversal identifies the first and last correlations. Complement symmetry gives $E[Y_k\mid X_k]=b_kX_k$.

**⟨2⟩2. Bound the joining gain from below.** Run the short channels independently conditional on their input pieces. Their total penalized cost decreases by the mutual information of their output blocks. Data processing to the fair boundary output spins gives $G_{i,j}\ge\rho^2 b_i^2b_j^2/2$.

**⟨2⟩3. Bound the summed gains from above.** Replace one boundary flip by a fair flip and test the original prior. The objective increase is bounded by $(1/2-p)$ times the difference of conditional mean scores. Sum over cut locations and apply Cauchy–Schwarz with the total flip count.

**⟨2⟩4. Lower-bound the average boundary correlation.** Discarding a terminal spin gives $F_k-F_{k-1}\ge\tau(1-b_k)/2$. Sum from $1$ to $N$ and compare $F_N/N$ to the uniform-prior cost $-\ln[(1+e^{-\tau})/2]$.

**⟨2⟩5. Match the two cut sums.** Sum the lower bound over $1\le i,j\le N$. Jensen gives at least $\rho^2N^2L^4/2$. Those cuts form a subset of all cuts of lengths through $2N$, each gain nonnegative. Sum the upper bound and use common-slope convergence.

**⟨2⟩6. Q.E.D.** By ⟨2⟩5 under the assumptions of ⟨1⟩1.

**⟨1⟩2. Q.E.D.** By ⟨1⟩1.
