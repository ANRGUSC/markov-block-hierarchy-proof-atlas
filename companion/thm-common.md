**⟨1⟩1.** Assume the hypotheses of the frozen statement. Prove the stated result under those hypotheses.

**⟨2⟩1. Reduce the common-slope estimate to one cut.** Write $\sigma_n=\sqrt n\,\omega_n$. Lemma 7 and the reverse triangle inequality give $|\sigma_{n+k}-(\sigma_n^2+\sigma_k^2)^{1/2}|\le B$, with $B=\sqrt\rho$.

**⟨2⟩2. Sum along dyadic lengths.** Doubling changes $\omega_n$ by at most $B/\sqrt{2n}$. The telescoping geometric bound is $(1+\sqrt2)B/\sqrt n$.

**⟨2⟩3. Identify the dyadic limits for every starting length.** Join $t$ equal pieces of length $2^j n$. The unnormalized error is at most $(t-1)B$ because $x\mapsto\sqrt{x^2+c^2}$ is 1-Lipschitz on $x\ge0$. Divide by $\sqrt{t2^jn}$ and send $j$ to infinity.

**⟨2⟩4. Check continuity, including zero.** Compactness and uniqueness give continuity for each finite optimizer at positive $\tau$. The score is between zero and $k\tau$, so $\omega_k$ tends to zero at the origin for each fixed $k$. Uniform convergence preserves continuity.

**⟨2⟩5. Establish strict positivity at a common slope.** Appendix B.2 bounds the gain from joining blocks on both sides, yielding the positive lower bound for $\omega_\infty(\tau)$ at $\tau>0$.

**⟨2⟩6. Control the objective and optimizing slopes.** The one-cut mean bound yields $0\le f_k-f\le J_0/k$. Finite duality gives the maximizing objective $f_k(\tau)-\tau D$. A uniform prior and the value at zero confine every maximizer to $[0,\ln 2/D]$.

**⟨2⟩7. Select the limiting slope at fixed distortion.** At a differentiability point every limiting maximizer equals $\tau(D)=-(\ln2)R'(D)$. Appendix B.2 gives a strictly positive lower bound at this interior distortion.

**⟨2⟩8. Return to the variance in bits.** Use $\tau_K\to\tau(D)$, uniform approximation at $\tau_K$, and continuity at $\tau(D)$. Then $v_K(D)=\omega_K(\tau_K)^2/(\ln2)^2$ tends to the claimed positive limit.

**⟨2⟩9. Q.E.D.** By ⟨2⟩3, ⟨2⟩4, ⟨2⟩5, ⟨2⟩7, ⟨2⟩8 under the assumptions of ⟨1⟩1.

**⟨1⟩2. Q.E.D.** By ⟨1⟩1.
