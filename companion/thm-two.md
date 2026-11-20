**⟨1⟩1.** Assume the hypotheses of the frozen statement. Prove the stated result under those hypotheses.

**⟨2⟩1. Full-support branch.** The backward binary symmetric channel attains the entropy lower bound through the first zero. The rate is $H(P_2)-2h_2(D)$ and the variance is the varentropy of $P_2$.

**⟨2⟩2. Solve the problem with only constant outputs.** A flip input always incurs one error. Given a constant input, an incorrect output incurs two errors. The conditional error budget is $\delta=(D-C)/S$. Chain rule gives the lower bound $S[h_2(B/S)-h_2(\delta)]$.

**⟨2⟩3. Compute the two active masses and the score.** With $u^2=\delta/(1-\delta)$ the masses are $(A-Bu^2,B-Au^2)/(S(1-u^2))$. The three normalizers are $A(1+u^2)/S,u,B(1+u^2)/S$.

**⟨2⟩4. Check the two unused columns.** Set $x=u/(1+u^2)$. Their column value is $2Sx+C/x$. It is at most one between the roots $C/S$ and $1/2$.

**⟨2⟩5. Close at zero rate.** The mass boundary $\delta=\min(A,B)/S$ gives $D=D_0$. At a biased endpoint only the more frequent constant attains zero rate, and the zero-slope convention gives zero variance.

**⟨2⟩6. Q.E.D.** By ⟨2⟩1, ⟨2⟩2, ⟨2⟩3, ⟨2⟩4, ⟨2⟩5 under the assumptions of ⟨1⟩1.

**⟨1⟩2. Q.E.D.** By ⟨1⟩1.
