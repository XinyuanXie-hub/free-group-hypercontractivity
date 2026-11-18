# Sharp hypercontractivity for free group von Neumann algebras

This project uses Lean to verify the sharp Poisson hypercontractivity threshold and the log-Sobolev inequality for free groups.

> Xinyuan Xie and Haonan Zhang, *Sharp hypercontractivity for free group von Neumann algebras*, [arXiv:2606.03423v3](https://arxiv.org/abs/2606.03423v3).

## Mathematical statements

Let $\mathbb F_n$ be the free group on $n\geq 2$ generators. Write $|g|$ for reduced word length, $\lambda_g$ for left translation on $\ell_2(\mathbb F_n)$, and $\tau$ for the canonical trace, so that $\tau(\lambda_g)=\mathbf 1_{g=e}$. The Poisson semigroup and its generator satisfy

$$
P_t(\lambda_g)=e^{-t|g|}\lambda_g,\qquad L(\lambda_g)=|g|\lambda_g.
$$

The tracial norm is $\|x\|_p=\tau(|x|^p)^{1/p}$. For positive $a$, write $\operatorname{Ent}(a)=\tau(a\log a)-\tau(a)\log\tau(a)$, with $0\log 0=0$.

<a name="theorem-1-1"></a>

**1. Theorem 1.1.** For $1<p\leq q<\infty$ and $t\geq 0$, the estimate $\|P_t x\|_q\leq\|x\|_p$ holds for every $x\in\mathbb C[\mathbb F_n]$ if and only if

$$
t\geq\frac12\log\frac{q-1}{p-1}.
$$

Lean states the estimate on Fourier polynomials, the dense core for the contractive extension to the tracial $L_p$ and $L_q$ spaces.

<a name="theorem-1-2"></a>

**2. Theorem 1.2.** For every positive $x\in\mathbb C[\mathbb F_n]$,

$$
\operatorname{Ent}(x^2)\leq 2\tau(xLx).
$$

The Lean statement covers the displayed group-algebra inequality.

## Verification

Check that the statements and definitions in [Challenge.lean](Challenge.lean) match the mathematical statements above and the cited paper. Run the verification on Linux with Bubblewrap and the toolchain in [lean-toolchain](lean-toolchain).

~~~sh
bash scripts/verify-comparator.sh
~~~

The script runs Comparator with Lean, NanoDa, and con-ron. The independent proofs start in [Solution.lean](Solution.lean). The solution model independently elaborates the approved definitions and reproduces the private auxiliary names that Comparator checks. [Template/Model.lean](Template/Model.lean)

To inspect verification on GitHub, open the Actions tab after publishing the repository and select the run for the commit being reviewed. Open **Verify the Challenge against Solution**, then **Run Comparator with Lean, NanoDa, and con-ron**. Confirm acceptance by all three checkers and the final “Your solution is okay!” message.

Successful verification checks the recorded Lean statements and proofs. Review [Challenge.lean](Challenge.lean) to confirm correspondence with the paper. See Lean's documentation on [validating proofs](https://lean-lang.org/doc/reference/latest/ValidatingProofs/#validating-comparator) and [Comparator](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/#lake-comparator).
