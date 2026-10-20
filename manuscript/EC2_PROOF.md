# Entanglement cost of every two-qubit state

## 1. Definitions and result

All Hilbert spaces are finite dimensional. Tensor products and partial traces are those of ordinary quantum mechanics; no superselection restriction is imposed. All entropies are in bits, except in the explicitly marked differentiation calculation. For a bipartite state,

\[
E_F(\rho_{A:B})=\inf_{\rho=\sum_jq_j|\psi_j\rangle\langle\psi_j|}
\sum_jq_jS(\operatorname{Tr}_B|\psi_j\rangle\langle\psi_j|).
\]

Write \(h_2(t)=-t\log_2t-(1-t)\log_2(1-t)\), with \(0\log0=0\), and

\[
W(c)=h_2\!\left(\frac{1+\sqrt{1-c^2}}2\right),\qquad 0\le c\le1.
\]

For a two-qubit state let \(J=\sigma_y\otimes\sigma_y\), \(\widetilde\rho=J\rho^*J\), and let \(\lambda_1\ge\cdots\ge\lambda_4\) be the square roots of the eigenvalues of \(\rho\widetilde\rho\). Wootters' theorem [1] states

\[
C(\rho)=\max(0,\lambda_1-\lambda_2-\lambda_3-\lambda_4),
\qquad E_F(\rho)=W(C(\rho)).
\]

We use two further consequences established in the same work: concurrence is the convex roof of pure-state concurrence and hence is convex, and \(W\) is increasing. Product ensembles imply the usual subadditivity of \(E_F\).

**Theorem.** Let \(A,B\) be qubits and let \(A',B'\) have arbitrary finite dimensions. Every state \(\Omega_{AA'BB'}\) satisfies

\[
\boxed{E_F(\Omega_{AA':BB'})\ge E_F(\Omega_{A:B})+E_F(\Omega_{A':B'}).}\tag{1}
\]

Consequently, for any two-qubit state \(\rho\) and any finite-dimensional bipartite state \(\sigma\),

\[
E_F(\rho\otimes\sigma)=E_F(\rho)+E_F(\sigma).\tag{2}
\]

In particular, for all two-qubit states,

\[
\boxed{E_F(\rho^{\otimes n})=nW(C(\rho))\quad\text{for every }n\ge1.}\tag{3}
\]

The operational entanglement cost under unrestricted LOCC, free classical communication, vanishing trace-distance error and no extra nonlocal resource is therefore

\[
\boxed{E_C(\rho)=W(C(\rho)).}\tag{4}
\]

The proof uses a balanced block entropy inequality and a fixed-axis concurrence bound. Both are proved below. The substantial imported results are the Schatten Hanner inequality [2], the Wootters formula [1], and the operational regularization theorem [3].

## 2. Balanced block entropy

**Lemma 1.** Let \(M\) be a complex \(2r\)-by-\(2s\) matrix of Frobenius norm one, partitioned into \(r\)-by-\(s\) blocks \(M_{ij}\). Put \(p_{ij}=\|M_{ij}\|_2^2\), using the Schatten 2 norm. Suppose

\[
p_{00}=p_{11}=x/2,\qquad p_{01}=p_{10}=y/2,\qquad x+y=1.
\]

Then

\[
S(MM^\dagger)\ge W(|x-y|)+
\sum_{i,j}p_{ij}S(M_{ij}M_{ij}^\dagger/p_{ij}).\tag{5}
\]

A zero-weight term is defined to be zero.

### Proof

Heinävaara's Corollary 1.1 [2] gives, for arbitrary complex matrices \(X,Y\) and \(q\ge2\),

\[
\|X+Y\|_q^q+\|X-Y\|_q^q
\le(\|X\|_q+\|Y\|_q)^q+|\|X\|_q-\|Y\|_q|^q.\tag{6}
\]

The complex-matrix scope is explicit in Corollary 1.5. Rectangular matrices are included by zero-padding, which preserves singular values. No positive-semidefinite or Hermitian assumption on \(X,Y\) is needed.

Set

\[
X=\begin{pmatrix}M_{00}&0\\0&M_{11}\end{pmatrix},\qquad
Y=\begin{pmatrix}0&M_{01}\\M_{10}&0\end{pmatrix}.
\]

The matrix \(X-Y\) is obtained from \(M=X+Y\) by changing the signs of the lower block row and right block column. It has the same singular values as \(M\). Thus (6) becomes

\[
2\|M\|_q^q\le(r(q)+s(q))^q+|r(q)-s(q)|^q,\tag{7}
\]

where \(r(q)=\|X\|_q\), \(s(q)=\|Y\|_q\). Both sides equal 2 at \(q=2\).

Use natural logarithms for the next calculation, writing \(S_e\) and \(W_e=(\ln2)W\). For any fixed nonzero matrix \(Z\), with \(z=\|Z\|_2^2\), differentiation of its singular-value sum gives

\[
\left.\frac{d}{dq}\log\|Z\|_q\right|_2
=-\frac14S_e(ZZ^\dagger/z).\tag{8}
\]

Indeed \(\log\|Z\|_q=q^{-1}\log\sum_k\zeta_k^q\); substituting \(\zeta_k^2=z\mu_k\) in its derivative cancels the \(\log z\) terms. Zero singular values contribute identically zero.

For \(x,y>0\), let \(S_X=S_e(XX^\dagger/x)\), \(S_Y=S_e(YY^\dagger/y)\). At \(q=2\), \(r=\sqrt{x}\), \(s=\sqrt{y}\), \(r'=-rS_X/4\), and \(s'=-sS_Y/4\). The derivative of the left side of (7) is \(-S_e(MM^\dagger)\). The derivative of the right side is

\[
(r+s)^2\log(r+s)+(r-s)^2\log|r-s|-xS_X-yS_Y
=\ln2-W_e(|x-y|)-xS_X-yS_Y.\tag{9}
\]

Since equality holds at 2, right differentiation preserves the inequality direction in (7). Rearranging gives

\[
S_e(MM^\dagger)\ge W_e(|x-y|)+xS_X+yS_Y-\ln2.\tag{10}
\]

Block-diagonal entropy and the assumed weights give

\[
xS_X+yS_Y=\ln2+\sum_{ij}p_{ij}S_e(M_{ij}M_{ij}^\dagger/p_{ij}).\tag{11}
\]

Substitution and division by \(\ln2\) prove (5).

For clarity, without the balance assumption the same argument gives

\[
S(MM^\dagger)\ge W(|x-y|)+\sum p_{ij}S(M_{ij}M_{ij}^\dagger/p_{ij})
+H(p_{00},p_{01},p_{10},p_{11})-h_2(x)-1.\tag{12}
\]

Balance is exactly what cancels the final three classical-entropy terms.

If \(x=y\), differentiability of \(r,s\) gives \(|r(q)-s(q)|=O(|q-2|)\), so the troublesome term in (7) has zero right derivative. If \(x=0\) or \(y=0\), \(M\) is block diagonal or block antidiagonal and (5) is the direct-sum entropy identity. Individual zero blocks contribute zero, with a continuous limit at fixed finite dimensions. These observations include all endpoints; no uniform limit over dimensions or tensor powers has been taken. \(\square\)

## 3. Transverse spin correlations bound concurrence

Write the Bloch decomposition

\[
\rho=\frac14\left(I\otimes I+a\cdot\sigma\otimes I+I\otimes b\cdot\sigma
+\sum_{ij}T_{ij}\sigma_i\otimes\sigma_j\right).
\]

Choose any unit axes \(n,m\) for which \(a\) is parallel to \(n\) and \(b\) is parallel to \(m\). If a Bloch vector is zero, its axis may be chosen arbitrarily. Let \(U=n^\perp\), \(V=m^\perp\), each a fixed two-dimensional real plane, and define

\[
k_{n,m}(\rho)=\max_{u\in U,v\in V,\ |u|=|v|=1}|u^TTv|.
\]

**Lemma 2.** For every two-qubit state and every such choice of axes,

\[
\boxed{C(\rho)\le k_{n,m}(\rho).}\tag{13}
\]

The clause about fixed axes at zero Bloch vectors is part of the statement.

### 3.1 Rank at most two

A two-dimensional complex subspace of \(\mathbb C^2\otimes\mathbb C^2\) contains a product vector: represent two independent vectors as 2-by-2 matrices; the homogeneous quadratic determinant of their linear combination has a projective complex root. The corresponding nonzero matrix has rank one. A rank-at-most-two state therefore has a product vector in its kernel. Local unitaries put that vector at \(|01\rangle\).

Positivity makes the 01 row and column vanish. Factor the state as \(ZZ^\dagger\) with two columns (pad a rank-one factor with a zero column). A unitary on these columns makes the 00 row equal to \((L,0)\), \(L\ge0\). If \(L=0\), the state is supported on \(|1\rangle_A\otimes\mathbb C^2_B\), so its concurrence is zero and (13) is immediate. Otherwise the two local relative phases and the remaining second-column phase put the factor in the form

\[
Z=\begin{pmatrix}L&0\\0&0\\u+iv&s\\t&r\end{pmatrix},
\qquad L,s,t,r\ge0,\quad u,v\in\mathbb R.\tag{14}
\]

For example, the phases of \(s,t,r\) change by \(\alpha+\gamma\), \(\alpha+\beta\), \(\alpha+\beta+\gamma\), respectively; these three independent combinations can set the nonzero entries nonnegative. This agrees with the three-qubit canonical purification form [4].

Keep the trace temporarily unnormalized:

\[
N=L^2+u^2+v^2+s^2+t^2+r^2,\qquad c=2Lt.
\]

The two potentially nonzero spin-flip roots are the singular values of

\[
Z^TJZ=\begin{pmatrix}-c&-Lr\\-Lr&0\end{pmatrix}.\tag{15}
\]

This follows by the equality of the nonzero spectra of \(AB\) and \(BA\), applied to \(ZZ^\dagger J\overline Z Z^TJ\). The singular-value difference of (15) is \(c\). Thus \(C(ZZ^\dagger/N)=c/N\).

Direct Pauli traces of \(ZZ^\dagger\) give the unnormalized vectors

\[
a=(2Lu,2Lv,2L^2-N),\qquad
b=(2(tu+sr),-2tv,N-2(t^2+r^2)),\tag{16}
\]

and

\[
T=\begin{pmatrix}
c&0&a_x\\0&-c&a_y\\-b_x&-b_y&2(L^2+t^2+r^2)-N
\end{pmatrix}
=D+a e_z^T-e_z b^T,
\quad D=\operatorname{diag}(c,-c,N).\tag{17}
\]

For \(u_0\in U\), \(v_0\in V\), both correction terms vanish, even when a Bloch vector is zero:

\[
u_0^TTv_0=u_0^TDv_0.\tag{18}
\]

If \(c=0\), the claim is immediate. Otherwise \(D\) is invertible, and the two planes \(V\) and \(D^{-1}U\) in \(\mathbb R^3\) intersect nontrivially. Pick a unit vector \(v_0\) in their intersection and set \(u_0=Dv_0/\|Dv_0\|\). Since

\[
N\ge L^2+t^2\ge2Lt=c,
\]

the least singular value of \(D\) is \(c\), so

\[
u_0^TTv_0=\|Dv_0\|\ge c.\tag{19}
\]

After division by \(N\), this proves the lemma for every rank-at-most-two state. The chosen axes can be carried through the local rotations, so no choice of a marginal eigenaxis has been lost.

### 3.2 Extension to all ranks

Work in the chosen local marginal eigenbases, and set \(w=\rho_{00,11}\), \(z=\rho_{01,10}\). Direct evaluation of the 2-by-2 transverse correlation matrix gives

\[
k_{n,m}(\rho)=2(|w|+|z|).\tag{20}
\]

One way to see this is to use independent local diagonal phases to make \(w,z\ge0\); these phases act as orthogonal rotations within \(U,V\). In that gauge the transverse matrix is \(\operatorname{diag}(2(w+z),2(z-w))\).

Consider the compact convex set \(\mathcal F\) of density matrices whose local marginals are diagonal in these fixed bases, whose \(w,z\) are real, and for which \(w,z\ge0\). There are seven real affine equality constraints: trace one, four local off-diagonal marginal conditions, and two imaginary anti-diagonal conditions.

Suppose an extreme point in \(\mathcal F\) has rank \(q\ge3\) and at least one of \(w,z\) positive. Hermitian perturbations supported on its range have \(q^2\ge9\) real parameters. At most one nonnegativity constraint is active. Thus at most eight homogeneous linear conditions constrain such perturbations, leaving a nonzero perturbation \(H\). For sufficiently small \(\epsilon>0\), both \(\rho\pm\epsilon H\) remain positive on the support, preserve all equalities and active constraints, and preserve the inactive strict signs. They are distinct points of \(\mathcal F\), contradicting extremality. Therefore every extreme point has rank at most two or satisfies \(w=z=0\).

It remains to check the zero face. Diagonal marginals imply its matrix is

\[
\rho=\begin{pmatrix}
\alpha&x&y&0\\x^*&\beta&0&-y\\y^*&0&\gamma&-x\\0&-y^*&-x^*&\delta
\end{pmatrix}.\tag{21}
\]

Independent local diagonal phases make \(x,y\) real. For a real state, \(R=\sqrt\rho J\sqrt\rho\) is real symmetric and the Wootters roots are the absolute values of its eigenvalues \(\mu_j\), because \(\sqrt\rho\widetilde\rho\sqrt\rho=R^2\). The triangle inequality gives

\[
C(\rho)=\max(0,2\max_j|\mu_j|-\sum_j|\mu_j|)
\le\left|\sum_j\mu_j\right|=|\operatorname{Tr}(\rho J)|=0.\tag{22}
\]

Thus the zero face has zero concurrence. The same separability also follows from the two-qubit PPT criterion.

Every member of a compact finite-dimensional convex set is a convex combination of its extreme points. On \(\mathcal F\), concurrence is convex and \(2(w+z)\) is linear. Applying the rank-at-most-two bound and the zero-face result to such a decomposition gives

\[
C(\rho)\le\sum_jp_jC(\rho_j)\le\sum_j2p_j(w_j+z_j)=2(w+z)=k_{n,m}(\rho).
\]

This proves Lemma 2 at every rank, including all degenerate marginal spectra. \(\square\)

## 4. Closure to strong superadditivity and operational cost

Let \(|\Psi\rangle\) be any pure state of \(AA'BB'\), and let \(\rho_{AB}\) be its two-qubit marginal. Choose axes \(n,m\) as in Lemma 2. The unit spheres in the two planes are compact, so there are maximizing transverse vectors \(u,v\). Reversing one sign if necessary gives

\[
\kappa=u^TTv=k_{n,m}(\rho_{AB})\ge C(\rho_{AB})\ge0.
\]

Expand the qubits in the eigenbases of \(u\cdot\sigma\) and \(v\cdot\sigma\). Because \(u\cdot a=v\cdot b=0\), the local measurement distributions are both uniform. The four joint probabilities are exactly

\[
p_{00}=p_{11}=\frac{1+\kappa}4,\qquad
p_{01}=p_{10}=\frac{1-\kappa}4.\tag{23}
\]

Across \(AA':BB'\), the coefficient matrix of \(|\Psi\rangle\) has four \(A'\)-by-\(B'\) blocks with these squared norms. Let \(|\phi_{ij}\rangle\) be the corresponding normalized nonzero block vectors. Lemma 1 and monotonicity of \(W\) give

\[
S(\Psi_{AA'})\ge W(\kappa)+\sum_{ij}p_{ij}S(\phi_{ij,A'})
\ge E_F(\rho_{AB})+\sum_{ij}p_{ij}E(\phi_{ij}).\tag{24}
\]

Tracing out \(AB\) shows

\[
\rho_{A'B'}=\sum_{ij}p_{ij}|\phi_{ij}\rangle\langle\phi_{ij}|.
\]

The definition of the convex roof therefore yields

\[
S(\Psi_{AA'})\ge E_F(\rho_{AB})+E_F(\rho_{A'B'}).\tag{25}
\]

Now take any pure decomposition \(\Omega=\sum_\ell q_\ell|\Psi_\ell\rangle\langle\Psi_\ell|\). Apply (25) separately to each vector. Its measurement axes may depend on \(\ell\), because the resulting right-hand side consists of intrinsic marginal entanglement measures. Convexity gives

\[
\sum_\ell q_\ell S(\Psi_{\ell,AA'})
\ge\sum_\ell q_\ell\{E_F(\rho^\ell_{AB})+E_F(\rho^\ell_{A'B'})\}
\ge E_F(\Omega_{AB})+E_F(\Omega_{A'B'}).
\]

Taking the infimum over decompositions proves (1). No optimal ensemble attainment assumption is necessary.

For \(\Omega=\rho\otimes\sigma\), (1) is the lower bound in (2); tensor products of arbitrarily close-to-optimal ensembles give the upper bound. Iteration proves (3) for every finite \(n\), including boundary states without a separate limiting argument. Finally the operational regularization theorem [3],

\[
E_C(\rho)=\lim_{n\to\infty}\frac{E_F(\rho^{\otimes n})}{n},
\]

proves (4). The source uses Bures error; the dimension-independent fidelity/trace-distance inequalities make vanishing Bures and trace error equivalent.  \(\square\)

## 5. Scope and physical meaning

The result concerns the entanglement needed asymptotically to prepare an ordinary two-qubit mixed state. Equation (3) rules out a reduction of the convex-roof cost through collective decompositions. Equation (4) identifies the Bell-pair formation rate. This concerns the asymptotic formation rate and does not imply reversibility with entanglement distillation.

The restriction on the peeled-off marginal in (1) is exactly \(2\times2\). Arbitrary auxiliary dimensions are allowed, but the argument does not establish unrestricted-dimensional additivity. Splitting a large system into qubit pairs only bounds its entanglement by a sum of pair marginals, which can be strictly smaller than the entanglement of a grouped marginal. For crossed Bell pairs \(A_1B_2\) and \(A_2B_1\), the grouped formation entanglement is 2 bits while both same-index marginals have zero entanglement.

Fermionic superselection examples use a different convex roof and a different copy-composition convention. The ordinary-state interpretation of the example in [7] is separable (Eq. III.28).

## References

1. W. K. Wootters, *Entanglement of Formation of an Arbitrary State of Two Qubits*, Phys. Rev. Lett. **80**, 2245 (1998). https://arxiv.org/abs/quant-ph/9709029 .
2. O. Heinävaara, *Tracial joint spectral measures*, Invent. Math. **239**, 505–526 (2025). https://doi.org/10.1007/s00222-024-01309-6 ; https://arxiv.org/abs/2310.03227 .
3. P. M. Hayden, M. Horodecki, B. M. Terhal, *The asymptotic entanglement cost of preparing a quantum state*, J. Phys. A **34**, 6891–6898 (2001). https://arxiv.org/abs/quant-ph/0008134 .
4. A. Acín et al., *Generalized Schmidt decomposition and classification of three-quantum-bit states*, Phys. Rev. Lett. **85**, 1560 (2000). https://arxiv.org/abs/quant-ph/0003050 .
5. K. Fang, *Entanglement cost of quantum depolarization*, arXiv:2610.00187v1 (2026). https://arxiv.org/abs/2610.00187 .
6. Z. Tang, C. Zhu, G. Bai, X. Wang, *Classical Capacity and Entanglement Cost of the Amplitude Damping Channel*, arXiv:2609.28592v1 (2026). https://arxiv.org/abs/2609.28592 .
7. F. Salek, A.-R. Negari, G. Smith, J. Eisert, D. Leung, *Nonadditivity in fermionic quantum Shannon theory*, arXiv:2610.06758v1 (2026). https://arxiv.org/abs/2610.06758 .
