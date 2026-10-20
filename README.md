# Entanglement cost of every two-qubit state

This repository contains a mathematical manuscript and its Lean 4 formalization of a strong-superadditivity result for **entanglement of formation with a distinguished two-qubit subsystem**.

For every finite-dimensional state \(\Omega_{AA'BB'}\) with \(A\) and \(B\) qubits and arbitrary finite-dimensional \(A'\) and \(B'\), the result is

$$
E_F(\Omega_{AA':BB'})\;\ge\;E_F(\Omega_{A:B})+E_F(\Omega_{A':B'}).
$$

Consequently, for any two-qubit state \(\rho\) and any finite-dimensional bipartite state \(\sigma\),

$$
E_F(\rho\otimes\sigma)=E_F(\rho)+E_F(\sigma),
\qquad
E_F(\rho^{\otimes n})=n\,W(C(\rho)),
\qquad
E_C(\rho)=W(C(\rho)),
$$

where \(C\) is the two-qubit concurrence and \(W(c)=h_2((1+\sqrt{1-c^2})/2)\).

## Manuscript

- [Mathematical proof (PDF)](manuscript/EC2_PROOF.pdf)
- [Searchable mathematical proof (Markdown)](manuscript/EC2_PROOF.md)

The PDF is the unchanged seven-page manuscript used as input to the independent mathematical and Lean audits (SHA-256 `3eec16b39f5a1f8a7157d8737f5c5f2e35e52c412f74bc76d6b4391d490ddeef`).

## Lean formalization

The development formalizes the EC2-specific entropy, concurrence, convex-roof, auxiliary-system and operational deductions using actual finite-dimensional complex quantum states. It reuses Mathlib and Physlib. The final declarations have **explicit theorem arguments** for the published complex Schatten–Hanner inequality, Wootters concurrence and formation formulas, and entanglement-cost regularization; those are the mathematical results imported from the cited literature.

| Mathematical statement | Lean declaration |
| --- | --- |
| Balanced rectangular block entropy, manuscript Eq. (5) | `EC2.balanced_complex_rectangular_block_entropy` |
| Fixed-axis transverse concurrence bound, Eq. (13) | `EC2.fixed_axis_concurrence` |
| Strong superadditivity, Eq. (1) | `EC2.strong_superadditivity` |
| Additivity with arbitrary finite-dimensional partner, Eq. (2) | `EC2.arbitrary_partner_additivity` |
| Every positive finite tensor power, Eq. (3) | `EC2.formation_tensor_power` |
| Operational entanglement cost, Eq. (4) | `EC2.entanglement_cost_formula` |

The main targets are in [`EC2/Targets.lean`](EC2/Targets.lean). The two core new lemmas appear in [`EC2/BlockEntropy.lean`](EC2/BlockEntropy.lean) and [`EC2/ConcurrenceFull.lean`](EC2/ConcurrenceFull.lean). The exact statement and axiom inspection is in [`verification/Statements.lean`](verification/Statements.lean).

## Reproduce

**Toolchain:** Lean `v4.35.0`; dependency revisions are fixed in `lakefile.toml` and `lake-manifest.json`.

Install [`elan`](https://github.com/leanprover/elan), then run at the repository root:

```bash
bash scripts/bootstrap.sh
```

With pinned dependencies already downloaded:

```bash
python3 scripts/verify.py --clean
```

The verification script runs a complete Lake build, checks the selected dependency revisions, prints the exact final declaration types and dependencies, and writes local records into `evidence/` (ignored by Git).

Alternatively, the essential checks are:

```bash
lake build
lake env lean verification/Statements.lean
```

For details, see [verification and mathematical scope](docs/VERIFICATION.md).

## Primary mathematical sources

1. W. K. Wootters, *Entanglement of Formation of an Arbitrary State of Two Qubits*, Physical Review Letters **80**, 2245–2248 (1998). [arXiv:quant-ph/9709029](https://arxiv.org/abs/quant-ph/9709029).
2. O. Heinävaara, *Tracial joint spectral measures*, Inventiones mathematicae **239**, 505–526 (2025). [arXiv:2310.03227](https://arxiv.org/abs/2310.03227).
3. P. M. Hayden, M. Horodecki and B. M. Terhal, *The asymptotic entanglement cost of preparing a quantum state*, Journal of Physics A **34**, 6891–6898 (2001). [arXiv:quant-ph/0008134](https://arxiv.org/abs/quant-ph/0008134).

Further references and the full derivation are in the manuscript.
