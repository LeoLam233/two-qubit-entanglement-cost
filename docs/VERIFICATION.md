# Verification and exact scope

## Reproducible project

- Lean: `leanprover/lean4:v4.35.0` (`lean-toolchain`).
- Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- Physlib: `1eefcc45aa0d864b8c742e72de5d975b3ee3b15e`.
- The transitive dependency graph is pinned in `lake-manifest.json`.

From the repository root, run `bash scripts/bootstrap.sh`, or `python3 scripts/verify.py --clean` if the pinned upstream dependencies are present. Reproducible final-statement inspection is in `verification/Statements.lean`.

The project was independently rebuilt against these revisions on 20 October 2026. Three distinct clean Lake-build replays recorded exit code zero, each ending with `Build completed successfully (3896 jobs)`, and the exact Statements verification succeeded. The public repository contains the source and verification commands so these checks can be repeated on another machine.

## Final declarations and meanings

| Declaration | Scope |
| --- | --- |
| `EC2.balanced_complex_rectangular_block_entropy` | Arbitrary finite complex rectangular block matrices satisfying the manuscript's exact normalization and balancing equations, including zero-mass endpoints. |
| `EC2.fixed_axis_concurrence` | Every two-qubit mixed state and **every** legal pair of prescribed marginal axes, including zero marginal Bloch vectors. |
| `EC2.strong_superadditivity` | Arbitrary mixed four-party state, qubits `A,B`, independently arbitrary finite nonempty auxiliary local types `a,b`; correct `AA':BB'` bipartition. |
| `EC2.arbitrary_partner_additivity` | Every two-qubit state with every finite-dimensional bipartite partner. |
| `EC2.formation_tensor_power` | Every positive natural tensor exponent. |
| `EC2.entanglement_cost_formula` | Actual Bell-pair dilution rate through finite-round adaptive LOCC and vanishing trace-distance error. |

`EC2.entanglement_cost_finite` and `EC2.entanglement_cost_real_formula` supply finiteness and the real-valued cost formula.

The substantive published-result interfaces are:

- `EC2.Entropy.RectangularHanner` / `EC2.Literature.ComplexRectangularHanner`: complex rectangular Schatten–Hanner inequality for real exponent at least two.
- `EC2.Literature.WoottersFormation`: formation-entanglement roof and concurrence relation for arbitrary two-qubit states.
- `EC2.ConcurrenceReduction.WoottersSpectralFormula`: spectral formula for two-qubit concurrence.
- `EC2.Operational.HHTRegularization`: asymptotic operational formation cost as regularized formation entanglement.

These appear as ordinary explicit proof arguments in the final theorem types. The EC2-specific lemmas and their composition are proved by Lean proof terms. `verification/Statements.lean` prints those types and their transitive axiom dependencies.

## Proof representations

The code sometimes uses an equivalent proof route rather than the manuscript's exact intermediary:

- The low-rank argument uses the product-kernel/Gram route to the needed concurrence bound.
- The zero-coherence face uses an explicit product-state decomposition.
- The all-rank extension uses an extreme-point/continuity argument.

The unbalanced explanatory variant in manuscript Eq. (12) is not exported as a standalone exact theorem declaration; it is not used in the six final claims. These representation choices do not modify their stated mathematical scopes.

## Manuscript reproducibility and release identity

The reader PDF includes author details and a short abstract. Its sole canonical
source is [`manuscript/EC2_PROOF.tex`](../manuscript/EC2_PROOF.tex), and the
[compiled PDF](../manuscript/EC2_PROOF.pdf) is built directly from that source.
The editorial migration preserves the original theorem hypotheses, proof
architecture and equations (1)--(25). The historical Markdown is retained in
Git history and the editorial review archive.

Regenerate the PDF using `python3 scripts/build_manuscript.py` with Python 3
and pdfLaTeX installed; the required standard packages and reproducibility
settings are listed in the [README](../README.md#reproduce). Use
`--log-dir PATH` to retain compiler diagnostics. A successful PDF build checks
typesetting, not mathematical correspondence or formal verification.
The Lean modules, verification scripts and pinned compiler/library dependencies
are unchanged by the editorial migration.
