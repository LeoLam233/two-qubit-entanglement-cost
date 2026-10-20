import EC2.BlockEntropy
import EC2.BlockEnsemble
import EC2.ConvexRoofFormation

/-!
# The arbitrary-auxiliary-system link in EC2 Section 4

The auxiliary marginal of a normalized coefficient matrix is exactly the
mixture of its four normalized blocks. The resulting formation-entanglement
upper bound is proved using the actual finite-ensemble infimum.

The last theorem here isolates the remaining two-qubit input: an upper bound
on `E_F(AB)` by the balanced binary-entropy term. It is an explicit premise,
so this module does not assert unconditional EC2 strong superadditivity.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace EC2

variable {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    [Nonempty a] [Nonempty b]

/-- The normalized coefficient blocks form a valid decomposition of `A'B'`
at every finite auxiliary dimension, including zero-weight outcomes. -/
theorem formationBits_auxiliary_le_blocks
    (M : Matrix (Q × a) (Q × b) ℂ) (hM : matrixWeight M = 1) :
    formationBits (marginalAux (MState.pure (ketOfMatrix M hM))) ≤
      ∑ i : Q, ∑ j : Q, weightedBlockEntropy (matrixBlock M i j) := by
  have h := formationBits_le_pure_average (blockEnsemble M hM)
  rw [blockEnsemble_mix, blockEnsemble_cost] at h
  exact h

/-- Eq. 5 plus the two-qubit measurement bound imply the pure-state
`AA':BB'` entropy inequality, without any auxiliary-dimension restriction. -/
theorem pure_entropy_bound_of_balanced_blocks
    (M : Matrix (Q × a) (Q × b) ℂ) (x y : ℝ)
    (hM : matrixWeight M = 1)
    (h00 : matrixWeight (matrixBlock M 0 0) = x / 2)
    (h01 : matrixWeight (matrixBlock M 0 1) = y / 2)
    (h10 : matrixWeight (matrixBlock M 1 0) = y / 2)
    (h11 : matrixWeight (matrixBlock M 1 1) = x / 2)
    (hxy : x + y = 1)
    (hHanner : Entropy.RectangularHanner (a ⊕ a) (b ⊕ b))
    (hAB : formationBits (marginalAB (MState.pure (ketOfMatrix M hM))) ≤
      Entropy.wBits |x-y|) :
    formationBits (marginalAB (MState.pure (ketOfMatrix M hM))) +
      formationBits (marginalAux (MState.pure (ketOfMatrix M hM))) ≤
        entropyBits (MState.pure (ketOfMatrix M hM)).traceRight := by
  exact (add_le_add hAB (formationBits_auxiliary_le_blocks M hM)).trans
    (balanced_complex_rectangular_block_entropy M x y hM h00 h01 h10 h11 hxy hHanner)

end EC2
