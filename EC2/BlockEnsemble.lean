import EC2.Measurements

/-!
# Rectangular coefficient blocks as an actual pure-state ensemble

This module links the blocks in Eq. 5 to the `A'B'` marginal in Eq. 24.
Both auxiliary dimensions are arbitrary. Zero-probability blocks use the
zero-weight convention and require no normalized zero vector.
-/

noncomputable section
open scoped BigOperators

namespace EC2

variable {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    [Nonempty a] [Nonempty b]

def blockEnsemble (M : Matrix (Q × a) (Q × b) ℂ) (h : matrixWeight M = 1) :
    PEnsemble (a × b) (Q × Q) :=
  conditionalEnsemble ((ketOfMatrix M h).relabel (regroup a b))

theorem blockEnsemble_weight (M : Matrix (Q × a) (Q × b) ℂ)
    (h : matrixWeight M = 1) (i j : Q) :
    ((blockEnsemble M h).distr (i,j) : ℝ) = matrixWeight (matrixBlock M i j) := rfl

/-- The block ensemble reconstructs the exact auxiliary marginal. -/
theorem blockEnsemble_mix (M : Matrix (Q × a) (Q × b) ℂ)
    (h : matrixWeight M = 1) :
    Ensemble.mix (Ensemble.toMEnsemble (blockEnsemble M h)) =
      marginalAux (MState.pure (ketOfMatrix M h)) := by
  unfold blockEnsemble
  rw [conditionalEnsemble_mix]
  rfl

theorem blockEnsemble_cost_entry (M : Matrix (Q × a) (Q × b) ℂ)
    (h : matrixWeight M = 1) (i j : Q) :
    ((blockEnsemble M h).distr (i,j) : ℝ) *
      entropyBits (MState.pure ((blockEnsemble M h).states (i,j))).traceRight =
      weightedBlockEntropy (matrixBlock M i j) := by
  rw [blockEnsemble_weight]
  by_cases hz : matrixWeight (matrixBlock M i j) = 0
  · simp [hz, weightedBlockEntropy_of_zero_weight _ hz]
  · have hn : ∃ ab : a × b, matrixBlock M i j ab.1 ab.2 ≠ 0 :=
      matrixWeight_ne_zero_exists _ hz
    unfold weightedBlockEntropy
    rw [dite_eq_right hz]
    congr 2
    congr 2
    change conditionalKet (fun ab : a × b => matrixBlock M i j ab.1 ab.2) = _
    simp only [conditionalKet, dite_eq_left hn]

/-- The average entanglement of the block ensemble is exactly the sum in Eq. 5. -/
theorem blockEnsemble_cost (M : Matrix (Q × a) (Q × b) ℂ)
    (h : matrixWeight M = 1) :
    (∑ k : Q × Q, ((blockEnsemble M h).distr k : ℝ) *
      entropyBits (MState.pure ((blockEnsemble M h).states k)).traceRight) =
      ∑ i : Q, ∑ j : Q, weightedBlockEntropy (matrixBlock M i j) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact blockEnsemble_cost_entry M h i j

end EC2
