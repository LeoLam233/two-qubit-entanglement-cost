import EC2.QuantumEntropy
import EC2.EntropyBlocks

/-!
# Balanced complex rectangular block entropy in physical units

The proof of Eq. 5 uses only the explicitly stated, established Schatten
Hanner inequality as an external input. All differentiation, spectral
identities, normalization, and zero-block arguments are proved in Lean.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace EC2

variable {r s : Type*} [Fintype r] [Fintype s] [DecidableEq r] [DecidableEq s]

theorem weightedBlockEntropy_eq_weightedGramEntropy (M : Matrix r s ℂ) :
    weightedBlockEntropy M = Entropy.weightedGramEntropy M / Real.log 2 := by
  rw [weightedBlockEntropy_eq_spectral, ← gramMass_eq_matrixWeight,
    Entropy.gramEntropy_decomposition]
  ring

/-- Eq. 5 with normalized density-state entropy in bits, every rectangular block,
and the zero-block convention. No strict positivity assumption is imposed. -/
theorem balanced_complex_rectangular_block_entropy
    (M : Matrix (Q × r) (Q × s) ℂ) (x y : ℝ)
    (hM : matrixWeight M = 1)
    (h00 : matrixWeight (matrixBlock M 0 0) = x / 2)
    (h01 : matrixWeight (matrixBlock M 0 1) = y / 2)
    (h10 : matrixWeight (matrixBlock M 1 0) = y / 2)
    (h11 : matrixWeight (matrixBlock M 1 1) = x / 2)
    (hxy : x + y = 1)
    (hHanner : Entropy.RectangularHanner (r ⊕ r) (s ⊕ s)) :
    Entropy.wBits |x-y| +
      (∑ i : Q, ∑ j : Q, weightedBlockEntropy (matrixBlock M i j)) ≤
        entropyBits (gramState M hM) := by
  have h : Entropy.wNats |x-y| +
      Entropy.weightedGramEntropy (matrixBlock M 0 0) +
      Entropy.weightedGramEntropy (matrixBlock M 0 1) +
      Entropy.weightedGramEntropy (matrixBlock M 1 0) +
      Entropy.weightedGramEntropy (matrixBlock M 1 1) ≤ Entropy.gramEntropy M :=
    Entropy.balanced_qubit_rectangular_entropy_nats M x y
    ((gramMass_eq_matrixWeight (matrixBlock M 0 0)).trans h00)
    ((gramMass_eq_matrixWeight (matrixBlock M 0 1)).trans h01)
    ((gramMass_eq_matrixWeight (matrixBlock M 1 0)).trans h10)
    ((gramMass_eq_matrixWeight (matrixBlock M 1 1)).trans h11)
    hxy (by simpa only [gramMass_eq_matrixWeight] using hM) hHanner
  have hd := div_le_div_of_nonneg_right h (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
  rw [gramState_entropy]
  simpa only [Entropy.wBits, Fin.sum_univ_two, weightedBlockEntropy_eq_weightedGramEntropy,
    add_div, add_assoc] using hd

end EC2
