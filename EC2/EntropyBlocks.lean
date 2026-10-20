import EC2.EntropyMatrix
import EC2.EntropyReindex

/-! The balanced block theorem in the qubit-product coefficient indexing. -/

noncomputable section
open scoped BigOperators

namespace EC2.Entropy

variable {r s : Type*} [Fintype r] [Fintype s] [DecidableEq r] [DecidableEq s]

/-- Manuscript Eq. (5), in nats, for the coefficient matrix indexed by
`Fin 2 × r` and `Fin 2 × s`. The entropy and weighted block entropies are
defined directly from the Gram spectra and retain all zero eigenvalues.
`hHanner` is the established external Schatten Hanner inequality. -/
theorem balanced_qubit_rectangular_entropy_nats
    (M : Matrix (Fin 2 × r) (Fin 2 × s) ℂ) (x y : ℝ)
    (h00 : gramMass (fun a b => M (0, a) (0, b)) = x / 2)
    (h01 : gramMass (fun a b => M (0, a) (1, b)) = y / 2)
    (h10 : gramMass (fun a b => M (1, a) (0, b)) = y / 2)
    (h11 : gramMass (fun a b => M (1, a) (1, b)) = x / 2)
    (hxy : x + y = 1) (hM : gramMass M = 1)
    (hHanner : RectangularHanner (r ⊕ r) (s ⊕ s)) :
    wNats |x - y| + weightedGramEntropy (fun a b => M (0, a) (0, b)) +
      weightedGramEntropy (fun a b => M (0, a) (1, b)) +
      weightedGramEntropy (fun a b => M (1, a) (0, b)) +
      weightedGramEntropy (fun a b => M (1, a) (1, b)) ≤ gramEntropy M := by
  have hM' : gramMass (Matrix.fromBlocks (fun a b => M (0, a) (0, b))
      (fun a b => M (0, a) (1, b)) (fun a b => M (1, a) (0, b))
      (fun a b => M (1, a) (1, b))) = 1 := by
    rw [← reindex_qubitSum, gramMass_reindex]
    exact hM
  have h := balanced_rectangular_entropy_nats
    (fun a b => M (0, a) (0, b)) (fun a b => M (0, a) (1, b))
    (fun a b => M (1, a) (0, b)) (fun a b => M (1, a) (1, b))
    x y h00 h01 h10 h11 hxy hM' hHanner
  rwa [← reindex_qubitSum, gramEntropy_reindex] at h

end EC2.Entropy
