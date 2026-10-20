import EC2.EntropyMatrixAlgebra
import Mathlib.Logic.Equiv.Prod

/-! Spectral entropy is unchanged by independent row and column relabellings. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace EC2.Entropy

variable {r s t u : Type*} [Fintype r] [Fintype s] [Fintype t] [Fintype u]
  [DecidableEq r] [DecidableEq s] [DecidableEq t] [DecidableEq u]

theorem gram_reindex (er : r ≃ t) (es : s ≃ u) (M : Matrix r s ℂ) :
    Matrix.reindex er es M * (Matrix.reindex er es M).conjTranspose =
      Matrix.reindex er er (M * M.conjTranspose) := by
  rw [Matrix.conjTranspose_reindex]
  exact Matrix.submatrix_mul_equiv M M.conjTranspose er.symm es.symm er.symm

theorem gramSpectrum_sum_reindex (er : r ≃ t) (es : s ≃ u)
    (M : Matrix r s ℂ) (f : ℝ → ℝ) :
    (∑ i, f (gramSpectrum (Matrix.reindex er es M) i)) =
      ∑ i, f (gramSpectrum M i) := by
  unfold gramSpectrum
  rw [sum_function_eigenvalues_eq_roots, sum_function_eigenvalues_eq_roots,
    gram_reindex, Matrix.charpoly_reindex]

@[simp] theorem gramMass_reindex (er : r ≃ t) (es : s ≃ u)
    (M : Matrix r s ℂ) : gramMass (Matrix.reindex er es M) = gramMass M :=
  gramSpectrum_sum_reindex er es M id

@[simp] theorem gramEntropy_reindex (er : r ≃ t) (es : s ≃ u)
    (M : Matrix r s ℂ) : gramEntropy (Matrix.reindex er es M) = gramEntropy M :=
  gramSpectrum_sum_reindex er es M Real.negMulLog

@[simp] theorem weightedGramEntropy_reindex (er : r ≃ t) (es : s ≃ u)
    (M : Matrix r s ℂ) :
    weightedGramEntropy (Matrix.reindex er es M) = weightedGramEntropy M := by
  have h := gramEntropy_decomposition (Matrix.reindex er es M)
  rw [gramEntropy_reindex, gramMass_reindex] at h
  linarith [gramEntropy_decomposition M]

/-- The concrete equivalence taking qubit label `0` to the first summand and
qubit label `1` to the second summand. -/
def qubitSumEquiv (r : Type*) : (Fin 2 × r) ≃ r ⊕ r :=
  (Equiv.prodCongr finTwoEquiv (Equiv.refl r)).trans (Equiv.boolProdEquivSum r)

@[simp] theorem qubitSumEquiv_symm_inl (a : r) :
    (qubitSumEquiv r).symm (Sum.inl a) = (0, a) := rfl

@[simp] theorem qubitSumEquiv_symm_inr (a : r) :
    (qubitSumEquiv r).symm (Sum.inr a) = (1, a) := rfl

theorem reindex_qubitSum (M : Matrix (Fin 2 × r) (Fin 2 × s) ℂ) :
    Matrix.reindex (qubitSumEquiv r) (qubitSumEquiv s) M =
      Matrix.fromBlocks (fun a b => M (0, a) (0, b))
        (fun a b => M (0, a) (1, b)) (fun a b => M (1, a) (0, b))
        (fun a b => M (1, a) (1, b)) := by
  ext (a | a) (b | b) <;> rfl

end EC2.Entropy
