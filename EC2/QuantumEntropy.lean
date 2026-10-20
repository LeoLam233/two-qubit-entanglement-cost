import EC2.Quantum
import EC2.QuantumProductEntropy
import EC2.EntropyMatrixDefs

/-! Equality of the concrete density-state entropy and the rectangular
Gram-spectrum entropy, including zero-weight blocks. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexConjugate

namespace EC2

def hermitianEntropy {d : Type*} [Fintype d] [DecidableEq d]
    (A : HermitianMat d ℂ) : ℝ := Entropy.entropy A.H.eigenvalues

theorem stateEntropy_eq_hermitianEntropy {d : Type*} [Fintype d] [DecidableEq d]
    (ρ : MState d) : Sᵥₙ ρ = hermitianEntropy ρ.M := rfl

theorem hermitianEntropy_smul {d : Type*} [Fintype d] [DecidableEq d]
    (A : HermitianMat d ℂ) (c : ℝ) :
    hermitianEntropy (c • A) = Entropy.entropy (fun i => c * A.H.eigenvalues i) := by
  obtain ⟨e,he⟩ := HermitianMat.cfc_eigenvalues (fun x => c*x) A
  rw [HermitianMat.cfc_const_mul_id] at he
  unfold hermitianEntropy Entropy.entropy
  rw [he]
  simpa [Function.comp_def] using
    Equiv.sum_comp e (fun i => Real.negMulLog (c * A.H.eigenvalues i))

section Gram
variable {r s : Type*} [Fintype r] [Fintype s] [DecidableEq r] [DecidableEq s]

def gramHermitian (M : Matrix r s ℂ) : HermitianMat r ℂ :=
  ⟨M * M.conjTranspose, Matrix.isHermitian_mul_conjTranspose_self M⟩

theorem gramMass_eq_matrixWeight (M : Matrix r s ℂ) :
    Entropy.gramMass M = matrixWeight M := by
  change (∑ i, (gramHermitian M).H.eigenvalues i) = _
  rw [HermitianMat.sum_eigenvalues_eq_trace, HermitianMat.trace_eq_re_trace]
  change (Matrix.trace (M * M.conjTranspose)).re = matrixWeight M
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    matrixWeight, Fintype.sum_prod_type, Complex.mul_re, Complex.normSq_apply]

theorem gramState_hermitian (M : Matrix r s ℂ) (h : matrixWeight M = 1) :
    (gramState M h).M = gramHermitian M := by
  apply Subtype.ext
  exact gramState_matrix M h

theorem gramState_entropy (M : Matrix r s ℂ) (h : matrixWeight M = 1) :
    entropyBits (gramState M h) = Entropy.gramEntropy M / Real.log 2 := by
  rw [entropyBits, stateEntropy_eq_hermitianEntropy, gramState_hermitian]
  rfl

theorem normalize_gram_matrix (M : Matrix r s ℂ) (h : matrixWeight M ≠ 0) :
    (MState.pure (Ket.normalize (fun ab : r × s => M ab.1 ab.2)
      (matrixWeight_ne_zero_exists M h))).traceRight.M =
        (matrixWeight M)⁻¹ • gramHermitian M := by
  have hp : 0 < matrixWeight M := lt_of_le_of_ne (matrixWeight_nonneg M) (Ne.symm h)
  have hs : Real.sqrt (matrixWeight M) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
  have hsc : (Real.sqrt (matrixWeight M) : ℂ) ≠ 0 := by exact_mod_cast hs
  have hs2 : (Real.sqrt (matrixWeight M) : ℂ) ^ 2 = (matrixWeight M : ℂ) := by
    exact_mod_cast Real.sq_sqrt hp.le
  apply Subtype.ext
  change (MState.pure (Ket.normalize (fun ab : r × s => M ab.1 ab.2)
    (matrixWeight_ne_zero_exists M h))).traceRight.M.mat =
      ((matrixWeight M)⁻¹ • gramHermitian M).mat
  rw [HermitianMat.mat_smul]
  ext a b
  simp only [MState.traceRight, MState.pure, HermitianMat.traceRight,
    HermitianMat.mat_mk, Matrix.traceRight, Matrix.vecMulVec_apply,
    Bra.eq_conj, Ket.apply, Ket.normalize, ← Complex.normSq_eq_norm_sq,
    gramHermitian, HermitianMat.mat_smul, Matrix.smul_apply, Complex.real_smul,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  change (∑ j, (M a j / (Real.sqrt (matrixWeight M) : ℂ)) *
    conj (M b j / (Real.sqrt (matrixWeight M) : ℂ))) =
    (((matrixWeight M)⁻¹ : ℝ) : ℂ) * ∑ j, M a j * conj (M b j)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [map_div₀, Complex.conj_ofReal, Complex.ofReal_inv]
  rw [← hs2]
  field_simp [hsc] <;> ring

theorem normalized_block_entropy (M : Matrix r s ℂ) (h : matrixWeight M ≠ 0) :
    Sᵥₙ (MState.pure (Ket.normalize (fun ab : r × s => M ab.1 ab.2)
      (matrixWeight_ne_zero_exists M h))).traceRight =
        Entropy.normalizedEntropy (Entropy.gramSpectrum M) := by
  rw [stateEntropy_eq_hermitianEntropy, normalize_gram_matrix M h, hermitianEntropy_smul]
  unfold Entropy.normalizedEntropy
  have hm : Entropy.mass (Entropy.gramSpectrum M) = matrixWeight M :=
    gramMass_eq_matrixWeight M
  rw [hm]
  congr 1
  funext i
  change (matrixWeight M)⁻¹ * Entropy.gramSpectrum M i =
    Entropy.gramSpectrum M i / matrixWeight M
  ring

theorem weightedBlockEntropy_eq_spectral (M : Matrix r s ℂ) :
    weightedBlockEntropy M =
      (Entropy.gramEntropy M - Real.negMulLog (matrixWeight M)) / Real.log 2 := by
  by_cases h : matrixWeight M = 0
  · have hz : Entropy.gramSpectrum M = 0 := by
      apply Entropy.eq_zero_of_nonneg_mass_zero (Entropy.gramSpectrum M)
        (Entropy.gramSpectrum_nonneg M)
      exact (gramMass_eq_matrixWeight M).trans h
    simp [weightedBlockEntropy, h, Entropy.gramEntropy, hz, Entropy.entropy]
  · rw [weightedBlockEntropy, dite_eq_right h, entropyBits, normalized_block_entropy M h]
    rw [← mul_div_assoc]
    congr 1
    have hm : Entropy.mass (Entropy.gramSpectrum M) = matrixWeight M :=
      gramMass_eq_matrixWeight M
    have he := Entropy.entropy_normalize (Entropy.gramSpectrum M) (by simpa [hm] using h)
    rw [hm] at he
    change matrixWeight M * Entropy.normalizedEntropy (Entropy.gramSpectrum M) =
      Entropy.entropy (Entropy.gramSpectrum M) - Real.negMulLog (matrixWeight M)
    linarith

end Gram

end EC2
