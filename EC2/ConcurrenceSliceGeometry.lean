import EC2.ConcurrenceSlice
import EC2.ConcurrenceAxes
import EC2.ConcurrenceZeroFacePhase

/-! # The actual marginal axes of every matrix in the fixed slice -/

noncomputable section
open scoped BigOperators ComplexConjugate
open EC2.ConcurrenceBloch EC2.ConcurrenceGeometry
set_option backward.isDefEq.respectTransparency false

namespace EC2.ConcurrenceReduction

theorem hermitian_entry_conj (H : HermitianMat (Fin 4) ℂ) (i j : Fin 4) :
    H j i = conj (H i j) := (H.H.apply j i).symm

theorem blochA_hermitian (H : HermitianMat (Fin 4) ℂ) :
    blochA H.mat = ![2 * (H 0 2 + H 1 3).re, -2 * (H 0 2 + H 1 3).im,
      (H 0 0 + H 1 1 - H 2 2 - H 3 3).re] := by
  ext i
  fin_cases i <;>
    simp [blochA, pauliA, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_succ,
      hermitian_entry_conj H 0 2, hermitian_entry_conj H 1 3, Complex.mul_re, Complex.mul_im] <;>
    ring

theorem blochB_hermitian (H : HermitianMat (Fin 4) ℂ) :
    blochB H.mat = ![2 * (H 0 1 + H 2 3).re, -2 * (H 0 1 + H 2 3).im,
      (H 0 0 - H 1 1 + H 2 2 - H 3 3).re] := by
  ext i
  fin_cases i <;>
    simp [blochB, pauliB, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_succ,
      hermitian_entry_conj H 0 1, hermitian_entry_conj H 2 3, Complex.mul_re, Complex.mul_im] <;>
    ring

theorem twoQubitMatrix_sliceState (H : HermitianMat (Fin 4) ℂ) (hH : H ∈ fixedSlice) :
    twoQubitMatrix (sliceState H hH) = H.mat :=
  congrArg HermitianMat.mat (qubitHermitian_sliceState H hH)

theorem sliceState_rank (H : HermitianMat (Fin 4) ℂ) (hH : H ∈ fixedSlice) :
    (sliceState H hH).m.rank = H.mat.rank :=
  Matrix.rank_reindex qubitIndexEquiv qubitIndexEquiv H.mat

/-- The fixed z-axis is allowed even if the first marginal is maximally
mixed; the scalar Bloch coefficient is permitted to vanish. -/
theorem sliceState_axisA (H : HermitianMat (Fin 4) ℂ) (hH : H ∈ fixedSlice) :
    IsMarginalAxis (marginalBlochA (sliceState H hH)) Pauli.zAxis := by
  have hre : (H 0 2 + H 1 3).re = 0 := congrFun hH.2.1 1
  have him : (H 0 2 + H 1 3).im = 0 := congrFun hH.2.1 2
  refine ⟨by norm_num [Pauli.zAxis, sqLength, dot3],
    (H 0 0 + H 1 1 - H 2 2 - H 3 3).re, ?_⟩
  change blochA (twoQubitMatrix (sliceState H hH)) = _
  rw [twoQubitMatrix_sliceState, blochA_hermitian, hre, him]
  ext i
  fin_cases i <;> simp [Pauli.zAxis]

/-- The same statement for the second marginal, with no spectral
nondegeneracy or nonzero Bloch-vector condition. -/
theorem sliceState_axisB (H : HermitianMat (Fin 4) ℂ) (hH : H ∈ fixedSlice) :
    IsMarginalAxis (marginalBlochB (sliceState H hH)) Pauli.zAxis := by
  have hre : (H 0 1 + H 2 3).re = 0 := congrFun hH.2.1 3
  have him : (H 0 1 + H 2 3).im = 0 := congrFun hH.2.1 4
  refine ⟨by norm_num [Pauli.zAxis, sqLength, dot3],
    (H 0 0 - H 1 1 + H 2 2 - H 3 3).re, ?_⟩
  change blochB (twoQubitMatrix (sliceState H hH)) = _
  rw [twoQubitMatrix_sliceState, blochB_hermitian, hre, him]
  ext i
  fin_cases i <;> simp [Pauli.zAxis]

theorem qubitHermitian_injective : Function.Injective qubitHermitian := by
  intro ρ σ h
  apply MState.ext
  apply Subtype.ext
  ext p q
  obtain ⟨i,rfl⟩ := qubitIndexEquiv.surjective p
  obtain ⟨j,rfl⟩ := qubitIndexEquiv.surjective q
  exact congrFun (congrFun (congrArg HermitianMat.mat h) i) j

@[simp] theorem sliceState_qubitHermitian (ρ : MState (Q × Q))
    (hρ : qubitHermitian ρ ∈ fixedSlice) : sliceState (qubitHermitian ρ) hρ = ρ :=
  qubitHermitian_injective (qubitHermitian_sliceState (qubitHermitian ρ) hρ)

/-- Actual diagonal marginal axes and the real nonnegative antidiagonal
gauge imply all seven slice equalities and both sign inequalities. -/
theorem mem_fixedSlice_of_axes_gauge (ρ : MState (Q × Q))
    (hA : IsMarginalAxis (marginalBlochA ρ) Pauli.zAxis)
    (hB : IsMarginalAxis (marginalBlochB ρ) Pauli.zAxis)
    (hwI : (twoQubitMatrix ρ 0 3).im = 0) (hzI : (twoQubitMatrix ρ 1 2).im = 0)
    (hwR : 0 ≤ (twoQubitMatrix ρ 0 3).re) (hzR : 0 ≤ (twoQubitMatrix ρ 1 2).re) :
    qubitHermitian ρ ∈ fixedSlice := by
  obtain ⟨_,α,hα⟩ := hA
  obtain ⟨_,β,hβ⟩ := hB
  have hHA : blochA (qubitHermitian ρ).mat = ![0,0,α] := by
    change marginalBlochA ρ = _
    rw [hα]
    ext i
    fin_cases i <;> simp [Pauli.zAxis]
  have hHB : blochB (qubitHermitian ρ).mat = ![0,0,β] := by
    change marginalBlochB ρ = _
    rw [hβ]
    ext i
    fin_cases i <;> simp [Pauli.zAxis]
  rw [blochA_hermitian] at hHA
  rw [blochB_hermitian] at hHB
  have hARe : ((qubitHermitian ρ) 0 2 + (qubitHermitian ρ) 1 3).re = 0 := by
    have h := congrFun hHA 0
    change 2 * _ = 0 at h
    linarith
  have hAIm : ((qubitHermitian ρ) 0 2 + (qubitHermitian ρ) 1 3).im = 0 := by
    have h := congrFun hHA 1
    change -2 * _ = 0 at h
    linarith
  have hBRe : ((qubitHermitian ρ) 0 1 + (qubitHermitian ρ) 2 3).re = 0 := by
    have h := congrFun hHB 0
    change 2 * _ = 0 at h
    linarith
  have hBIm : ((qubitHermitian ρ) 0 1 + (qubitHermitian ρ) 2 3).im = 0 := by
    have h := congrFun hHB 1
    change -2 * _ = 0 at h
    linarith
  have htrace : (qubitHermitian ρ).trace = 1 := by
    change (ρ.M.reindex qubitIndexEquiv.symm).trace = 1
    rw [HermitianMat.trace_reindex]
    exact ρ.tr
  refine ⟨?_, ?_, hwR, hzR⟩
  · change 0 ≤ ρ.M.reindex qubitIndexEquiv.symm
    rw [HermitianMat.reindex_eq_conj]
    exact HermitianMat.conj_nonneg _ ρ.nonneg
  · ext i
    fin_cases i
    · exact htrace
    · exact hARe
    · exact hAIm
    · exact hBRe
    · exact hBIm
    · exact hwI
    · exact hzI

/-- The zero-sign terminal is discharged by the actual complex zero-face
product decomposition, independently of the Wootters formula. -/
theorem fixedSlice_zero_concurrence (H : HermitianMat (Fin 4) ℂ) (hH : H ∈ fixedSlice)
    (hw : signCoordinates H 0 = 0) (hz : signCoordinates H 1 = 0) :
    concurrence (sliceState H hH) = 0 := by
  apply ConcurrenceZeroFace.concurrence_zero_of_diagonal_marginals_antidiagonal
  · rw [twoQubitMatrix_sliceState]
    apply Complex.ext
    · exact congrFun hH.2.1 1
    · exact congrFun hH.2.1 2
  · rw [twoQubitMatrix_sliceState]
    apply Complex.ext
    · exact congrFun hH.2.1 3
    · exact congrFun hH.2.1 4
  · rw [twoQubitMatrix_sliceState]
    apply Complex.ext
    · exact hw
    · exact congrFun hH.2.1 5
  · rw [twoQubitMatrix_sliceState]
    apply Complex.ext
    · exact hz
    · exact congrFun hH.2.1 6

end EC2.ConcurrenceReduction
