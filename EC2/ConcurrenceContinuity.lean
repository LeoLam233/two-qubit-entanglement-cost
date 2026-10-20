import EC2.ConcurrenceQuantum
import EC2.ConcurrenceReduction
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Continuity from the cited Wootters spectral formula

The sole literature interface is the exact spectral formula for the
ordinary two-qubit convex roof. Continuity is proved here from continuous
matrix square roots and the operator norm, including at singular states.
-/

noncomputable section
open scoped BigOperators ComplexConjugate
set_option backward.isDefEq.respectTransparency false

namespace EC2.ConcurrenceReduction

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Transposition of a Hermitian matrix is its entrywise conjugate. -/
def hermitianTranspose : HermitianMat d ℂ →ₗ[ℝ] HermitianMat d ℂ where
  toFun A := ⟨A.mat.transpose, A.H.transpose⟩
  map_add' A B := by apply Subtype.ext; rfl
  map_smul' c A := by apply Subtype.ext; rfl

@[fun_prop] theorem continuous_hermitianTranspose :
    Continuous (hermitianTranspose (d := d)) :=
  hermitianTranspose.continuous_of_finiteDimensional

@[fun_prop] theorem continuous_hermitian_lin :
    Continuous (HermitianMat.lin : HermitianMat d ℂ →
      (EuclideanSpace ℂ d →L[ℂ] EuclideanSpace ℂ d)) := by
  have h : Continuous (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ)) :=
    (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  exact h.comp HermitianMat.continuous_mat

@[fun_prop] theorem continuous_hermitian_trace :
    Continuous (HermitianMat.trace : HermitianMat d ℂ → ℝ) := by
  rw [funext HermitianMat.trace_eq_re_trace]
  fun_prop

/-- The physical spin flip `J conjugate(ρ) J†`, where `J = σy ⊗ σy`. -/
def hermitianSpinFlip (ρ : HermitianMat (Fin 4) ℂ) : HermitianMat (Fin 4) ℂ :=
  (hermitianTranspose ρ).conj ConcurrenceAlgebra.spinFlipJ

@[fun_prop] theorem continuous_hermitianSpinFlip : Continuous hermitianSpinFlip := by
  exact (HermitianMat.conjLinear ℝ ConcurrenceAlgebra.spinFlipJ).continuous_of_finiteDimensional.comp
    continuous_hermitianTranspose

/-- The positive matrix with Wootters's four ordered roots as eigenvalues. -/
def woottersRoot (ρ : HermitianMat (Fin 4) ℂ) : HermitianMat (Fin 4) ℂ :=
  ((hermitianSpinFlip ρ).conj (ρ.cfc Real.sqrt).mat).cfc Real.sqrt

@[fun_prop] theorem continuous_woottersRoot : Continuous woottersRoot := by
  apply (HermitianMat.cfc_continuous Real.continuous_sqrt).comp
  simp only [HermitianMat.conj, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  fun_prop

/-- Wootters's `max(0, λ₁ - λ₂ - λ₃ - λ₄)` written without an
eigenvalue ordering: for a positive matrix its operator norm is `λ₁`. -/
def spectralConcurrence (ρ : HermitianMat (Fin 4) ℂ) : ℝ :=
  max 0 (2 * ‖(woottersRoot ρ).lin‖ - (woottersRoot ρ).trace)

@[fun_prop] theorem continuous_spectralConcurrence : Continuous spectralConcurrence := by
  unfold spectralConcurrence
  fun_prop

/-- The computational-order Hermitian matrix of the actual two-qubit state. -/
def qubitHermitian (ρ : MState (Q × Q)) : HermitianMat (Fin 4) ℂ :=
  ⟨twoQubitMatrix ρ, ρ.M.H.submatrix twoQubitIndex⟩

@[simp] theorem qubitHermitian_mat (ρ : MState (Q × Q)) :
    (qubitHermitian ρ).mat = twoQubitMatrix ρ := rfl

@[fun_prop] theorem continuous_qubitHermitian : Continuous qubitHermitian := by
  unfold qubitHermitian twoQubitMatrix
  fun_prop

/-- Established-results interface: Wootters's exact spectral formula for
the finite pure-state convex-roof concurrence of every two-qubit state.
This includes singular states and has no marginal-axis hypotheses. -/
def WoottersSpectralFormula : Prop :=
  ∀ ρ : MState (Q × Q), concurrence ρ = spectralConcurrence (qubitHermitian ρ)

/-- Continuity is derived, rather than included in the literature interface. -/
theorem concurrence_continuous (hWootters : WoottersSpectralFormula) :
    Continuous concurrence := by
  rw [show concurrence = spectralConcurrence ∘ qubitHermitian from funext hWootters]
  exact continuous_spectralConcurrence.comp continuous_qubitHermitian

end EC2.ConcurrenceReduction
