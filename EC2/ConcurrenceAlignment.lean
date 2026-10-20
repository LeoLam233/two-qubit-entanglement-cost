import EC2.ConcurrenceEnsemble
import EC2.ConcurrenceCovariance

/-! # Exact two-dimensional unitary row alignment -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix ComplexConjugate

namespace EC2

/-- Complete a normalized qubit column to a unitary matrix. -/
def qubitCompletion (ψ : Ket Q) : Matrix.unitaryGroup Q ℂ :=
  ⟨!![ψ 0, -conj (ψ 1); ψ 1, conj (ψ 0)], by
    apply Matrix.mem_unitaryGroup_iff.mpr
    have hnorm : Complex.normSq (ψ 0) + Complex.normSq (ψ 1) = 1 := by
      simpa [Fin.sum_univ_two] using ψ.normalized
    simp only [Complex.normSq_apply] at hnorm
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
        Matrix.one_apply, Complex.mul_re, Complex.mul_im] <;> nlinarith only [hnorm]⟩

@[simp] theorem qubitCompletion_first_column (ψ : Ket Q) (i : Q) :
    (qubitCompletion ψ).val i 0 = ψ i := by
  fin_cases i <;> rfl

/-- A right unitary can annihilate the second entry of any complex two-entry
row, including the zero row. No division by a vanishing norm is required. -/
theorem exists_qubit_row_alignment (x : Q → ℂ) :
    ∃ U : Matrix.unitaryGroup Q ℂ, (x 0 * U.val 0 1 + x 1 * U.val 1 1) = 0 := by
  classical
  by_cases h : ∃ i, x i ≠ 0
  · have hc : ∃ i, conj (x i) ≠ 0 := by
      obtain ⟨i,hi⟩ := h
      exact ⟨i, by simpa using hi⟩
    let ψ := Ket.normalize (fun i => conj (x i)) hc
    refine ⟨qubitCompletion ψ, ?_⟩
    simp [qubitCompletion, ψ, Ket.normalize, Ket.apply]
    ring
  · have hz : ∀ i, x i = 0 := by simpa using h
    refine ⟨1, ?_⟩
    simp [hz]

end EC2
