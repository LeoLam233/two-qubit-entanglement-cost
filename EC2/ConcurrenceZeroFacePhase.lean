import EC2.ConcurrenceZeroFaceQuantum
import EC2.ConcurrencePhase

/-! # The full complex zero-antidiagonal face

Independent local phases make the two remaining coherences real. This
reduces every complex state in the zero face to the constructive real
Hadamard factorization, including singular and zero-coherence cases.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace EC2.ConcurrenceZeroFace

theorem hermitian4_real_of_upper (M : Matrix (Fin 4) (Fin 4) ℂ)
    (hM : M.IsHermitian)
    (h01 : (M 0 1).im = 0) (h02 : (M 0 2).im = 0) (h03 : (M 0 3).im = 0)
    (h12 : (M 1 2).im = 0) (h13 : (M 1 3).im = 0) (h23 : (M 2 3).im = 0) :
    ∀ i j : Fin 4, (M i j).im = 0 := by
  intro i j
  have h := congrArg Complex.im (hM.apply i j)
  simp only [RCLike.star_def, Complex.conj_im] at h
  fin_cases i <;> fin_cases j <;> simp_all <;> linarith

/-- Every complex two-qubit state with diagonal marginals and vanishing
antidiagonal coherences has zero actual convex-roof concurrence. -/
theorem concurrence_zero_of_diagonal_marginals_antidiagonal
    (ρ : MState (Q × Q))
    (hmargA : twoQubitMatrix ρ 0 2 + twoQubitMatrix ρ 1 3 = 0)
    (hmargB : twoQubitMatrix ρ 0 1 + twoQubitMatrix ρ 2 3 = 0)
    (hw : twoQubitMatrix ρ 0 3 = 0) (hz : twoQubitMatrix ρ 1 2 = 0) :
    concurrence ρ = 0 := by
  let a := twoQubitMatrix ρ 0 1
  let b := twoQubitMatrix ρ 0 2
  let τ := localConj ρ (phaseUnitary b) (phaseUnitary a)
  have hb13 : twoQubitMatrix ρ 1 3 = -b := by
    dsimp [b]
    linear_combination hmargA
  have ha23 : twoQubitMatrix ρ 2 3 = -a := by
    dsimp [a]
    linear_combination hmargB
  have ht01 : twoQubitMatrix τ 0 1 = (‖a‖ : ℂ) := by
    dsimp only [τ]
    rw [twoQubitMatrix_localConj_phase]
    change (1 * 1) * a * conj (1 * phaseOf a) = _
    simpa using mul_conj_phaseOf a
  have ht02 : twoQubitMatrix τ 0 2 = (‖b‖ : ℂ) := by
    dsimp only [τ]
    rw [twoQubitMatrix_localConj_phase]
    change (1 * 1) * b * conj (phaseOf b * 1) = _
    simpa using mul_conj_phaseOf b
  have ht03 : twoQubitMatrix τ 0 3 = 0 := by
    dsimp only [τ]
    rw [twoQubitMatrix_localConj_phase]
    change (1 * 1) * twoQubitMatrix ρ 0 3 * conj (phaseOf b * phaseOf a) = 0
    simp [hw]
  have ht12 : twoQubitMatrix τ 1 2 = 0 := by
    dsimp only [τ]
    rw [twoQubitMatrix_localConj_phase]
    change (1 * phaseOf a) * twoQubitMatrix ρ 1 2 * conj (phaseOf b * 1) = 0
    simp [hz]
  have ht13 : twoQubitMatrix τ 1 3 = -(‖b‖ : ℂ) := by
    dsimp only [τ]
    rw [twoQubitMatrix_localConj_phase]
    change (1 * phaseOf a) * twoQubitMatrix ρ 1 3 *
      conj (phaseOf b * phaseOf a) = _
    rw [hb13, map_mul]
    calc
      (1 * phaseOf a) * -b * (conj (phaseOf b) * conj (phaseOf a)) =
          -(b * conj (phaseOf b)) * (phaseOf a * conj (phaseOf a)) := by ring
      _ = -(‖b‖ : ℂ) := by rw [mul_conj_phaseOf, phaseOf_mul_conj, mul_one]
  have ht23 : twoQubitMatrix τ 2 3 = -(‖a‖ : ℂ) := by
    dsimp only [τ]
    rw [twoQubitMatrix_localConj_phase]
    change (phaseOf b * 1) * twoQubitMatrix ρ 2 3 *
      conj (phaseOf b * phaseOf a) = _
    rw [ha23, map_mul]
    calc
      (phaseOf b * 1) * -a * (conj (phaseOf b) * conj (phaseOf a)) =
          -(a * conj (phaseOf a)) * (phaseOf b * conj (phaseOf b)) := by ring
      _ = -(‖a‖ : ℂ) := by rw [mul_conj_phaseOf, phaseOf_mul_conj, mul_one]
  have hτreal : ∀ i j : Fin 4, (twoQubitMatrix τ i j).im = 0 :=
    hermitian4_real_of_upper _ (τ.psd.submatrix twoQubitIndex).1
      (by rw [ht01]; simp) (by rw [ht02]; simp) (by rw [ht03]; simp)
      (by rw [ht12]; simp) (by rw [ht13]; simp) (by rw [ht23]; simp)
  have hC := concurrence_zero_of_real_antidiagonal τ hτreal ht03 ht12
  simpa only [τ, concurrence_localConj] using hC

end EC2.ConcurrenceZeroFace
