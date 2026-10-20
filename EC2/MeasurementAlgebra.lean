import EC2.BasisTransport
import EC2.ConcurrenceAxes

/-! # Exact computational measurement probabilities and coefficient blocks -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder

namespace EC2
open ConcurrenceGeometry ConcurrenceBloch

def measurementProbability (ρ : MState (Q × Q)) (i j : Q) : ℝ :=
  (ρ.m (i,j) (i,j)).re

theorem measurementProbability_nonneg (ρ : MState (Q × Q)) (i j : Q) :
    0 ≤ measurementProbability ρ i j :=
  (Complex.nonneg_iff.mp (ρ.psd.diag_nonneg (i := (i,j)))).1

theorem measurementProbability_sum (ρ : MState (Q × Q)) :
    measurementProbability ρ 0 0 + measurementProbability ρ 0 1 +
      measurementProbability ρ 1 0 + measurementProbability ρ 1 1 = 1 := by
  have h := congrArg Complex.re ρ.tr'
  simpa [Matrix.trace, Matrix.diag, Fintype.sum_prod_type,
    Fin.sum_univ_two, measurementProbability, add_assoc] using h

theorem measurementProbability_left (ρ : MState (Q × Q)) :
    dot3 (marginalBlochA ρ) Pauli.zAxis =
      measurementProbability ρ 0 0 + measurementProbability ρ 0 1 -
        measurementProbability ρ 1 0 - measurementProbability ρ 1 1 := by
  simp [dot3, Pauli.zAxis, marginalBlochA, blochA, twoQubitMatrix,
    twoQubitIndex, pauliA, measurementProbability, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im]
  ring

theorem measurementProbability_right (ρ : MState (Q × Q)) :
    dot3 (marginalBlochB ρ) Pauli.zAxis =
      measurementProbability ρ 0 0 - measurementProbability ρ 0 1 +
        measurementProbability ρ 1 0 - measurementProbability ρ 1 1 := by
  simp [dot3, Pauli.zAxis, marginalBlochB, blochB, twoQubitMatrix,
    twoQubitIndex, pauliB, measurementProbability, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im]
  ring

theorem measurementProbability_joint (ρ : MState (Q × Q)) :
    dot3 Pauli.zAxis ((correlationMatrix ρ).mulVec Pauli.zAxis) =
      measurementProbability ρ 0 0 - measurementProbability ρ 0 1 -
        measurementProbability ρ 1 0 + measurementProbability ρ 1 1 := by
  simp [dot3, Pauli.zAxis, correlationMatrix, correlation, twoQubitMatrix,
    twoQubitIndex, pauliA, pauliB, measurementProbability, Matrix.trace,
    Matrix.diag, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im]
  ring

/-- Vanishing local Pauli expectations imply the four balanced probabilities;
no positivity of individual outcomes is assumed. -/
theorem measurementProbability_balanced (ρ : MState (Q × Q))
    (hA : dot3 (marginalBlochA ρ) Pauli.zAxis = 0)
    (hB : dot3 (marginalBlochB ρ) Pauli.zAxis = 0) :
    let κ := dot3 Pauli.zAxis ((correlationMatrix ρ).mulVec Pauli.zAxis)
    measurementProbability ρ 0 0 = (1+κ)/4 ∧
    measurementProbability ρ 1 1 = (1+κ)/4 ∧
    measurementProbability ρ 0 1 = (1-κ)/4 ∧
    measurementProbability ρ 1 0 = (1-κ)/4 := by
  have ht := measurementProbability_sum ρ
  rw [measurementProbability_left] at hA
  rw [measurementProbability_right] at hB
  dsimp only
  apply joint_probabilities_balanced
  · linarith
  · linarith
  · linarith
  · linarith
  · exact (measurementProbability_joint ρ).symm

/-- The physical measurement probability is exactly the squared Frobenius
weight of the corresponding rectangular coefficient block. -/
theorem matrixBlock_weight_eq_AB_probability {a b : Type}
    [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (ψ : Ket ((Q × a) × (Q × b))) (i j : Q) :
    matrixWeight (matrixBlock (coefficientMatrix ψ) i j) =
      measurementProbability (marginalAB (MState.pure ψ)) i j := by
  change (∑ ab : a × b, Complex.normSq (ψ ((i,ab.1),(j,ab.2)))) =
    (∑ ab : a × b, ψ ((i,ab.1),(j,ab.2)) *
      conj (ψ ((i,ab.1),(j,ab.2)))).re
  simp only [Complex.mul_conj, ← Complex.ofReal_sum, Complex.ofReal_re]

/-- A Bloch vector always admits a marginal axis. At zero, the chosen z axis
is merely one of the allowed choices; the concurrence theorem quantifies all. -/
theorem exists_marginal_axis (a : Vec3) : ∃ n : Vec3, IsMarginalAxis a n := by
  by_cases hz : a = 0
  · refine ⟨Pauli.zAxis, ?_⟩
    rw [hz]
    exact zero_has_every_unit_axis _ (by norm_num [Pauli.zAxis, sqLength, dot3])
  · have hn : ∃ i, a i ≠ 0 := by
      by_contra h
      apply hz
      push Not at h
      ext i
      exact h i
    obtain ⟨i, hi⟩ := hn
    have hp := sqLength_pos_of_coord i hi
    refine ⟨normalize a, normalize_unit hp, Real.sqrt (sqLength a), ?_⟩
    have hs : Real.sqrt (sqLength a) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp)
    funext j
    change a j = Real.sqrt (sqLength a) * (a j / Real.sqrt (sqLength a))
    field_simp

end EC2
