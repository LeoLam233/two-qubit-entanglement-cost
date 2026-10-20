import EC2.ConcurrenceAntidiagonalPhase
import EC2.ConcurrenceAxes
import EC2.ConcurrenceExpectations

/-! # Diagonal phases preserve the prescribed computational marginal axes -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix ComplexConjugate

namespace EC2

@[simp] theorem phaseUnitary_rotation_zAxis (z : ℂ) :
    Pauli.rotation (phaseUnitary z) Pauli.zAxis = Pauli.zAxis := by
  apply Pauli.observable_injective
  rw [Pauli.observable_rotation]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, phaseUnitary,
      Matrix.diagonal_apply, Pauli.observable, Pauli.zAxis,
      Matrix.conjTranspose_apply, RCLike.star_def, phaseDiagonal]

/-- The exact transverse maximum for the fixed z axes is unchanged by
any pair of diagonal local phases. -/
theorem transverseBound_localConj_phase (ρ : MState (Q × Q)) (a b : ℂ) :
    transverseBound (localConj ρ (phaseUnitary b) (phaseUnitary a)) Pauli.zAxis Pauli.zAxis =
      transverseBound ρ Pauli.zAxis Pauli.zAxis := by
  simpa only [phaseUnitary_rotation_zAxis] using
    transverseBound_localConj ρ (phaseUnitary b) (phaseUnitary a) Pauli.zAxis Pauli.zAxis

theorem marginalAxisA_localConj_phase (ρ : MState (Q × Q)) (a b : ℂ)
    (h : IsMarginalAxis (marginalBlochA ρ) Pauli.zAxis) :
    IsMarginalAxis (marginalBlochA (localConj ρ (phaseUnitary b) (phaseUnitary a)))
      Pauli.zAxis := by
  rw [marginalBlochA_localConj]
  simpa only [phaseUnitary_rotation_zAxis] using
    marginalAxis_rotation (marginalBlochA ρ) Pauli.zAxis (phaseUnitary b) h

theorem marginalAxisB_localConj_phase (ρ : MState (Q × Q)) (a b : ℂ)
    (h : IsMarginalAxis (marginalBlochB ρ) Pauli.zAxis) :
    IsMarginalAxis (marginalBlochB (localConj ρ (phaseUnitary b) (phaseUnitary a)))
      Pauli.zAxis := by
  rw [marginalBlochB_localConj]
  simpa only [phaseUnitary_rotation_zAxis] using
    marginalAxis_rotation (marginalBlochB ρ) Pauli.zAxis (phaseUnitary a) h

/-- The concurrence inequality for the fixed z axes may be proved after
simultaneously making both antidiagonal entries real and nonnegative. -/
theorem fixed_z_bound_of_nonnegative_gauge
    (h : ∀ ρ : MState (Q × Q),
      IsMarginalAxis (marginalBlochA ρ) Pauli.zAxis →
      IsMarginalAxis (marginalBlochB ρ) Pauli.zAxis →
      (twoQubitMatrix ρ 0 3).im = 0 → (twoQubitMatrix ρ 1 2).im = 0 →
      0 ≤ (twoQubitMatrix ρ 0 3).re → 0 ≤ (twoQubitMatrix ρ 1 2).re →
      concurrence ρ ≤ transverseBound ρ Pauli.zAxis Pauli.zAxis)
    (ρ : MState (Q × Q))
    (ha : IsMarginalAxis (marginalBlochA ρ) Pauli.zAxis)
    (hb : IsMarginalAxis (marginalBlochB ρ) Pauli.zAxis) :
    concurrence ρ ≤ transverseBound ρ Pauli.zAxis Pauli.zAxis := by
  obtain ⟨α, β, _, _, hw, hz⟩ := exists_nonnegative_antidiagonal_gauge ρ
  have hτ := h (localConj ρ (phaseUnitary α) (phaseUnitary β))
    (marginalAxisA_localConj_phase ρ β α ha)
    (marginalAxisB_localConj_phase ρ β α hb)
    (by rw [hw]; simp) (by rw [hz]; simp)
    (by rw [hw]; simpa using norm_nonneg (twoQubitMatrix ρ 0 3))
    (by rw [hz]; simpa using norm_nonneg (twoQubitMatrix ρ 1 2))
  simpa only [concurrence_localConj, transverseBound_localConj_phase] using hτ

/-- Every allowed fixed marginal-axis choice transports to the computational
z axes, including vanishing marginal Bloch vectors. -/
theorem fixed_axis_bound_of_fixed_z
    (h : ∀ ρ : MState (Q × Q),
      IsMarginalAxis (marginalBlochA ρ) Pauli.zAxis →
      IsMarginalAxis (marginalBlochB ρ) Pauli.zAxis →
      concurrence ρ ≤ transverseBound ρ Pauli.zAxis Pauli.zAxis)
    (ρ : MState (Q × Q)) (n m : ConcurrenceGeometry.Vec3)
    (ha : IsMarginalAxis (marginalBlochA ρ) n)
    (hb : IsMarginalAxis (marginalBlochB ρ) m) :
    concurrence ρ ≤ transverseBound ρ n m := by
  obtain ⟨U, hU⟩ := Pauli.exists_axis_unitary n ha.1
  obtain ⟨V, hV⟩ := Pauli.exists_axis_unitary m hb.1
  have hUi : Pauli.rotation U⁻¹ n = Pauli.zAxis := by
    rw [← hU, Pauli.rotation_inverse]
  have hVi : Pauli.rotation V⁻¹ m = Pauli.zAxis := by
    rw [← hV, Pauli.rotation_inverse]
  have ha' : IsMarginalAxis (marginalBlochA (localConj ρ U⁻¹ V⁻¹)) Pauli.zAxis := by
    rw [marginalBlochA_localConj]
    simpa only [hUi] using marginalAxis_rotation (marginalBlochA ρ) n U⁻¹ ha
  have hb' : IsMarginalAxis (marginalBlochB (localConj ρ U⁻¹ V⁻¹)) Pauli.zAxis := by
    rw [marginalBlochB_localConj]
    simpa only [hVi] using marginalAxis_rotation (marginalBlochB ρ) m V⁻¹ hb
  have hτ := h (localConj ρ U⁻¹ V⁻¹) ha' hb'
  have hbound := transverseBound_localConj ρ U⁻¹ V⁻¹ n m
  rw [hUi, hVi] at hbound
  rwa [concurrence_localConj, hbound] at hτ

end EC2
