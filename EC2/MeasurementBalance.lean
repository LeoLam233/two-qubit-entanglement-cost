import EC2.MeasurementAlgebra
import EC2.ConcurrenceExpectations

/-! # Attained transverse correlations yield balanced qubit measurements

The axes remain fixed throughout the maximum. Their prescribed choices are
retained even when either marginal Bloch vector is zero.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix

namespace EC2
open ConcurrenceGeometry

/-- Exact four-outcome balance after changing only the two qubit bases. -/
structure BalancedMeasurement (ρ : MState (Q × Q))
    (U V : Matrix.unitaryGroup Q ℂ) (κ : ℝ) : Prop where
  p00 : measurementProbability (localConj ρ U V) 0 0 = (1+κ)/4
  p11 : measurementProbability (localConj ρ U V) 1 1 = (1+κ)/4
  p01 : measurementProbability (localConj ρ U V) 0 1 = (1-κ)/4
  p10 : measurementProbability (localConj ρ U V) 1 0 = (1-κ)/4

/-- Eq. 23, obtained from an actual maximizing pair of transverse Pauli axes
and their actual unitary eigenbases. The signed correlation is harmless:
its absolute value is exactly the fixed-axis maximum. -/
theorem exists_balanced_maximizing_measurement (ρ : MState (Q × Q)) (n m : Vec3)
    (hn : IsMarginalAxis (marginalBlochA ρ) n)
    (hm : IsMarginalAxis (marginalBlochB ρ) m) :
    ∃ (U V : Matrix.unitaryGroup Q ℂ) (κ : ℝ),
      |κ| = transverseBound ρ n m ∧ BalancedMeasurement ρ U V κ := by
  obtain ⟨u,v,hu,hv,hnu,hmv,hmax⟩ := transverseBound_attained ρ n m
  obtain ⟨U,hU⟩ := Pauli.exists_axis_unitary u hu
  obtain ⟨V,hV⟩ := Pauli.exists_axis_unitary v hv
  have hu' : Pauli.rotation U⁻¹ u = Pauli.zAxis := by
    rw [← hU, Pauli.rotation_inverse]
  have hv' : Pauli.rotation V⁻¹ v = Pauli.zAxis := by
    rw [← hV, Pauli.rotation_inverse]
  have hA0 : dot3 (marginalBlochA ρ) u = 0 := by
    obtain ⟨_,α,ha⟩ := hn
    rw [ha]
    rw [dot3_comm]
    exact transverse_parallel n u α hnu
  have hB0 : dot3 (marginalBlochB ρ) v = 0 := by
    obtain ⟨_,β,hb⟩ := hm
    rw [hb]
    rw [dot3_comm]
    exact transverse_parallel m v β hmv
  have hA := marginal_expectation_left_localConj ρ U⁻¹ V⁻¹ u
  have hB := marginal_expectation_right_localConj ρ U⁻¹ V⁻¹ v
  rw [hu', hA0] at hA
  rw [hv', hB0] at hB
  have hc := correlation_localConj ρ U⁻¹ V⁻¹ u v
  rw [hu', hv'] at hc
  refine ⟨U⁻¹, V⁻¹, dot3 Pauli.zAxis
    ((correlationMatrix (localConj ρ U⁻¹ V⁻¹)).mulVec Pauli.zAxis), ?_, ?_⟩
  · rw [hc]
    exact hmax.symm
  · obtain ⟨h00,h11,h01,h10⟩ := measurementProbability_balanced
      (localConj ρ U⁻¹ V⁻¹) hA hB
    exact ⟨h00,h11,h01,h10⟩

/-- Positivity of actual outcome probabilities supplies both correlation
endpoints, without an operator-norm assumption. -/
theorem BalancedMeasurement.abs_le_one {ρ : MState (Q × Q)}
    {U V : Matrix.unitaryGroup Q ℂ} {κ : ℝ}
    (h : BalancedMeasurement ρ U V κ) : |κ| ≤ 1 := by
  have h00 := measurementProbability_nonneg (localConj ρ U V) 0 0
  have h01 := measurementProbability_nonneg (localConj ρ U V) 0 1
  rw [h.p00] at h00
  rw [h.p01] at h01
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end EC2
