import EC2.ConcurrenceSliceGeometry
import EC2.ConcurrenceRankTwo
import EC2.ConcurrenceGauge
import EC2.ConcurrencePhaseAxes

/-!
# The fixed-axis concurrence bound at every rank

All new EC2 inputs are proved in the imported files: the rank-two kernel
and Gram argument, the complex zero-face product decomposition, supported
Hermitian perturbations, the extreme-point classification, and the
compact-convex closure. The only literature premise in the final theorem
is Wootters's exact spectral formula, used to derive continuity at singular
states. Every allowed fixed marginal axis is retained throughout.
-/

noncomputable section
open scoped BigOperators ComplexConjugate
set_option backward.isDefEq.respectTransparency false

namespace EC2
open ConcurrenceGeometry ConcurrenceReduction

theorem transverseBound_sliceState (H : HermitianMat (Fin 4) ℂ) (hH : H ∈ fixedSlice) :
    transverseBound (sliceState H hH) Pauli.zAxis Pauli.zAxis = sliceWitness H := by
  have hwI : (twoQubitMatrix (sliceState H hH) 0 3).im = 0 := by
    rw [twoQubitMatrix_sliceState]
    exact congrFun hH.2.1 5
  have hzI : (twoQubitMatrix (sliceState H hH) 1 2).im = 0 := by
    rw [twoQubitMatrix_sliceState]
    exact congrFun hH.2.1 6
  have hwR : 0 ≤ (twoQubitMatrix (sliceState H hH) 0 3).re := by
    rw [twoQubitMatrix_sliceState]
    exact hH.2.2.1
  have hzR : 0 ≤ (twoQubitMatrix (sliceState H hH) 1 2).re := by
    rw [twoQubitMatrix_sliceState]
    exact hH.2.2.2
  have h := transverseBound_zAxis_gauge (sliceState H hH) hwI hzI hwR hzR
  change transverseBound (sliceState H hH) Pauli.zAxis Pauli.zAxis =
    2 * ((twoQubitMatrix (sliceState H hH) 0 3).re +
      (twoQubitMatrix (sliceState H hH) 1 2).re) at h
  rw [twoQubitMatrix_sliceState] at h
  exact h

/-- The rank-two input to the extreme-point reduction is discharged by the
proved fixed-axis theorem, retaining zero Bloch-vector axis choices. -/
theorem fixedSlice_rank_two_concurrence
    (H : HermitianMat (Fin 4) ℂ) (hH : H ∈ fixedSlice) (hrank : H.mat.rank ≤ 2) :
    concurrence (sliceState H hH) ≤ sliceWitness H := by
  have h := rank_two_fixed_axis_concurrence (sliceState H hH)
    (by rw [sliceState_rank]; exact hrank) Pauli.zAxis Pauli.zAxis
    (sliceState_axisA H hH) (sliceState_axisB H hH)
  rwa [transverseBound_sliceState] at h

theorem fixed_z_axis_concurrence_nonnegative (hWootters : WoottersSpectralFormula)
    (ρ : MState (Q × Q))
    (hA : IsMarginalAxis (marginalBlochA ρ) Pauli.zAxis)
    (hB : IsMarginalAxis (marginalBlochB ρ) Pauli.zAxis)
    (hwI : (twoQubitMatrix ρ 0 3).im = 0) (hzI : (twoQubitMatrix ρ 1 2).im = 0)
    (hwR : 0 ≤ (twoQubitMatrix ρ 0 3).re) (hzR : 0 ≤ (twoQubitMatrix ρ 1 2).re) :
    concurrence ρ ≤ transverseBound ρ Pauli.zAxis Pauli.zAxis := by
  have hρ := mem_fixedSlice_of_axes_gauge ρ hA hB hwI hzI hwR hzR
  have h := all_rank_fixedSlice_bound hWootters fixedSlice_rank_two_concurrence
    fixedSlice_zero_concurrence (qubitHermitian ρ) hρ
  rw [sliceState_qubitHermitian] at h
  rw [transverseBound_zAxis_gauge ρ hwI hzI hwR hzR]
  exact h

/-- The all-rank bound for the computational fixed axes, with arbitrary
complex antidiagonal entries handled by total local phases. -/
theorem fixed_z_axis_concurrence (hWootters : WoottersSpectralFormula)
    (ρ : MState (Q × Q))
    (hA : IsMarginalAxis (marginalBlochA ρ) Pauli.zAxis)
    (hB : IsMarginalAxis (marginalBlochB ρ) Pauli.zAxis) :
    concurrence ρ ≤ transverseBound ρ Pauli.zAxis Pauli.zAxis :=
  fixed_z_bound_of_nonnegative_gauge (fixed_z_axis_concurrence_nonnegative hWootters) ρ hA hB

/-- **EC2 Eq. (13), full stated scope.** Every two-qubit density matrix and
every prescribed pair of allowed marginal axes satisfy the transverse
correlation concurrence bound. Rank-deficient states and all choices at
vanishing marginal Bloch vectors are included by the definitions and proof. -/
theorem fixed_axis_concurrence (hWootters : WoottersSpectralFormula)
    (ρ : MState (Q × Q)) (n m : Vec3)
    (hn : IsMarginalAxis (marginalBlochA ρ) n)
    (hm : IsMarginalAxis (marginalBlochB ρ) m) :
    concurrence ρ ≤ transverseBound ρ n m := by
  obtain ⟨U,hU⟩ := Pauli.exists_axis_unitary n hn.1
  obtain ⟨V,hV⟩ := Pauli.exists_axis_unitary m hm.1
  have hn' : Pauli.rotation U⁻¹ n = Pauli.zAxis := by
    rw [← hU, Pauli.rotation_inverse]
  have hm' : Pauli.rotation V⁻¹ m = Pauli.zAxis := by
    rw [← hV, Pauli.rotation_inverse]
  have hA : IsMarginalAxis (marginalBlochA (localConj ρ U⁻¹ V⁻¹)) Pauli.zAxis := by
    rw [marginalBlochA_localConj, ← hn']
    exact marginalAxis_rotation _ _ U⁻¹ hn
  have hB : IsMarginalAxis (marginalBlochB (localConj ρ U⁻¹ V⁻¹)) Pauli.zAxis := by
    rw [marginalBlochB_localConj, ← hm']
    exact marginalAxis_rotation _ _ V⁻¹ hm
  have h := fixed_z_axis_concurrence hWootters (localConj ρ U⁻¹ V⁻¹) hA hB
  have hT := transverseBound_localConj ρ U⁻¹ V⁻¹ n m
  rw [hn', hm'] at hT
  rwa [concurrence_localConj, hT] at h

end EC2
