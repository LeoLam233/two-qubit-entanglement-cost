import EC2.ConcurrenceExpectations
import EC2.ConcurrenceAxes

/-! # Exact transverse maximum in the real antidiagonal gauge

The z-axis transverse plane depends only on the two antidiagonal entries.
For real nonnegative entries its maximum is exactly twice their sum. The
statement is about the actual Pauli-trace definition and makes no rank or
nonzero-marginal assumption.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix ComplexConjugate

namespace EC2
open ConcurrenceGeometry ConcurrenceBloch

theorem transverse_correlation_zAxis_gauge (ρ : MState (Q × Q))
    (hw : (ρ.m (0,0) (1,1)).im = 0) (hz : (ρ.m (0,1) (1,0)).im = 0)
    (u v : Vec3) (hu : dot3 Pauli.zAxis u = 0) (hv : dot3 Pauli.zAxis v = 0) :
    dot3 u ((correlationMatrix ρ).mulVec v) =
      transverseGauge (ρ.m (0,0) (1,1)).re (ρ.m (0,1) (1,0)).re
        ![u 0, u 1] ![v 0, v 1] := by
  have hu2 : u 2 = 0 := by simpa [dot3, Pauli.zAxis] using hu
  have hv2 : v 2 = 0 := by simpa [dot3, Pauli.zAxis] using hv
  have hstar (a b : Q × Q) : ρ.m b a = conj (ρ.m a b) := by
    simpa [Matrix.conjTranspose_apply] using
      (congrFun (congrFun ρ.Hermitian b) a).symm
  simp [dot3, transverseGauge, correlationMatrix, correlation, twoQubitMatrix,
    twoQubitIndex, pauliA, pauliB, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im,
    hu2, hv2, hstar (0,0) (1,1), hstar (0,1) (1,0), hw, hz]
  ring

/-- EC2 Eq. (20), with the maximum taken over the actual fixed transverse
planes and with zero antidiagonal entries included. -/
theorem transverseBound_zAxis_gauge (ρ : MState (Q × Q))
    (hwreal : (ρ.m (0,0) (1,1)).im = 0)
    (hzreal : (ρ.m (0,1) (1,0)).im = 0)
    (hwpos : 0 ≤ (ρ.m (0,0) (1,1)).re)
    (hzpos : 0 ≤ (ρ.m (0,1) (1,0)).re) :
    transverseBound ρ Pauli.zAxis Pauli.zAxis =
      2 * ((ρ.m (0,0) (1,1)).re + (ρ.m (0,1) (1,0)).re) := by
  apply le_antisymm
  · apply csSup_le (transverseValues_nonempty ρ Pauli.zAxis Pauli.zAxis)
    rintro r ⟨u,v,hu,hv,hun,hvn,rfl⟩
    rw [transverse_correlation_zAxis_gauge ρ hwreal hzreal u v hun hvn]
    have hu2 : u 2 = 0 := by simpa [dot3, Pauli.zAxis] using hun
    have hv2 : v 2 = 0 := by simpa [dot3, Pauli.zAxis] using hvn
    apply transverse_gauge_bound _ _ hwpos hzpos
    · simpa [sqLength, dot3, hu2, pow_two] using hu
    · simpa [sqLength, dot3, hv2, pow_two] using hv
  · let e : Vec3 := ![1,0,0]
    have he : sqLength e = 1 := by norm_num [e, sqLength, dot3]
    have hz : dot3 Pauli.zAxis e = 0 := by norm_num [e, Pauli.zAxis, dot3]
    apply le_transverseBound_of_witness ρ Pauli.zAxis Pauli.zAxis e e _ he he hz hz
    rw [transverse_correlation_zAxis_gauge ρ hwreal hzreal e e hz hz]
    simpa only [e, Matrix.cons_val_zero, Matrix.cons_val_one] using
      (le_of_eq (transverse_gauge_attains _ _ hwpos hzpos).symm)

end EC2
