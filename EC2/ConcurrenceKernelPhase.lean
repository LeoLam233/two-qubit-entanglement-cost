import EC2.ConcurrenceKernelFace
import EC2.ConcurrencePhase
import EC2.ConcurrenceKernel

/-! # Removing the product-kernel coherence phase

The phase is total at zero, so the fixed-axis theorem on the product-kernel
face applies without excluding separable or singular endpoints.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix ComplexConjugate

namespace EC2
open ConcurrenceGeometry

theorem rank_localConj_le (ρ : MState (Q × Q)) (U V : Matrix.unitaryGroup Q ℂ) :
    (localConj ρ U V).m.rank ≤ ρ.m.rank := by
  change ((U ⊗ᵤ V).val * ρ.m * (U ⊗ᵤ V).val.conjTranspose).rank ≤ ρ.m.rank
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

/-- Equation (13) on the complete rank-at-most-two product-kernel face.
No reality or nonvanishing restriction is placed on its entries. -/
theorem fixed_axis_concurrence_zero_diagonal (ρ : MState (Q × Q))
    (hrank : ρ.m.rank ≤ 2) (hzero : ρ.m (0,1) (0,1) = 0)
    (n m : Vec3) (ha : IsMarginalAxis (marginalBlochA ρ) n)
    (hb : IsMarginalAxis (marginalBlochB ρ) m) :
    concurrence ρ ≤ transverseBound ρ n m := by
  let w := ρ.m (0,0) (1,1)
  let U := phaseUnitary 0
  let V := phaseUnitary w
  let σ := localConj ρ U V
  have hrank' : σ.m.rank ≤ 2 := (rank_localConj_le ρ U V).trans hrank
  have hzero' : σ.m (0,1) (0,1) = 0 := by
    simp [σ, U, V, localConj_phase_apply, phaseDiagonal, hzero]
  have hw : σ.m (0,0) (1,1) = (‖w‖ : ℂ) := by
    have hp0 : phaseOf 0 = 1 := by simp [phaseOf]
    calc
      σ.m (0,0) (1,1) = w * conj (phaseOf w) := by
        simp [σ, U, V, localConj_phase_apply, phaseDiagonal, hp0, w]
      _ = _ := mul_conj_phaseOf w
  have ha' : IsMarginalAxis (marginalBlochA σ) (Pauli.rotation U n) := by
    rw [show marginalBlochA σ = Pauli.rotation U (marginalBlochA ρ) from
      marginalBlochA_localConj ρ U V]
    exact marginalAxis_rotation _ _ U ha
  have hb' : IsMarginalAxis (marginalBlochB σ) (Pauli.rotation V m) := by
    rw [show marginalBlochB σ = Pauli.rotation V (marginalBlochB ρ) from
      marginalBlochB_localConj ρ U V]
    exact marginalAxis_rotation _ _ V hb
  have h := fixed_axis_concurrence_zero_diagonal_real σ hrank' hzero'
    (by rw [hw]; simp) (by rw [hw]; exact norm_nonneg w)
    (Pauli.rotation U n) (Pauli.rotation V m) ha' hb'
  change concurrence (localConj ρ U V) ≤
    transverseBound (localConj ρ U V) (Pauli.rotation U n) (Pauli.rotation V m) at h
  rwa [concurrence_localConj, transverseBound_localConj] at h

end EC2
