import EC2.ConcurrenceKernelPhase
import EC2.ConcurrenceKernelTransport

/-! # The complete rank-at-most-two fixed-axis concurrence theorem

A two-dimensional kernel contains a product vector. Explicit local unitaries
carry it to the computational `01` face; a total phase removes the remaining
coherence phase. The constructive Gram ensemble and plane-intersection bound
then apply, and exact local-unitary covariance returns the prescribed axes.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace EC2
open ConcurrenceGeometry

/-- Equation (13) for every two-qubit state of rank at most two, including
rank-one states and every fixed-axis choice at a zero marginal Bloch vector. -/
theorem rank_two_fixed_axis_concurrence (ρ : MState (Q × Q)) (hrank : ρ.m.rank ≤ 2)
    (n m : Vec3) (ha : IsMarginalAxis (marginalBlochA ρ) n)
    (hb : IsMarginalAxis (marginalBlochB ρ) m) :
    concurrence ρ ≤ transverseBound ρ n m := by
  obtain ⟨U,V,hzero⟩ := rank_le_two_exists_local_kernel_face ρ hrank
  have ha' : IsMarginalAxis (marginalBlochA (localConj ρ U V)) (Pauli.rotation U n) := by
    rw [marginalBlochA_localConj]
    exact marginalAxis_rotation _ _ U ha
  have hb' : IsMarginalAxis (marginalBlochB (localConj ρ U V)) (Pauli.rotation V m) := by
    rw [marginalBlochB_localConj]
    exact marginalAxis_rotation _ _ V hb
  have h := fixed_axis_concurrence_zero_diagonal (localConj ρ U V)
    ((rank_localConj_le ρ U V).trans hrank) hzero
    (Pauli.rotation U n) (Pauli.rotation V m) ha' hb'
  rwa [concurrence_localConj, transverseBound_localConj] at h

end EC2
