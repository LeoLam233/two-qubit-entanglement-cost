import EC2.LocalUnitary
import EC2.ConvexRoofFormation

/-! Local basis changes preserve the concrete bipartite entropy and EoF. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix Kronecker NNReal

namespace EC2

theorem trace_conjugate_pairing {a b : Type} [Fintype a] [Fintype b]
    (K : Matrix b a ℂ) (R : Matrix a a ℂ) (B : Matrix b b ℂ) :
    (K * R * K.conjTranspose * B).trace =
      (R * (K.conjTranspose * B * K)).trace := by
  calc
    _ = (K * (R * K.conjTranspose * B)).trace := by simp only [Matrix.mul_assoc]
    _ = ((R * K.conjTranspose * B) * K).trace := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

section Bipartite
variable {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

theorem matrix_traceRight_local_conj (R : Matrix (a × b) (a × b) ℂ)
    (U : Matrix.unitaryGroup a ℂ) (V : Matrix.unitaryGroup b ℂ) :
    ((U.val ⊗ₖ V.val) * R * (U.val ⊗ₖ V.val).conjTranspose).traceRight =
      U.val * R.traceRight * U.val.conjTranspose := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro A
  have hv : V.val.conjTranspose * V.val = 1 := V.prop.1
  have hk : (U.val ⊗ₖ V.val).conjTranspose * (A ⊗ₖ (1 : Matrix b b ℂ)) *
      (U.val ⊗ₖ V.val) = (U.val.conjTranspose * A * U.val) ⊗ₖ (1 : Matrix b b ℂ) := by
    simp only [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one, hv]
  calc
    _ = ((U.val ⊗ₖ V.val) * R * (U.val ⊗ₖ V.val).conjTranspose *
        (A ⊗ₖ (1 : Matrix b b ℂ))).trace := (Matrix.trace_mul_kron_one_right _ A).symm
    _ = (R * ((U.val ⊗ₖ V.val).conjTranspose * (A ⊗ₖ (1 : Matrix b b ℂ)) *
        (U.val ⊗ₖ V.val))).trace := trace_conjugate_pairing _ _ _
    _ = (R * ((U.val.conjTranspose * A * U.val) ⊗ₖ (1 : Matrix b b ℂ))).trace := by rw [hk]
    _ = (R.traceRight * (U.val.conjTranspose * A * U.val)).trace :=
      Matrix.trace_mul_kron_one_right _ _
    _ = _ := (trace_conjugate_pairing U.val R.traceRight A).symm

theorem matrix_traceLeft_local_conj (R : Matrix (a × b) (a × b) ℂ)
    (U : Matrix.unitaryGroup a ℂ) (V : Matrix.unitaryGroup b ℂ) :
    ((U.val ⊗ₖ V.val) * R * (U.val ⊗ₖ V.val).conjTranspose).traceLeft =
      V.val * R.traceLeft * V.val.conjTranspose := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro B
  have hu : U.val.conjTranspose * U.val = 1 := U.prop.1
  have hk : (U.val ⊗ₖ V.val).conjTranspose * ((1 : Matrix a a ℂ) ⊗ₖ B) *
      (U.val ⊗ₖ V.val) = (1 : Matrix a a ℂ) ⊗ₖ (V.val.conjTranspose * B * V.val) := by
    simp only [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one, hu]
  calc
    _ = ((U.val ⊗ₖ V.val) * R * (U.val ⊗ₖ V.val).conjTranspose *
        ((1 : Matrix a a ℂ) ⊗ₖ B)).trace := (Matrix.trace_mul_one_kron_right _ B).symm
    _ = (R * ((U.val ⊗ₖ V.val).conjTranspose * ((1 : Matrix a a ℂ) ⊗ₖ B) *
        (U.val ⊗ₖ V.val))).trace := trace_conjugate_pairing _ _ _
    _ = (R * ((1 : Matrix a a ℂ) ⊗ₖ (V.val.conjTranspose * B * V.val))).trace := by rw [hk]
    _ = (R.traceLeft * (V.val.conjTranspose * B * V.val)).trace :=
      Matrix.trace_mul_one_kron_right _ _
    _ = _ := (trace_conjugate_pairing V.val R.traceLeft B).symm

@[simp] theorem traceRight_localConj (ρ : MState (a × b))
    (U : Matrix.unitaryGroup a ℂ) (V : Matrix.unitaryGroup b ℂ) :
    (localConj ρ U V).traceRight = ρ.traceRight.uConj U := by
  apply MState.ext_m
  exact matrix_traceRight_local_conj ρ.m U V

@[simp] theorem traceLeft_localConj (ρ : MState (a × b))
    (U : Matrix.unitaryGroup a ℂ) (V : Matrix.unitaryGroup b ℂ) :
    (localConj ρ U V).traceLeft = ρ.traceLeft.uConj V := by
  apply MState.ext_m
  exact matrix_traceLeft_local_conj ρ.m U V

@[simp] theorem pure_entropy_localUnitary (ψ : Ket (a × b))
    (U : Matrix.unitaryGroup a ℂ) (V : Matrix.unitaryGroup b ℂ) :
    entropyBits (MState.pure (unitaryKet (U ⊗ᵤ V) ψ)).traceRight =
      entropyBits (MState.pure ψ).traceRight := by
  rw [pure_unitaryKet]
  change entropyBits (localConj (MState.pure ψ) U V).traceRight = _
  rw [traceRight_localConj, entropyBits_uConj]

variable [Nonempty a] [Nonempty b]

@[simp] theorem formationBits_localConj (ρ : MState (a × b))
    (U : Matrix.unitaryGroup a ℂ) (V : Matrix.unitaryGroup b ℂ) :
    formationBits (localConj ρ U V) = formationBits ρ := by
  have hc : ∀ ψ : Ket (a × b),
      formationPureCostNats (KetUpToPhase.mk (unitaryKet (U ⊗ᵤ V) ψ)) =
        formationPureCostNats (KetUpToPhase.mk ψ) := by
    intro ψ
    apply NNReal.eq
    simp only [formationPureCostNats_mk]
    rw [pure_unitaryKet]
    change Sᵥₙ (localConj (MState.pure ψ) U V).traceRight = _
    rw [traceRight_localConj]
    simp only [Sᵥₙ, MState.uConj_spectrum_eq]
  have hr := convex_roof_unitary_invariant formationPureCostNats (U ⊗ᵤ V) hc ρ
  unfold formationBits
  rw [EoF_eq_formationPureCostNats, EoF_eq_formationPureCostNats]
  exact congrArg (fun t : ℝ≥0 => (t : ℝ) / Real.log 2) hr

end Bipartite
end EC2
