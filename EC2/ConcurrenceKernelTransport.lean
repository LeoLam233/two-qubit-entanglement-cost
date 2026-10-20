import EC2.ConcurrenceAlignment
import EC2.ConcurrenceKernel

/-! # Transporting every product kernel to a computational kernel face

The local unitaries are explicitly completed from the normalized product
factors. No invertibility of the density matrix or nonzero marginal is used.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix Kronecker ComplexConjugate

namespace EC2

/-- A kernel column of the inverse basis gives a zero computational
population after the corresponding unitary change of basis. -/
theorem uConj_diagonal_zero_of_kernel_column {d : Type} [Fintype d] [DecidableEq d]
    (ρ : MState d) (U : Matrix.unitaryGroup d ℂ) (i : d)
    (hk : ρ.m.mulVec (U.val.conjTranspose.col i) = 0) :
    (ρ.uConj U).m i i = 0 := by
  have hc (j : d) : (ρ.m * U.val.conjTranspose) j i = 0 := congrFun hk j
  change (U.val * ρ.m * U.val.conjTranspose) i i = 0
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [hc, mul_zero, Finset.sum_const_zero]

/-- Normalizing either nonzero factor retains a product kernel. -/
theorem normalize_product_kernel (ρ : MState (Q × Q)) (u v : Q → ℂ)
    (hu : ∃ i, u i ≠ 0) (hv : ∃ i, v i ≠ 0)
    (hk : ρ.m.mulVec (fun ab : Q × Q => u ab.1 * v ab.2) = 0) :
    ρ.m.mulVec (fun ab : Q × Q => (Ket.normalize u hu) ab.1 *
      (Ket.normalize v hv) ab.2) = 0 := by
  let cu : ℂ := (Real.sqrt (∑ i, ‖u i‖ ^ 2) : ℂ)⁻¹
  let cv : ℂ := (Real.sqrt (∑ i, ‖v i‖ ^ 2) : ℂ)⁻¹
  have he : (fun ab : Q × Q => (Ket.normalize u hu) ab.1 *
      (Ket.normalize v hv) ab.2) =
      (cu * cv) • (fun ab : Q × Q => u ab.1 * v ab.2) := by
    funext ab
    simp only [Ket.normalize, Ket.apply, Pi.smul_apply, smul_eq_mul, cu, cv,
      div_eq_mul_inv]
    ring
  rw [he, Matrix.mulVec_smul, hk, smul_zero]

theorem qubitCompletion_second_column (ψ : Ket Q) (i : Q) :
    (qubitCompletion ψ * Qubit.X).val i 1 = ψ i := by
  change ((qubitCompletion ψ).val * Qubit.X.val) i 1 = ψ i
  simp [Matrix.mul_apply, Fin.sum_univ_two, Qubit.X,
    qubitCompletion_first_column]

/-- Adjoint of the inverse local basis, at the underlying matrix level. -/
theorem inverse_local_unitary_adjoint (U V : Matrix.unitaryGroup Q ℂ) :
    (U⁻¹ ⊗ᵤ V⁻¹).val.conjTranspose = U.val ⊗ₖ V.val := by
  ext ab cd
  change conj (conj (U.val ab.1 cd.1) * conj (V.val ab.2 cd.2)) =
    U.val ab.1 cd.1 * V.val ab.2 cd.2
  simp

/-- Every nonzero product kernel can be moved to the exact `01` computational
face by local qubit unitaries. This applies at every rank having such a kernel. -/
theorem exists_local_unitary_kernel_face (ρ : MState (Q × Q)) (u v : Q → ℂ)
    (hu : u ≠ 0) (hv : v ≠ 0)
    (hk : ρ.m.mulVec (fun ab : Q × Q => u ab.1 * v ab.2) = 0) :
    ∃ U V : Matrix.unitaryGroup Q ℂ,
      (localConj ρ U V).m (0,1) (0,1) = 0 := by
  have hu' : ∃ i, u i ≠ 0 := by
    by_contra h
    apply hu
    push Not at h
    exact funext h
  have hv' : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv
    push Not at h
    exact funext h
  let α := Ket.normalize u hu'
  let β := Ket.normalize v hv'
  let U := qubitCompletion α
  let V := qubitCompletion β * Qubit.X
  refine ⟨U⁻¹, V⁻¹, ?_⟩
  apply uConj_diagonal_zero_of_kernel_column
  rw [inverse_local_unitary_adjoint]
  have he : (U.val ⊗ₖ V.val).col (0,1) =
      fun ab : Q × Q => α ab.1 * β ab.2 := by
    funext ab
    change U.val ab.1 0 * V.val ab.2 1 = α ab.1 * β ab.2
    rw [qubitCompletion_first_column, qubitCompletion_second_column]
  rw [he]
  exact normalize_product_kernel ρ u v hu' hv' hk

/-- The kernel-face reduction for every rank-at-most-two two-qubit state. -/
theorem rank_le_two_exists_local_kernel_face (ρ : MState (Q × Q)) (hr : ρ.m.rank ≤ 2) :
    ∃ U V : Matrix.unitaryGroup Q ℂ,
      (localConj ρ U V).m (0,1) (0,1) = 0 := by
  obtain ⟨u,v,hu,hv,hk⟩ := rank_le_two_product_kernel ρ hr
  exact exists_local_unitary_kernel_face ρ u v hu hv hk

end EC2
