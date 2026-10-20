import EC2.ConcurrenceQuantum
import EC2.LocalUnitary

/-! # Local unitary invariance of the actual concurrence convex roof -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators NNReal Matrix ComplexConjugate

namespace EC2

/-- The two-qubit coefficient matrix keeps the A:B bipartition explicit. -/
def qubitCoefficient (ψ : Ket (Q × Q)) : Matrix Q Q ℂ := fun i j => ψ (i,j)

/-- Tensor-product unitary action sends the coefficient matrix to U A Vᵀ. -/
theorem qubitCoefficient_unitaryKet (U V : Matrix.unitaryGroup Q ℂ)
    (ψ : Ket (Q × Q)) :
    qubitCoefficient (unitaryKet (U ⊗ᵤ V) ψ) =
      U.val * qubitCoefficient ψ * V.val.transpose := by
  ext i j
  simp [qubitCoefficient, unitaryKet_apply, Matrix.mulVec, dotProduct,
    Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.unitary_kron_apply]
  ring

/-- The complex determinant of a unitary matrix has modulus one. -/
theorem unitary_det_norm {d : Type} [Fintype d] [DecidableEq d]
    (U : Matrix.unitaryGroup d ℂ) : ‖U.val.det‖ = 1 :=
  CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary U.prop)

/-- Pure two-qubit concurrence is unchanged by every local unitary. -/
theorem pureConcurrence_unitaryKet (U V : Matrix.unitaryGroup Q ℂ)
    (ψ : Ket (Q × Q)) :
    pureConcurrence (unitaryKet (U ⊗ᵤ V) ψ) = pureConcurrence ψ := by
  apply NNReal.eq
  have hdet : 2 * ‖(qubitCoefficient (unitaryKet (U ⊗ᵤ V) ψ)).det‖ =
      2 * ‖(qubitCoefficient ψ).det‖ := by
    rw [qubitCoefficient_unitaryKet, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_transpose, norm_mul, norm_mul, unitary_det_norm U, unitary_det_norm V]
    ring
  change 2 * ‖(unitaryKet (U ⊗ᵤ V) ψ) (0,0) * (unitaryKet (U ⊗ᵤ V) ψ) (1,1) -
      (unitaryKet (U ⊗ᵤ V) ψ) (0,1) * (unitaryKet (U ⊗ᵤ V) ψ) (1,0)‖ =
    2 * ‖ψ (0,0) * ψ (1,1) - ψ (0,1) * ψ (1,0)‖
  simpa only [Matrix.det_fin_two, qubitCoefficient] using hdet

/-- Local unitary invariance for every mixed two-qubit state, with no rank
restriction. This transports the ordinary finite pure-state convex roof. -/
theorem concurrence_localConj (ρ : MState (Q × Q)) (U V : Matrix.unitaryGroup Q ℂ) :
    concurrence (localConj ρ U V) = concurrence ρ := by
  unfold concurrence localConj
  rw [convex_roof_unitary_invariant phaseConcurrence (U ⊗ᵤ V)]
  intro ψ
  simpa only [phaseConcurrence_mk] using pureConcurrence_unitaryKet U V ψ

end EC2
