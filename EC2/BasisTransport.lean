import EC2.LocalEntropy
import EC2.BlockPureClosure

/-!
# Qubit measurement basis changes with arbitrary auxiliary systems

Only `A` and `B` are rotated. The `AA':BB'` pure entropy, the `AB` formation
entanglement, and the exact `A'B'` marginal transform as required in Section 4.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix Kronecker

namespace EC2

theorem relabel_uConj_of_matrix {d e : Type} [Fintype d] [Fintype e]
    [DecidableEq d] [DecidableEq e] (ρ : MState d)
    (U : Matrix.unitaryGroup d ℂ) (f : e ≃ d) (V : Matrix.unitaryGroup e ℂ)
    (hV : V.val = U.val.submatrix f f) :
    (ρ.uConj U).relabel f = (ρ.relabel f).uConj V := by
  apply MState.ext_m
  change (U.val * ρ.m * U.val.conjTranspose).submatrix f f =
    V.val * ρ.m.submatrix f f * V.val.conjTranspose
  simp only [hV, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]

def coefficientMatrix {a b : Type} [Fintype a] [Fintype b] (ψ : Ket (a × b)) :
    Matrix a b ℂ := fun i j => ψ (i,j)

theorem coefficientMatrix_weight {a b : Type} [Fintype a] [Fintype b]
    (ψ : Ket (a × b)) : matrixWeight (coefficientMatrix ψ) = 1 := ψ.normalized

@[simp] theorem ketOfMatrix_coefficientMatrix {a b : Type} [Fintype a] [Fintype b]
    (ψ : Ket (a × b)) :
    ketOfMatrix (coefficientMatrix ψ) (coefficientMatrix_weight ψ) = ψ := by
  ext i
  rfl

section Auxiliary
variable {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

def qubitBasisChange (Ω : MState ((Q × a) × (Q × b)))
    (U V : Matrix.unitaryGroup Q ℂ) : MState ((Q × a) × (Q × b)) :=
  localConj Ω (U ⊗ᵤ (1 : Matrix.unitaryGroup a ℂ))
    (V ⊗ᵤ (1 : Matrix.unitaryGroup b ℂ))

def qubitBasisKet (ψ : Ket ((Q × a) × (Q × b)))
    (U V : Matrix.unitaryGroup Q ℂ) : Ket ((Q × a) × (Q × b)) :=
  unitaryKet ((U ⊗ᵤ (1 : Matrix.unitaryGroup a ℂ)) ⊗ᵤ
    (V ⊗ᵤ (1 : Matrix.unitaryGroup b ℂ))) ψ

theorem pure_qubitBasisKet (ψ : Ket ((Q × a) × (Q × b)))
    (U V : Matrix.unitaryGroup Q ℂ) :
    MState.pure (qubitBasisKet ψ U V) = qubitBasisChange (MState.pure ψ) U V :=
  pure_unitaryKet _ _

theorem regroup_qubitBasisChange (Ω : MState ((Q × a) × (Q × b)))
    (U V : Matrix.unitaryGroup Q ℂ) :
    (qubitBasisChange Ω U V).relabel (regroup a b) =
      localConj (Ω.relabel (regroup a b)) (U ⊗ᵤ V) (1 : Matrix.unitaryGroup (a × b) ℂ) := by
  apply relabel_uConj_of_matrix
  ext x y
  rcases x with ⟨⟨i,j⟩,⟨a₁,b₁⟩⟩
  rcases y with ⟨⟨k,l⟩,⟨a₂,b₂⟩⟩
  change (U.val i k * V.val j l) *
    (1 : Matrix (a × b) (a × b) ℂ) (a₁,b₁) (a₂,b₂) =
    (U.val i k * (1 : Matrix a a ℂ) a₁ a₂) *
      (V.val j l * (1 : Matrix b b ℂ) b₁ b₂)
  simp only [Matrix.one_apply, Prod.mk.injEq]
  split_ifs <;> simp_all <;> ring

@[simp] theorem marginalAB_qubitBasisChange (Ω : MState ((Q × a) × (Q × b)))
    (U V : Matrix.unitaryGroup Q ℂ) :
    marginalAB (qubitBasisChange Ω U V) = localConj (marginalAB Ω) U V := by
  unfold marginalAB
  rw [regroup_qubitBasisChange, traceRight_localConj]
  rfl

@[simp] theorem marginalAux_qubitBasisChange (Ω : MState ((Q × a) × (Q × b)))
    (U V : Matrix.unitaryGroup Q ℂ) :
    marginalAux (qubitBasisChange Ω U V) = marginalAux Ω := by
  unfold marginalAux
  rw [regroup_qubitBasisChange, traceLeft_localConj, uConj_one]

@[simp] theorem pure_entropy_qubitBasisKet (ψ : Ket ((Q × a) × (Q × b)))
    (U V : Matrix.unitaryGroup Q ℂ) :
    entropyBits (MState.pure (qubitBasisKet ψ U V)).traceRight =
      entropyBits (MState.pure ψ).traceRight :=
  pure_entropy_localUnitary _ _ _

variable [Nonempty a] [Nonempty b]

@[simp] theorem formationBits_AB_qubitBasisKet (ψ : Ket ((Q × a) × (Q × b)))
    (U V : Matrix.unitaryGroup Q ℂ) :
    formationBits (marginalAB (MState.pure (qubitBasisKet ψ U V))) =
      formationBits (marginalAB (MState.pure ψ)) := by
  rw [pure_qubitBasisKet, marginalAB_qubitBasisChange, formationBits_localConj]

@[simp] theorem formationBits_aux_qubitBasisKet (ψ : Ket ((Q × a) × (Q × b)))
    (U V : Matrix.unitaryGroup Q ℂ) :
    formationBits (marginalAux (MState.pure (qubitBasisKet ψ U V))) =
      formationBits (marginalAux (MState.pure ψ)) := by
  rw [pure_qubitBasisKet, marginalAux_qubitBasisChange]

/-- The balanced coefficient argument may be applied in any qubit measurement
basis, while retaining the original state and bipartitions in the conclusion. -/
theorem pure_entropy_bound_of_qubit_measurement
    (ψ : Ket ((Q × a) × (Q × b))) (U V : Matrix.unitaryGroup Q ℂ) (x y : ℝ)
    (h00 : matrixWeight (matrixBlock (coefficientMatrix (qubitBasisKet ψ U V)) 0 0) = x/2)
    (h01 : matrixWeight (matrixBlock (coefficientMatrix (qubitBasisKet ψ U V)) 0 1) = y/2)
    (h10 : matrixWeight (matrixBlock (coefficientMatrix (qubitBasisKet ψ U V)) 1 0) = y/2)
    (h11 : matrixWeight (matrixBlock (coefficientMatrix (qubitBasisKet ψ U V)) 1 1) = x/2)
    (hxy : x+y=1)
    (hHanner : Entropy.RectangularHanner (a ⊕ a) (b ⊕ b))
    (hAB : formationBits (marginalAB (MState.pure ψ)) ≤ Entropy.wBits |x-y|) :
    formationBits (marginalAB (MState.pure ψ)) +
      formationBits (marginalAux (MState.pure ψ)) ≤ entropyBits (MState.pure ψ).traceRight := by
  have h := pure_entropy_bound_of_balanced_blocks
    (coefficientMatrix (qubitBasisKet ψ U V)) x y
    (coefficientMatrix_weight _) h00 h01 h10 h11 hxy hHanner
    (by simpa only [ketOfMatrix_coefficientMatrix, formationBits_AB_qubitBasisKet] using hAB)
  simpa only [ketOfMatrix_coefficientMatrix, formationBits_AB_qubitBasisKet,
    formationBits_aux_qubitBasisKet, pure_entropy_qubitBasisKet] using h

end Auxiliary
end EC2
