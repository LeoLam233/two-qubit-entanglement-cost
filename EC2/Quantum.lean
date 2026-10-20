import QuantumInfo.States.Entanglement
import QuantumInfo.States.Pure.Qubit

/-! Concrete ordinary finite-dimensional quantum objects used by EC2.
Entropy and formation entanglement are in bits.  There are no extra
superselection constraints on states or ensembles. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace EC2

abbrev Q := Fin 2

def entropyBits {d : Type*} [Fintype d] [DecidableEq d] (ρ : MState d) : ℝ :=
  Sᵥₙ ρ / Real.log 2

def formationBits {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] [Nonempty a] [Nonempty b]
    (ρ : MState (a × b)) : ℝ := (EoF ρ : ℝ) / Real.log 2

theorem entropyBits_nonneg {d : Type*} [Fintype d] [DecidableEq d]
    (ρ : MState d) : 0 ≤ entropyBits ρ := by
  exact div_nonneg (Sᵥₙ_nonneg ρ) (Real.log_nonneg (by norm_num))

theorem formationBits_nonneg {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] [Nonempty a] [Nonempty b]
    (ρ : MState (a × b)) : 0 ≤ formationBits ρ := by
  exact div_nonneg (EoF ρ).2 (Real.log_nonneg (by norm_num))

theorem formationBits_pure {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] [Nonempty a] [Nonempty b]
    (ψ : Ket (a × b)) :
    formationBits (MState.pure ψ) = entropyBits (MState.pure ψ).traceRight := by
  unfold formationBits EoF
  rw [convex_roof_of_pure]
  rfl

section Matrices
variable {r s : Type*} [Fintype r] [Fintype s]

/-- Squared Frobenius norm, without any square-matrix restriction. -/
def matrixWeight (M : Matrix r s ℂ) : ℝ :=
  ∑ ab : r × s, Complex.normSq (M ab.1 ab.2)

theorem matrixWeight_nonneg (M : Matrix r s ℂ) : 0 ≤ matrixWeight M := by
  exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

@[simp] theorem matrixWeight_zero : matrixWeight (0 : Matrix r s ℂ) = 0 := by
  simp [matrixWeight]

theorem matrixWeight_eq_zero (M : Matrix r s ℂ) : matrixWeight M = 0 ↔ M = 0 := by
  classical
  constructor
  · intro h
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun ab (_ : ab ∈ (Finset.univ : Finset (r × s))) =>
        Complex.normSq_nonneg (M ab.1 ab.2))).mp h
    ext a b
    have hab := hz (a,b) (Finset.mem_univ _)
    simpa using hab
  · rintro rfl
    exact matrixWeight_zero

theorem matrixWeight_ne_zero_exists (M : Matrix r s ℂ) (h : matrixWeight M ≠ 0) :
    ∃ ab : r × s, M ab.1 ab.2 ≠ 0 := by
  by_contra hn
  push Not at hn
  apply h
  simp [matrixWeight, hn]

def ketOfMatrix (M : Matrix r s ℂ) (h : matrixWeight M = 1) : Ket (r × s) where
  vec ab := M ab.1 ab.2
  normalized' := by
    simpa [matrixWeight, Complex.normSq_eq_norm_sq] using h

variable [DecidableEq r] [DecidableEq s]

def gramState (M : Matrix r s ℂ) (h : matrixWeight M = 1) : MState r :=
  (MState.pure (ketOfMatrix M h)).traceRight

theorem gramState_matrix (M : Matrix r s ℂ) (h : matrixWeight M = 1) :
    (gramState M h).m = M * M.conjTranspose := by
  ext a b
  simp [gramState, ketOfMatrix, MState.m, MState.traceRight, MState.pure,
    HermitianMat.traceRight, Matrix.traceRight, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, Bra.eq_conj,
    Ket.apply]

/-- A weighted normalized block entropy. Its zero-block value is defined to be zero. -/
def weightedBlockEntropy (M : Matrix r s ℂ) : ℝ :=
  if h : matrixWeight M = 0 then 0
  else matrixWeight M * entropyBits
    (MState.pure (Ket.normalize (fun ab : r × s => M ab.1 ab.2)
      (matrixWeight_ne_zero_exists M h))).traceRight

@[simp] theorem weightedBlockEntropy_zero :
    weightedBlockEntropy (0 : Matrix r s ℂ) = 0 := by
  simp [weightedBlockEntropy]

theorem weightedBlockEntropy_of_zero_weight (M : Matrix r s ℂ)
    (h : matrixWeight M = 0) : weightedBlockEntropy M = 0 := by
  simp [weightedBlockEntropy, h]

theorem weightedBlockEntropy_nonneg (M : Matrix r s ℂ) :
    0 ≤ weightedBlockEntropy M := by
  unfold weightedBlockEntropy
  split
  · exact le_rfl
  · exact mul_nonneg (matrixWeight_nonneg M) (entropyBits_nonneg _)

def matrixBlock (M : Matrix (Q × r) (Q × s) ℂ) (i j : Q) : Matrix r s ℂ :=
  fun a b => M (i,a) (j,b)

end Matrices

/-- Reorders AA'BB' into AB A'B'. The underlying bipartition is always explicit. -/
def regroup (a b : Type*) : ((Q × Q) × (a × b)) ≃ ((Q × a) × (Q × b)) where
  toFun x := ((x.1.1,x.2.1),(x.1.2,x.2.2))
  invFun x := ((x.1.1,x.2.1),(x.1.2,x.2.2))
  left_inv := by rintro ⟨⟨_,_⟩,⟨_,_⟩⟩; rfl
  right_inv := by rintro ⟨⟨_,_⟩,⟨_,_⟩⟩; rfl

section Marginals
variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

def marginalAB (Ω : MState ((Q × a) × (Q × b))) : MState (Q × Q) :=
  (Ω.relabel (regroup a b)).traceRight

def marginalAux (Ω : MState ((Q × a) × (Q × b))) : MState (a × b) :=
  (Ω.relabel (regroup a b)).traceLeft

def partnerProduct (ρ : MState (Q × Q)) (σ : MState (a × b)) :
    MState ((Q × a) × (Q × b)) :=
  (ρ.prod σ).relabel (regroup a b).symm

@[simp] theorem marginalAB_partnerProduct (ρ : MState (Q × Q))
    (σ : MState (a × b)) : marginalAB (partnerProduct ρ σ) = ρ := by
  simp [marginalAB, partnerProduct, MState.relabel_relabel]

@[simp] theorem marginalAux_partnerProduct (ρ : MState (Q × Q))
    (σ : MState (a × b)) : marginalAux (partnerProduct ρ σ) = σ := by
  simp [marginalAux, partnerProduct, MState.relabel_relabel]

end Marginals
end EC2
