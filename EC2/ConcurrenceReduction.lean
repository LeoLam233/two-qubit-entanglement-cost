import QuantumInfo.ForMathlib.HermitianMat.CFC
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Finite-dimensional perturbations for the fixed concurrence slice

The coordinate order is `00, 01, 10, 11`. The seven real slice equalities
are trace one, diagonal local marginals, and real antidiagonal entries.
These are the actual equalities of EC2 Section 3.2.
-/

noncomputable section
open scoped BigOperators ComplexConjugate
open Set

namespace EC2.ConcurrenceReduction

variable {r d : Type*} [Fintype r] [Fintype d] [DecidableEq r] [DecidableEq d]

/-- Every complex matrix is uniquely a Hermitian matrix plus `I` times a
Hermitian matrix. The equivalence is real-linear. -/
def matrixHermitianDecomposition (r : Type*) :
    Matrix r r ℂ ≃ₗ[ℝ] selfAdjoint (Matrix r r ℂ) × selfAdjoint (Matrix r r ℂ) where
  toFun A := (realPart A, imaginaryPart A)
  invFun p := (p.1 : Matrix r r ℂ) + Complex.I • (p.2 : Matrix r r ℂ)
  left_inv A := realPart_add_I_smul_imaginaryPart A
  right_inv p := by
    apply Prod.ext <;> simp
  map_add' A B := by
    apply Prod.ext <;> exact map_add _ A B
  map_smul' c A := by
    apply Prod.ext <;> exact map_smul _ c A

/-- A complex Hermitian `q × q` matrix has exactly `q²` real parameters. -/
theorem finrank_hermitian :
    Module.finrank ℝ (HermitianMat r ℂ) = Fintype.card r ^ 2 := by
  letI : Module.Finite ℝ (selfAdjoint (Matrix r r ℂ)) :=
    FiniteDimensional.finiteDimensional_submodule (selfAdjoint.submodule ℝ (Matrix r r ℂ))
  have h := (matrixHermitianDecomposition r).finrank_eq
  rw [Module.finrank_prod] at h
  change Module.finrank ℝ (Matrix r r ℂ) =
    Module.finrank ℝ (HermitianMat r ℂ) + Module.finrank ℝ (HermitianMat r ℂ) at h
  have hm : Module.finrank ℝ (Matrix r r ℂ) = 2 * Fintype.card r ^ 2 := by
    rw [Module.finrank_matrix, Complex.finrank_real_complex]
    ring
  rw [hm] at h
  omega

/-- Fewer than `q²` real homogeneous constraints leave a nonzero Hermitian
solution. No independence assumption on the constraints is needed. -/
theorem exists_nonzero_hermitian_kernel {k : ℕ}
    (L : HermitianMat r ℂ →ₗ[ℝ] (Fin k → ℝ))
    (hk : k < Fintype.card r ^ 2) :
    ∃ H : HermitianMat r ℂ, H ≠ 0 ∧ L H = 0 := by
  have hd : Module.finrank ℝ (Fin k → ℝ) < Module.finrank ℝ (HermitianMat r ℂ) := by
    simpa [Module.finrank_pi, finrank_hermitian] using hk
  obtain ⟨H, hmem, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := L) hd)
  exact ⟨H, hne, hmem⟩

theorem exists_nonzero_hermitian_kernel_eight
    (L : HermitianMat r ℂ →ₗ[ℝ] (Fin 8 → ℝ)) (hr : 3 ≤ Fintype.card r) :
    ∃ H : HermitianMat r ℂ, H ≠ 0 ∧ L H = 0 := by
  apply exists_nonzero_hermitian_kernel L
  nlinarith

/-- Conjugation by a rectangular matrix of full column rank is injective;
the left inverse is a concrete witness of that rank condition. -/
theorem conj_injective_of_leftInverse (R : Matrix d r ℂ) (L : Matrix r d ℂ)
    (hLR : L * R = 1) :
    Function.Injective (HermitianMat.conj R : HermitianMat r ℂ → HermitianMat d ℂ) := by
  intro A B h
  have hh := congrArg (HermitianMat.conj L) h
  simpa only [HermitianMat.conj_conj, hLR, HermitianMat.conj_one] using hh

/-- A full-rank support factor with at least three columns admits a nonzero
supported Hermitian perturbation satisfying eight prescribed real linear
constraints. The perturbation is the actual matrix `R K R†`. -/
theorem exists_nonzero_supported_perturbation
    (R : Matrix d r ℂ) (L : Matrix r d ℂ) (hLR : L * R = 1)
    (constraints : HermitianMat d ℂ →ₗ[ℝ] (Fin 8 → ℝ))
    (hr : 3 ≤ Fintype.card r) :
    ∃ K : HermitianMat r ℂ, K ≠ 0 ∧ K.conj R ≠ 0 ∧ constraints (K.conj R) = 0 := by
  obtain ⟨K, hK, hc⟩ := exists_nonzero_hermitian_kernel_eight
    (constraints.comp (HermitianMat.conjLinear ℝ R)) hr
  refine ⟨K, hK, ?_, hc⟩
  intro hz
  apply hK
  apply conj_injective_of_leftInverse R L hLR
  simpa using hz

@[simp] theorem hermitian_add_apply (A B : HermitianMat d ℂ) (i j : d) :
    (A+B) i j = A i j + B i j := rfl

/-- The seven real equality coordinates of the fixed affine slice. -/
def sliceEqualities : HermitianMat (Fin 4) ℂ →ₗ[ℝ] (Fin 7 → ℝ) where
  toFun H := ![H.trace,
    (H 0 2 + H 1 3).re, (H 0 2 + H 1 3).im,
    (H 0 1 + H 2 3).re, (H 0 1 + H 2 3).im,
    (H 0 3).im, (H 1 2).im]
  map_add' A B := by
    ext i
    fin_cases i <;> simp [add_add_add_comm]
  map_smul' c A := by
    ext i
    fin_cases i <;> simp [HermitianMat.smul_apply, mul_add]

/-- The two nonnegative antidiagonal coordinates `w` and `z`. -/
def signCoordinates : HermitianMat (Fin 4) ℂ →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun H := ![(H 0 3).re, (H 1 2).re]
  map_add' A B := by
    ext i
    fin_cases i <;> simp
  map_smul' c A := by
    ext i
    fin_cases i <;> simp [HermitianMat.smul_apply]

def fixedSlice : Set (HermitianMat (Fin 4) ℂ) :=
  {ρ | 0 ≤ ρ ∧ sliceEqualities ρ = ![1,0,0,0,0,0,0] ∧
    0 ≤ signCoordinates ρ 0 ∧ 0 ≤ signCoordinates ρ 1}

/-- The eighth constraint preserves one of the two sign coordinates. -/
def augmentedConstraints (active : Fin 2) :
    HermitianMat (Fin 4) ℂ →ₗ[ℝ] (Fin 8 → ℝ) where
  toFun H := Fin.cons (signCoordinates H active) (sliceEqualities H)
  map_add' A B := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.cons, map_add]
  map_smul' c A := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.cons, map_smul]

theorem augmentedConstraints_eq_zero_iff (H : HermitianMat (Fin 4) ℂ) (active : Fin 2) :
    augmentedConstraints active H = 0 ↔
      signCoordinates H active = 0 ∧ sliceEqualities H = 0 := by
  change (Fin.cons (signCoordinates H active) (sliceEqualities H) : Fin 8 → ℝ) = 0 ↔ _
  constructor
  · intro h
    constructor
    · exact congrFun h 0
    · ext i
      exact congrFun h i.succ
  · rintro ⟨h₁,h₂⟩
    rw [h₁,h₂]
    ext i
    exact Fin.cases rfl (fun _ => rfl) i

/-- Choose an active zero sign when present. If both signs are positive, an
extra equality preserving `z` is harmless because nine parameters remain. -/
def activeSign (ρ : HermitianMat (Fin 4) ℂ) : Fin 2 :=
  if signCoordinates ρ 0 = 0 then 0 else 1

theorem all_zero_signs_preserved (ρ H : HermitianMat (Fin 4) ℂ)
    (hpositive : 0 < signCoordinates ρ 0 + signCoordinates ρ 1)
    (hH : augmentedConstraints (activeSign ρ) H = 0) :
    ∀ i : Fin 2, signCoordinates ρ i = 0 → signCoordinates H i = 0 := by
  have hc := (augmentedConstraints_eq_zero_iff H (activeSign ρ)).mp hH |>.1
  intro i hi
  fin_cases i
  · change signCoordinates ρ 0 = 0 at hi
    change signCoordinates H 0 = 0
    simpa [activeSign, hi] using hc
  · change signCoordinates ρ 1 = 0 at hi
    change signCoordinates H 1 = 0
    by_cases hw : signCoordinates ρ 0 = 0
    · exfalso
      simp [hw, hi] at hpositive
    · simpa [activeSign, hw] using hc

/-- The elementary identity used to reconstruct a parent from the two
endpoints of a feasible perturbation interval. -/
theorem endpoint_convex_identity (ρ H : HermitianMat d ℂ) (a b : ℝ)
    (ha : a < 0) (hb : 0 < b) :
    (b / (b-a)) • (ρ + a • H) + (-a / (b-a)) • (ρ + b • H) = ρ := by
  have hab : b-a ≠ 0 := by linarith
  rw [smul_add, smul_add, smul_smul, smul_smul]
  have hweights : b / (b-a) + -a / (b-a) = 1 := by field_simp; ring
  have hzero : b / (b-a) * a + -a / (b-a) * b = 0 := by ring
  rw [add_add_add_comm, ← add_smul, ← add_smul, hweights, hzero, one_smul, zero_smul, add_zero]

end EC2.ConcurrenceReduction
