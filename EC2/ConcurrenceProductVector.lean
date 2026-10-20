import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Product vectors in two-dimensional two-qubit subspaces

The first reduction in EC2 §3.1 is proved here by an explicit quadratic root
and an explicit rank-one factorization.  No density-matrix rank hypothesis
or product-vector existence axiom is imported.
-/

namespace EC2
namespace ConcurrenceProductVector

noncomputable section

open Matrix

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

theorem complex_quadratic_has_root (a b d : ℂ) (ha : a ≠ 0) :
    ∃ z : ℂ, a * z ^ 2 + b * z + d = 0 := by
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (b ^ 2 - 4 * a * d) (n := 2) (by norm_num)
  refine ⟨(-b + r) / (2 * a), ?_⟩
  field_simp [ha]
  linear_combination hr

/-- Every two-dimensional complex subspace of 2×2 coefficient matrices
contains a nonzero singular matrix. -/
theorem exists_nonzero_singular_combination (A B : Mat2)
    (hAB : LinearIndependent ℂ ![A, B]) :
    ∃ α β : ℂ, α • A + β • B ≠ 0 ∧ Matrix.det (α • A + β • B) = 0 := by
  by_cases hB : Matrix.det B = 0
  · refine ⟨0, 1, ?_, ?_⟩
    · simpa using hAB.ne_zero 1
    · simpa using hB
  let b := A 0 0 * B 1 1 + B 0 0 * A 1 1 - A 0 1 * B 1 0 - B 0 1 * A 1 0
  obtain ⟨z, hz⟩ := complex_quadratic_has_root (Matrix.det B) b (Matrix.det A) hB
  refine ⟨1, z, ?_, ?_⟩
  · intro hzero
    have h := (LinearIndependent.pair_iff.mp hAB) 1 z hzero
    norm_num at h
  · have hid : Matrix.det (1 • A + z • B) = Matrix.det B * z ^ 2 + b * z + Matrix.det A := by
      simp [Matrix.det_fin_two, Matrix.add_apply, Matrix.smul_apply, b]
      ring
    simpa only [one_smul] using hid.trans hz

/-- A nonzero singular 2×2 complex matrix is an outer product of nonzero
vectors.  This is the product-state criterion used by EC2. -/
theorem singular_nonzero_is_product (A : Mat2) (hA : A ≠ 0) (hd : Matrix.det A = 0) :
    ∃ u v : Fin 2 → ℂ, u ≠ 0 ∧ v ≠ 0 ∧ A = Matrix.vecMulVec u v := by
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 0 := by simpa [Matrix.det_fin_two] using hd
  by_cases h00 : A 0 0 ≠ 0
  · refine ⟨![A 0 0, A 1 0], ![1, A 0 1 / A 0 0], ?_, ?_, ?_⟩
    · intro h
      have h0 := congrFun h 0
      simpa using h00 h0
    · intro h
      have h0 := congrFun h 0
      norm_num at h0
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.vecMulVec]
      · field_simp [h00]
      · field_simp [h00]
        linear_combination hdet
  have h00z : A 0 0 = 0 := not_ne_iff.mp h00
  by_cases h01 : A 0 1 ≠ 0
  · have h10 : A 1 0 = 0 := by
      have hprod : A 0 1 * A 1 0 = 0 := by simpa [h00z] using hdet
      exact (mul_eq_zero.mp hprod).resolve_left h01
    refine ⟨![A 0 1, A 1 1], ![0, 1], ?_, ?_, ?_⟩
    · intro h
      have h0 := congrFun h 0
      simpa using h01 h0
    · intro h
      have h1 := congrFun h 1
      norm_num at h1
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.vecMulVec, h00z, h10]
  have h01z : A 0 1 = 0 := not_ne_iff.mp h01
  refine ⟨![0, 1], ![A 1 0, A 1 1], ?_, ?_, ?_⟩
  · intro h
    have h1 := congrFun h 1
    norm_num at h1
  · intro h
    apply hA
    have h10 := congrFun h 0
    have h11 := congrFun h 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp_all
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.vecMulVec, h00z, h01z]

/-- The full product-vector conclusion of the first sentence in EC2 §3.1. -/
theorem two_dimensional_span_contains_product (A B : Mat2)
    (hAB : LinearIndependent ℂ ![A, B]) :
    ∃ (α β : ℂ) (u v : Fin 2 → ℂ),
      u ≠ 0 ∧ v ≠ 0 ∧ α • A + β • B = Matrix.vecMulVec u v := by
  obtain ⟨α, β, hnonzero, hdet⟩ := exists_nonzero_singular_combination A B hAB
  obtain ⟨u, v, hu, hv, huv⟩ := singular_nonzero_is_product (α • A + β • B) hnonzero hdet
  exact ⟨α, β, u, v, hu, hv, huv⟩

end
end ConcurrenceProductVector
end EC2
