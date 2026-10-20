import EC2.Quantum
import EC2.ConcurrenceProductVector
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Finite

/-! # Product vectors in kernels of rank-at-most-two states

This file connects the algebraic product-vector theorem to the actual
matrix rank and kernel of every two-qubit density matrix.
-/

noncomputable section

namespace EC2
open ConcurrenceProductVector

/-- Every subspace of two-qubit coefficient vectors of dimension at least
two contains a nonzero product vector. -/
theorem subspace_contains_product (K : Submodule ℂ ((Q × Q) → ℂ))
    (hK : 2 ≤ Module.finrank ℂ K) :
    ∃ u v : Q → ℂ, u ≠ 0 ∧ v ≠ 0 ∧ (fun ab : Q × Q => u ab.1 * v ab.2) ∈ K := by
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank hK
  have hfpair : LinearIndependent ℂ ![f 0, f 1] := by
    convert hf using 1
    funext i
    fin_cases i <;> rfl
  let A : Mat2 := fun i j => (f 0).val (i,j)
  let B : Mat2 := fun i j => (f 1).val (i,j)
  have hAB : LinearIndependent ℂ ![A,B] := by
    apply LinearIndependent.pair_iff.mpr
    intro α β h
    apply LinearIndependent.pair_iff.mp hfpair α β
    apply Subtype.ext
    funext ab
    exact congrFun (congrFun h ab.1) ab.2
  obtain ⟨α, β, u, v, hu, hv, huv⟩ := two_dimensional_span_contains_product A B hAB
  refine ⟨u, v, hu, hv, ?_⟩
  have hmem := (α • f 0 + β • f 1).property
  have hvec : (α • f 0 + β • f 1).val = fun ab : Q × Q => u ab.1 * v ab.2 := by
    funext ab
    exact congrFun (congrFun huv ab.1) ab.2
  rw [hvec] at hmem
  exact hmem

/-- The first rank reduction in EC2 §3.1, now for ordinary normalized
quantum density matrices: every state of rank at most two has a nonzero
product vector in its kernel. -/
theorem rank_le_two_product_kernel (ρ : MState (Q × Q)) (hrank : ρ.m.rank ≤ 2) :
    ∃ u v : Q → ℂ, u ≠ 0 ∧ v ≠ 0 ∧
      ρ.m.mulVec (fun ab : Q × Q => u ab.1 * v ab.2) = 0 := by
  have hdim := ρ.m.mulVecLin.finrank_range_add_finrank_ker
  have hfour : Module.finrank ℂ ((Q × Q) → ℂ) = 4 := by
    simp [Module.finrank_pi, Q]
  rw [hfour] at hdim
  have hK : 2 ≤ Module.finrank ℂ (LinearMap.ker ρ.m.mulVecLin) := by
    change Module.finrank ℂ (LinearMap.range ρ.m.mulVecLin) ≤ 2 at hrank
    omega
  obtain ⟨u, v, hu, hv, huv⟩ := subspace_contains_product (LinearMap.ker ρ.m.mulVecLin) hK
  exact ⟨u, v, hu, hv, huv⟩

end EC2
