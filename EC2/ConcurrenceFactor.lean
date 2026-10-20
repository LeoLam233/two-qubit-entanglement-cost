import EC2.ConcurrenceSupport
import Mathlib.Data.Fin.Embedding

/-! Standard `Fin n` support factors, with proved zero-column padding. -/

noncomputable section
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

namespace EC2.ConcurrenceReduction

variable {d : Type*} [Fintype d] [DecidableEq d]

theorem exists_rank_factor (ρ : HermitianMat d ℂ) (hρ : 0 ≤ ρ) :
    ∃ R : Matrix d (Fin ρ.mat.rank) ℂ, R * R.conjTranspose = ρ.mat := by
  let e : spectralSupport ρ ≃ Fin ρ.mat.rank :=
    Fintype.equivOfCardEq (by rw [spectralSupport_card,Fintype.card_fin])
  refine ⟨(spectralSupportFactor ρ).submatrix id e.symm, ?_⟩
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    spectralSupport_factorization ρ hρ]
  rfl

def extendColumns {r s : Type*} (e : r ↪ s) (R : Matrix d r ℂ) : Matrix d s ℂ :=
  fun i => Function.extend e (R i) 0

theorem gram_extendColumns {r s : Type*} [Fintype r] [Fintype s] [DecidableEq s]
    (e : r ↪ s) (R : Matrix d r ℂ) :
    extendColumns e R * (extendColumns e R).conjTranspose = R * R.conjTranspose := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, extendColumns]
  calc
    (∑ j : s, Function.extend e (R i) 0 j * conj (Function.extend e (R k) 0 j)) =
        ∑ j : s, Function.extend e (fun a => R i a * conj (R k a)) 0 j := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : ∃ a, e a = j
      · obtain ⟨a,rfl⟩ := hj
        simp only [e.injective.extend_apply]
      · simp only [Function.extend_apply' _ _ _ hj, Pi.zero_apply, map_zero, mul_zero]
    _ = ∑ a : r, R i a * conj (R k a) :=
      Finset.sum_extend_zero_of_injective (fun a => R i a * conj (R k a)) e.injective
        (fun a => Finset.mem_univ (e a))

/-- Every PSD matrix of rank at most `n` has an actual `n`-column Gram
factor; unused columns are zero. In particular `n = 2` includes rank zero
and rank one without any limiting argument. -/
theorem exists_rank_le_factor {n : ℕ} (ρ : HermitianMat d ℂ)
    (hρ : 0 ≤ ρ) (hrank : ρ.mat.rank ≤ n) :
    ∃ R : Matrix d (Fin n) ℂ, R * R.conjTranspose = ρ.mat := by
  obtain ⟨R,hR⟩ := exists_rank_factor ρ hρ
  exact ⟨extendColumns (Fin.castLEEmb hrank) R, (gram_extendColumns _ _).trans hR⟩

end EC2.ConcurrenceReduction
