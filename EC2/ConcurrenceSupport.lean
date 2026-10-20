import EC2.ConcurrencePerturbation

/-! Full-column PSD support factors from the actual finite spectral theorem. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexConjugate
open Matrix
attribute [local instance] Classical.propDecidable

namespace EC2.ConcurrenceReduction

variable {d : Type*} [Fintype d] [DecidableEq d]

def spectralSupport (ρ : HermitianMat d ℂ) := {i : d // ρ.H.eigenvalues i ≠ 0}

instance (ρ : HermitianMat d ℂ) : Fintype (spectralSupport ρ) :=
  inferInstanceAs (Fintype {i : d // ρ.H.eigenvalues i ≠ 0})

instance (ρ : HermitianMat d ℂ) : DecidableEq (spectralSupport ρ) :=
  inferInstanceAs (DecidableEq {i : d // ρ.H.eigenvalues i ≠ 0})

def spectralSupportFactor (ρ : HermitianMat d ℂ) : Matrix d (spectralSupport ρ) ℂ :=
  fun i j => ρ.H.eigenvectorUnitary i j.1 * (Real.sqrt (ρ.H.eigenvalues j.1) : ℂ)

def spectralSupportLeftInverse (ρ : HermitianMat d ℂ) : Matrix (spectralSupport ρ) d ℂ :=
  fun j i => conj (ρ.H.eigenvectorUnitary i j.1) / (Real.sqrt (ρ.H.eigenvalues j.1) : ℂ)

theorem spectralSupport_card (ρ : HermitianMat d ℂ) :
    Fintype.card (spectralSupport ρ) = ρ.mat.rank :=
  ρ.H.rank_eq_card_non_zero_eigs.symm

theorem spectralSupport_sqrt_ne_zero (ρ : HermitianMat d ℂ) (hρ : 0 ≤ ρ)
    (j : spectralSupport ρ) : (Real.sqrt (ρ.H.eigenvalues j.1) : ℂ) ≠ 0 := by
  have hp : 0 < ρ.H.eigenvalues j.1 :=
    lt_of_le_of_ne (HermitianMat.eigenvalues_nonneg hρ j.1) (Ne.symm j.2)
  exact_mod_cast (Real.sqrt_pos.mpr hp).ne'

theorem spectralSupport_leftInverse (ρ : HermitianMat d ℂ) (hρ : 0 ≤ ρ) :
    spectralSupportLeftInverse ρ * spectralSupportFactor ρ = 1 := by
  ext j k
  let U : Matrix d d ℂ := ρ.H.eigenvectorUnitary
  have hU : U.conjTranspose * U = 1 := ρ.H.eigenvectorUnitary.2.1
  have hsum :
      (spectralSupportLeftInverse ρ * spectralSupportFactor ρ) j k =
        ((Real.sqrt (ρ.H.eigenvalues k.1) : ℂ) /
          (Real.sqrt (ρ.H.eigenvalues j.1) : ℂ)) * (U.conjTranspose * U) j.1 k.1 := by
    simp only [Matrix.mul_apply, spectralSupportLeftInverse, spectralSupportFactor,
      Matrix.conjTranspose_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [U]
    ring
  rw [hsum,hU]
  by_cases h : j=k
  · subst k
    simp [Matrix.one_apply, spectralSupport_sqrt_ne_zero ρ hρ j]
  · have hval : j.1 ≠ k.1 := fun hh => h (Subtype.ext hh)
    simp [Matrix.one_apply,h,hval]

theorem spectralSupport_factorization (ρ : HermitianMat d ℂ) (hρ : 0 ≤ ρ) :
    spectralSupportFactor ρ * (spectralSupportFactor ρ).conjTranspose = ρ.mat := by
  let U : Matrix d d ℂ := ρ.H.eigenvectorUnitary
  have hspec : ρ.mat = U * Matrix.diagonal (fun i => (ρ.H.eigenvalues i : ℂ)) * U.conjTranspose := by
    simpa only [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using ρ.H.spectral_theorem
  rw [hspec]
  ext i k
  have hs :
      (∑ j : spectralSupport ρ,
        U i j.1 * (ρ.H.eigenvalues j.1 : ℂ) * conj (U k j.1)) =
      ∑ j : d, U i j * (ρ.H.eigenvalues j : ℂ) * conj (U k j) := by
    have h := Fintype.sum_subtype_add_sum_subtype (fun j => ρ.H.eigenvalues j ≠ 0)
      (fun j => U i j * (ρ.H.eigenvalues j : ℂ) * conj (U k j))
    have hz : (∑ j : {j : d // ¬ρ.H.eigenvalues j ≠ 0},
        U i j.1 * (ρ.H.eigenvalues j.1 : ℂ) * conj (U k j.1)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      have hj : ρ.H.eigenvalues j.1 = 0 := not_not.mp j.2
      simp [hj]
    rw [hz,add_zero] at h
    exact h
  calc
    (spectralSupportFactor ρ * (spectralSupportFactor ρ).conjTranspose) i k =
        ∑ j : spectralSupport ρ, U i j.1 * (ρ.H.eigenvalues j.1 : ℂ) * conj (U k j.1) := by
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro j _
      have hsqrt : (Real.sqrt (ρ.H.eigenvalues j.1) : ℂ)^2 = (ρ.H.eigenvalues j.1 : ℂ) := by
        exact_mod_cast Real.sq_sqrt (HermitianMat.eigenvalues_nonneg hρ j.1)
      simp only [spectralSupportFactor, Matrix.conjTranspose_apply]
      dsimp [U]
      rw [← hsqrt]
      simp only [map_mul, Complex.conj_ofReal]
      ring
    _ = ∑ j : d, U i j * (ρ.H.eigenvalues j : ℂ) * conj (U k j) := hs
    _ = (U * Matrix.diagonal (fun j => (ρ.H.eigenvalues j : ℂ)) * U.conjTranspose) i k := by
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
      rfl

theorem spectralSupport_conj_one (ρ : HermitianMat d ℂ) (hρ : 0 ≤ ρ) :
    (1 : HermitianMat (spectralSupport ρ) ℂ).conj (spectralSupportFactor ρ) = ρ := by
  apply HermitianMat.ext
  simpa only [HermitianMat.conj_apply_mat,HermitianMat.mat_one,Matrix.mul_one] using
    spectralSupport_factorization ρ hρ

/-- The exact extreme-point rank reduction in manuscript Section 3.2:
every extreme point of the fixed slice has rank at most two or both
antidiagonal entries zero. -/
theorem extreme_fixedSlice_rank_or_zero
    (ρ : HermitianMat (Fin 4) ℂ) (hρ : ρ ∈ fixedSlice.extremePoints ℝ) :
    ρ.mat.rank ≤ 2 ∨ (signCoordinates ρ 0 = 0 ∧ signCoordinates ρ 1 = 0) := by
  by_cases hr : ρ.mat.rank ≤ 2
  · exact Or.inl hr
  · right
    have hmem : ρ ∈ fixedSlice := hρ.1
    by_contra hz
    have hp : 0 < signCoordinates ρ 0 + signCoordinates ρ 1 := by
      rcases lt_or_eq_of_le (hmem.2.2.1) with hw | hw
      · linarith [hmem.2.2.2]
      · have hz' : signCoordinates ρ 1 ≠ 0 := by
          intro hh
          exact hz ⟨hw.symm,hh⟩
        exact lt_of_le_of_ne (by linarith [hmem.2.2.2]) (by
          intro hh
          apply hz'
          linarith)
    have hn := not_extreme_of_fullRank_support (spectralSupportFactor ρ)
      (spectralSupportLeftInverse ρ) (spectralSupport_leftInverse ρ hmem.1)
      (by rwa [spectralSupport_conj_one ρ hmem.1])
      (by simpa only [spectralSupport_conj_one ρ hmem.1] using hp)
      (by rw [spectralSupport_card]; omega)
    rw [spectralSupport_conj_one ρ hmem.1] at hn
    exact hn hρ

end EC2.ConcurrenceReduction
