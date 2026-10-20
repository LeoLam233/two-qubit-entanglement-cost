import EC2.ConcurrenceReduction
import Mathlib.Analysis.Convex.Extreme

/-! Positive support perturbations and exact preservation of the affine slice. -/

noncomputable section
open scoped BigOperators
open Set

namespace EC2.ConcurrenceReduction

variable {r d : Type*} [Fintype r] [Fintype d] [DecidableEq r] [DecidableEq d]

/-- A sufficiently small real Hermitian perturbation of the identity is
positive semidefinite. This proof is uniform over zero eigenvalues and uses
the finite spectral calculus already proved by Physlib. -/
theorem exists_positive_identity_perturbation_radius (K : HermitianMat r ℂ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε → 0 ≤ (1 : HermitianMat r ℂ) + t • K := by
  let B : ℝ := ∑ i, |K.H.eigenvalues i|
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hBp : 0 < B+1 := by linarith
  refine ⟨1/(B+1), div_pos (by norm_num) hBp, ?_⟩
  intro t ht
  have heq : K.cfc (fun x => 1+t*x) = (1 : HermitianMat r ℂ) + t • K := by
    rw [HermitianMat.cfc_add_apply, HermitianMat.cfc_const,
      HermitianMat.cfc_const_mul_id, one_smul]
  rw [← heq, HermitianMat.cfc_nonneg_iff]
  intro i
  have hi : |K.H.eigenvalues i| ≤ B := by
    change |K.H.eigenvalues i| ≤ ∑ j, |K.H.eigenvalues j|
    exact Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset r)) =>
      abs_nonneg (K.H.eigenvalues j)) (Finset.mem_univ i)
  have habs : |t * K.H.eigenvalues i| < 1 := by
    rw [abs_mul]
    calc
      |t| * |K.H.eigenvalues i| ≤ |t| * (B+1) :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg t)
      _ < 1 := (lt_div_iff₀ hBp).mp ht
  linarith [neg_abs_le (t * K.H.eigenvalues i)]

/-- For the actual support factorization `ρ = R R†`, conjugating a small
identity perturbation gives two-sided PSD perturbations of `ρ`. -/
theorem exists_positive_supported_perturbation_radius
    (R : Matrix d r ℂ) (K : HermitianMat r ℂ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
      0 ≤ (1 : HermitianMat r ℂ).conj R + t • K.conj R := by
  obtain ⟨ε,hε,h⟩ := exists_positive_identity_perturbation_radius K
  refine ⟨ε,hε,fun t ht => ?_⟩
  have hp := HermitianMat.conj_nonneg R (h t ht)
  change 0 ≤ (HermitianMat.conjLinear ℝ R) ((1 : HermitianMat r ℂ) + t • K) at hp
  simpa only [map_add, map_smul, HermitianMat.conjLinear_apply] using hp

/-- A finite collection of nonnegative affine coordinates remains
nonnegative under small perturbations that preserve every active zero. -/
theorem exists_affine_nonnegative_radius {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hzero : ∀ i, a i = 0 → b i = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε → ∀ i, 0 ≤ a i + t*b i := by
  have hlocal (i : ι) : ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε → 0 ≤ a i + t*b i := by
    by_cases hz : a i = 0
    · exact ⟨1, by norm_num, fun t _ => by simp [hz,hzero i hz]⟩
    · have hp : 0 < a i := lt_of_le_of_ne (ha i) (Ne.symm hz)
      have hb : 0 < |b i|+1 := by positivity
      refine ⟨a i/(|b i|+1), div_pos hp hb, fun t ht => ?_⟩
      have hlt : |t*b i| < a i := by
        rw [abs_mul]
        calc
          |t| * |b i| ≤ |t| * (|b i|+1) :=
            mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg t)
          _ < a i := (lt_div_iff₀ hb).mp ht
      linarith [neg_abs_le (t*b i)]
  choose ε hε hεprop using hlocal
  let δ : ℝ := Finset.univ.inf' (by simp : (Finset.univ : Finset (Option ι)).Nonempty)
    (fun i => i.elim 1 ε)
  have hδ : 0 < δ := by
    apply (Finset.lt_inf'_iff _).mpr
    intro i _
    cases i with
    | none => norm_num
    | some i => exact hε i
  refine ⟨δ,hδ,fun t ht i => ?_⟩
  apply hεprop i t
  exact ht.trans_le (Finset.inf'_le _ (Finset.mem_univ (some i)))

/-- Every zero sign stays zero and each initially positive sign remains
nonnegative on a sufficiently small two-sided interval. -/
theorem exists_slice_sign_radius (ρ H : HermitianMat (Fin 4) ℂ)
    (hρ : ρ ∈ fixedSlice)
    (hpositive : 0 < signCoordinates ρ 0 + signCoordinates ρ 1)
    (hH : augmentedConstraints (activeSign ρ) H = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
      ∀ i : Fin 2, 0 ≤ signCoordinates (ρ+t•H) i := by
  have ha : ∀ i : Fin 2, 0 ≤ signCoordinates ρ i := by
    intro i
    fin_cases i
    · exact hρ.2.2.1
    · exact hρ.2.2.2
  obtain ⟨ε,hε,h⟩ := exists_affine_nonnegative_radius
    (signCoordinates ρ) (signCoordinates H) ha (all_zero_signs_preserved ρ H hpositive hH)
  refine ⟨ε,hε,fun t ht i => ?_⟩
  simpa only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h t ht i

/-- The dimension count and spectral neighborhood jointly produce a
nonzero two-sided feasible perturbation of the exact fixed slice. -/
theorem exists_feasible_supported_perturbation
    (R : Matrix (Fin 4) r ℂ) (L : Matrix r (Fin 4) ℂ) (hLR : L*R=1)
    (hρ : (1 : HermitianMat r ℂ).conj R ∈ fixedSlice)
    (hpositive : 0 < signCoordinates ((1 : HermitianMat r ℂ).conj R) 0 +
      signCoordinates ((1 : HermitianMat r ℂ).conj R) 1)
    (hr : 3 ≤ Fintype.card r) :
    ∃ H : HermitianMat (Fin 4) ℂ, H ≠ 0 ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
        (1 : HermitianMat r ℂ).conj R + t • H ∈ fixedSlice := by
  let ρ := (1 : HermitianMat r ℂ).conj R
  obtain ⟨K,hK,hHK,hc⟩ := exists_nonzero_supported_perturbation R L hLR
    (augmentedConstraints (activeSign ρ)) hr
  obtain ⟨ε₁,hε₁,hpos⟩ := exists_positive_supported_perturbation_radius R K
  obtain ⟨ε₂,hε₂,hsign⟩ := exists_slice_sign_radius ρ (K.conj R) hρ hpositive hc
  refine ⟨K.conj R,hHK,min ε₁ ε₂,lt_min hε₁ hε₂,fun t ht => ?_⟩
  have heq := (augmentedConstraints_eq_zero_iff (K.conj R) (activeSign ρ)).mp hc |>.2
  refine ⟨hpos t (ht.trans_le (min_le_left _ _)), ?_,
    hsign t (ht.trans_le (min_le_right _ _)) 0,
    hsign t (ht.trans_le (min_le_right _ _)) 1⟩
  simpa only [map_add,map_smul,heq,smul_zero,add_zero] using hρ.2.1

/-- A state with a full-column support factor of dimension at least three
and a positive antidiagonal sign is not an extreme point of the exact
fixed slice. The feasible perturbations, including active sign handling,
are constructed by the preceding theorems. -/
theorem not_extreme_of_fullRank_support
    (R : Matrix (Fin 4) r ℂ) (L : Matrix r (Fin 4) ℂ) (hLR : L*R=1)
    (hρ : (1 : HermitianMat r ℂ).conj R ∈ fixedSlice)
    (hpositive : 0 < signCoordinates ((1 : HermitianMat r ℂ).conj R) 0 +
      signCoordinates ((1 : HermitianMat r ℂ).conj R) 1)
    (hr : 3 ≤ Fintype.card r) :
    (1 : HermitianMat r ℂ).conj R ∉ fixedSlice.extremePoints ℝ := by
  obtain ⟨H,hH,ε,hε,hfeas⟩ := exists_feasible_supported_perturbation R L hLR hρ hpositive hr
  intro hx
  have hm := hfeas (-ε/2) (by rw [abs_of_neg (by linarith)]; linarith)
  have hp := hfeas (ε/2) (by rw [abs_of_pos (by linarith)]; linarith)
  have hos : (1 : HermitianMat r ℂ).conj R ∈
      openSegment ℝ ((1 : HermitianMat r ℂ).conj R + (-ε/2) • H)
        ((1 : HermitianMat r ℂ).conj R + (ε/2) • H) := by
    simpa only [sub_eq_add_neg, neg_smul, neg_div] using
      mem_openSegment_sub_add (𝕜 := ℝ) ((1 : HermitianMat r ℂ).conj R) ((ε/2) • H)
  have heq := hx.2 hm hp hos
  have hz : (-ε/2) • H = 0 := add_left_cancel (by simpa only [add_zero] using heq)
  exact hH ((smul_eq_zero.mp hz).resolve_left (by linarith))

end EC2.ConcurrenceReduction
