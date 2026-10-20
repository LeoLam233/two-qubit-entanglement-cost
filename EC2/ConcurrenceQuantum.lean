import EC2.Quantum
import EC2.ConcurrenceBloch
import EC2.ConcurrenceCompact
import EC2.ConvexRoofQuantum

/-! # Concrete concurrence and fixed-axis target definitions

Concurrence is the ordinary finite pure-state convex roof of twice the
absolute determinant of the two-qubit coefficient matrix.  Phase invariance
is proved before passing to Physlib's quotient of kets by global phase.
This is the standard convex-roof concurrence characterized by Wootters.
-/

noncomputable section
open scoped BigOperators NNReal

namespace EC2

def pureConcurrence (ψ : Ket (Q × Q)) : ℝ≥0 :=
  ⟨2 * ‖ψ (0,0) * ψ (1,1) - ψ (0,1) * ψ (1,0)‖,
    mul_nonneg (by norm_num) (norm_nonneg _)⟩

theorem pureConcurrence_phase_invariant (ψ φ : Ket (Q × Q))
    (h : Ket.PhaseEquiv.r ψ φ) : pureConcurrence ψ = pureConcurrence φ := by
  obtain ⟨z, hz, hvec⟩ := h
  have hcoord (i : Q × Q) : ψ i = z * φ i := by
    simpa [Ket.apply] using congrFun hvec i
  have hdet : ψ (0,0) * ψ (1,1) - ψ (0,1) * ψ (1,0) =
      z ^ 2 * (φ (0,0) * φ (1,1) - φ (0,1) * φ (1,0)) := by
    simp only [hcoord]
    ring
  apply NNReal.eq
  change 2 * ‖ψ (0,0) * ψ (1,1) - ψ (0,1) * ψ (1,0)‖ =
    2 * ‖φ (0,0) * φ (1,1) - φ (0,1) * φ (1,0)‖
  rw [hdet, norm_mul, norm_pow, hz]
  simp [pureConcurrence]

def phaseConcurrence : KetUpToPhase (Q × Q) → ℝ≥0 :=
  KetUpToPhase.lift pureConcurrence pureConcurrence_phase_invariant

@[simp] theorem phaseConcurrence_mk (ψ : Ket (Q × Q)) :
    phaseConcurrence (KetUpToPhase.mk ψ) = pureConcurrence ψ :=
  KetUpToPhase.lift_mk _ _ _

/-- The exact convex-roof concurrence; all finite pure-state ensembles enter
the infimum, and no rank restriction is imposed. -/
def concurrence (ρ : MState (Q × Q)) : ℝ := (convex_roof phaseConcurrence ρ : ℝ)

theorem concurrence_nonneg (ρ : MState (Q × Q)) : 0 ≤ concurrence ρ :=
  (convex_roof phaseConcurrence ρ).coe_nonneg

theorem concurrence_pure (ψ : Ket (Q × Q)) :
    concurrence (MState.pure ψ) =
      2 * ‖ψ (0,0) * ψ (1,1) - ψ (0,1) * ψ (1,0)‖ := by
  simp only [concurrence, convex_roof_of_pure, phaseConcurrence_mk]
  rfl

theorem pureConcurrence_le_one (ψ : Ket (Q × Q)) : pureConcurrence ψ ≤ 1 := by
  have hnorm : ‖ψ (0,0)‖ ^ 2 + ‖ψ (0,1)‖ ^ 2 +
      ‖ψ (1,0)‖ ^ 2 + ‖ψ (1,1)‖ ^ 2 = 1 := by
    simpa [Fintype.sum_prod_type, Fin.sum_univ_two, add_assoc, Complex.normSq_eq_norm_sq] using ψ.normalized
  have htri : ‖ψ (0,0) * ψ (1,1) - ψ (0,1) * ψ (1,0)‖ ≤
      ‖ψ (0,0)‖ * ‖ψ (1,1)‖ + ‖ψ (0,1)‖ * ‖ψ (1,0)‖ := by
    simpa only [norm_mul] using norm_sub_le (ψ (0,0) * ψ (1,1)) (ψ (0,1) * ψ (1,0))
  change 2 * ‖ψ (0,0) * ψ (1,1) - ψ (0,1) * ψ (1,0)‖ ≤ 1
  nlinarith only [hnorm, htri, sq_nonneg (‖ψ (0,0)‖ - ‖ψ (1,1)‖),
    sq_nonneg (‖ψ (0,1)‖ - ‖ψ (1,0)‖)]

theorem concurrence_pure_product (ψ φ : Ket Q) :
    concurrence (MState.pure (ψ.prod φ)) = 0 := by
  rw [concurrence_pure]
  have hdet : (ψ.prod φ) (0,0) * (ψ.prod φ) (1,1) -
      (ψ.prod φ) (0,1) * (ψ.prod φ) (1,0) = 0 := by
    simp [Ket.prod, Ket.apply]
    ring
  rw [hdet]
  simp

theorem concurrence_finite_jensen {ι : Type} [Fintype ι]
    (e : MEnsemble (Q × Q) ι) :
    concurrence (Ensemble.mix e) ≤ ∑ i, (e.distr i : ℝ) * concurrence (e.states i) :=
  convex_roof_finite_jensen phaseConcurrence e

theorem concurrence_le_one (ρ : MState (Q × Q)) : concurrence ρ ≤ 1 := by
  let e := Ensemble.spectral_ensemble ρ
  have hroof : concurrence ρ ≤
      (Ensemble.pure_average_NNReal (phaseConcurrence ∘ KetUpToPhase.mk) e : ℝ) := by
    have h := convex_roof_le_any_ensemble phaseConcurrence e
    simpa [concurrence, e, Ensemble.spectral_ensemble_mix] using h
  apply hroof.trans
  rw [pure_average_real]
  calc
    ∑ i, (e.distr i : ℝ) * (phaseConcurrence (KetUpToPhase.mk (e.states i)) : ℝ) ≤
        ∑ i, (e.distr i : ℝ) * 1 := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left
      · exact pureConcurrence_le_one _
      · exact (e.distr i).zero_le_coe
    _ = 1 := by simpa using e.distr.normalized

/-- Computational-basis flattening, preserving the order 00,01,10,11. -/
def twoQubitIndex : Fin 4 → Q × Q := ![(0,0), (0,1), (1,0), (1,1)]

def twoQubitMatrix (ρ : MState (Q × Q)) : ConcurrenceAlgebra.Mat4 :=
  fun i j => ρ.m (twoQubitIndex i) (twoQubitIndex j)

def marginalBlochA (ρ : MState (Q × Q)) : ConcurrenceGeometry.Vec3 :=
  ConcurrenceBloch.blochA (twoQubitMatrix ρ)

def marginalBlochB (ρ : MState (Q × Q)) : ConcurrenceGeometry.Vec3 :=
  ConcurrenceBloch.blochB (twoQubitMatrix ρ)

def correlationMatrix (ρ : MState (Q × Q)) : Matrix (Fin 3) (Fin 3) ℝ :=
  ConcurrenceBloch.correlation (twoQubitMatrix ρ)

/-- An allowed marginal eigenaxis.  When the Bloch vector vanishes,
the coefficient can be zero and every unit axis remains allowed. -/
def IsMarginalAxis (a n : ConcurrenceGeometry.Vec3) : Prop :=
  ConcurrenceGeometry.sqLength n = 1 ∧ ∃ α : ℝ, a = fun i => α * n i

theorem zero_has_every_unit_axis (n : ConcurrenceGeometry.Vec3)
    (hn : ConcurrenceGeometry.sqLength n = 1) : IsMarginalAxis 0 n := by
  refine ⟨hn, 0, ?_⟩
  ext i
  simp

def transverseValues (ρ : MState (Q × Q)) (n m : ConcurrenceGeometry.Vec3) : Set ℝ :=
  {z | ∃ u v : ConcurrenceGeometry.Vec3,
    ConcurrenceGeometry.sqLength u = 1 ∧ ConcurrenceGeometry.sqLength v = 1 ∧
    ConcurrenceGeometry.dot3 n u = 0 ∧ ConcurrenceGeometry.dot3 m v = 0 ∧
    z = |ConcurrenceGeometry.dot3 u ((correlationMatrix ρ).mulVec v)|}

def transverseBound (ρ : MState (Q × Q)) (n m : ConcurrenceGeometry.Vec3) : ℝ :=
  sSup (transverseValues ρ n m)

theorem transverseValues_nonempty (ρ : MState (Q × Q))
    (n m : ConcurrenceGeometry.Vec3) : (transverseValues ρ n m).Nonempty := by
  obtain ⟨u, hu, hn⟩ := ConcurrenceGeometry.exists_unit_perpendicular n
  obtain ⟨v, hv, hm⟩ := ConcurrenceGeometry.exists_unit_perpendicular m
  exact ⟨_, u, v, hu, hv, hn, hm, rfl⟩

theorem transverseValues_bddAbove (ρ : MState (Q × Q))
    (n m : ConcurrenceGeometry.Vec3) : BddAbove (transverseValues ρ n m) := by
  refine ⟨∑ i, ∑ j, |correlationMatrix ρ i j|, ?_⟩
  rintro z ⟨u, v, hu, hv, _, _, rfl⟩
  exact ConcurrenceGeometry.unit_correlation_bounded (correlationMatrix ρ) u v hu hv

theorem transverseBound_nonneg (ρ : MState (Q × Q))
    (n m : ConcurrenceGeometry.Vec3) : 0 ≤ transverseBound ρ n m := by
  obtain ⟨z, hz⟩ := transverseValues_nonempty ρ n m
  have hz0 : 0 ≤ z := by
    obtain ⟨u, v, _, _, _, _, rfl⟩ := hz
    exact abs_nonneg _
  exact hz0.trans (le_csSup (transverseValues_bddAbove ρ n m) hz)

theorem le_transverseBound_of_witness (ρ : MState (Q × Q))
    (n m u v : ConcurrenceGeometry.Vec3) (c : ℝ)
    (hu : ConcurrenceGeometry.sqLength u = 1)
    (hv : ConcurrenceGeometry.sqLength v = 1)
    (hn : ConcurrenceGeometry.dot3 n u = 0)
    (hm : ConcurrenceGeometry.dot3 m v = 0)
    (hc : c ≤ |ConcurrenceGeometry.dot3 u ((correlationMatrix ρ).mulVec v)|) :
    c ≤ transverseBound ρ n m :=
  hc.trans (le_csSup (transverseValues_bddAbove ρ n m) ⟨u, v, hu, hv, hn, hm, rfl⟩)

/-- The fixed-axis bound is an actual attained maximum, as in the manuscript,
for every state and every pair of fixed axes. -/
theorem transverseBound_attained (ρ : MState (Q × Q))
    (n m : ConcurrenceGeometry.Vec3) :
    ∃ u v : ConcurrenceGeometry.Vec3,
      ConcurrenceGeometry.sqLength u = 1 ∧ ConcurrenceGeometry.sqLength v = 1 ∧
      ConcurrenceGeometry.dot3 n u = 0 ∧ ConcurrenceGeometry.dot3 m v = 0 ∧
      transverseBound ρ n m =
        |ConcurrenceGeometry.dot3 u ((correlationMatrix ρ).mulVec v)| := by
  obtain ⟨u, v, hu, hv, hn, hm, hmax⟩ :=
    ConcurrenceCompact.exists_maximal_unit_correlation (correlationMatrix ρ) n m
  refine ⟨u, v, hu, hv, hn, hm, le_antisymm ?_ ?_⟩
  · apply csSup_le (transverseValues_nonempty ρ n m)
    rintro z ⟨x, y, hx, hy, hxn, hym, rfl⟩
    exact hmax x y hx hy hxn hym
  · exact le_csSup (transverseValues_bddAbove ρ n m) ⟨u, v, hu, hv, hn, hm, rfl⟩

theorem concurrence_zero_fixed_axis_bound (ρ : MState (Q × Q))
    (hρ : concurrence ρ = 0) (n m : ConcurrenceGeometry.Vec3) :
    concurrence ρ ≤ transverseBound ρ n m := by
  rw [hρ]
  exact transverseBound_nonneg ρ n m

end EC2
