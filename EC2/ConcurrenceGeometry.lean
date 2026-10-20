import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The fixed-axis geometric step in the EC2 concurrence proof

The coordinates here carry the Euclidean scalar product, written explicitly
to keep the result independent of a particular density-matrix library.  No
nonzero assumption is made on either marginal Bloch vector.  In particular,
the geometric estimate respects any preselected axes at a zero marginal.
-/

namespace EC2
namespace ConcurrenceGeometry

noncomputable section

abbrev Vec3 := Fin 3 → ℝ

def dot3 (u v : Vec3) : ℝ := u 0 * v 0 + u 1 * v 1 + u 2 * v 2

def sqLength (u : Vec3) : ℝ := dot3 u u

/-- The coordinate representation is the standard real Euclidean space. -/
def asEuclidean (v : Vec3) : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 v

theorem dot3_eq_dotProduct (u v : Vec3) : dot3 u v = u ⬝ᵥ v := by
  simp [dot3, dotProduct, Fin.sum_univ_three]

theorem asEuclidean_norm_sq (v : Vec3) : ‖asEuclidean v‖ ^ 2 = sqLength v := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [asEuclidean, sqLength, dot3,
    Fin.sum_univ_three, pow_two]

theorem sqLength_eq_one_iff_norm (v : Vec3) : sqLength v = 1 ↔ ‖asEuclidean v‖ = 1 := by
  rw [← asEuclidean_norm_sq]
  constructor
  · intro h
    nlinarith [norm_nonneg (asEuclidean v)]
  · intro h
    rw [h]
    norm_num

def cross3 (a b : Vec3) : Vec3 :=
  ![a 1 * b 2 - a 2 * b 1,
    a 2 * b 0 - a 0 * b 2,
    a 0 * b 1 - a 1 * b 0]

def diagAction (c N : ℝ) (v : Vec3) : Vec3 := ![c * v 0, -c * v 1, N * v 2]

theorem dot3_comm (u v : Vec3) : dot3 u v = dot3 v u := by
  unfold dot3
  ring

theorem sqLength_nonneg (v : Vec3) : 0 ≤ sqLength v := by
  unfold sqLength dot3
  nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]

theorem sqLength_pos_of_coord {v : Vec3} (i : Fin 3) (hi : v i ≠ 0) :
    0 < sqLength v := by
  fin_cases i
  · change v 0 ≠ 0 at hi
    have hp := sq_pos_of_ne_zero hi
    unfold sqLength dot3
    nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  · change v 1 ≠ 0 at hi
    have hp := sq_pos_of_ne_zero hi
    unfold sqLength dot3
    nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  · change v 2 ≠ 0 at hi
    have hp := sq_pos_of_ne_zero hi
    unfold sqLength dot3
    nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]

theorem cross3_perp_left (a b : Vec3) : dot3 a (cross3 a b) = 0 := by
  simp [dot3, cross3]
  ring

theorem cross3_perp_right (a b : Vec3) : dot3 b (cross3 a b) = 0 := by
  simp [dot3, cross3]
  ring

/-- Any two homogeneous real equations in three unknowns have a nonzero
solution.  This explicit proof includes coinciding or zero normals. -/
theorem common_perpendicular (a b : Vec3) :
    ∃ v : Vec3, dot3 a v = 0 ∧ dot3 b v = 0 ∧ 0 < sqLength v := by
  by_cases hc : ∃ i : Fin 3, cross3 a b i ≠ 0
  · obtain ⟨i, hi⟩ := hc
    exact ⟨cross3 a b, cross3_perp_left a b, cross3_perp_right a b,
      sqLength_pos_of_coord i hi⟩
  have hz : ∀ i : Fin 3, cross3 a b i = 0 := by
    intro i
    by_contra hi
    exact hc ⟨i, hi⟩
  have hz1 : a 2 * b 0 - a 0 * b 2 = 0 := by simpa [cross3] using hz 1
  have hz2 : a 0 * b 1 - a 1 * b 0 = 0 := by simpa [cross3] using hz 2
  by_cases ha0 : a 0 ≠ 0
  · refine ⟨![-a 1, a 0, 0], ?_, ?_, ?_⟩
    · simp [dot3]
      ring
    · simp [dot3]
      nlinarith
    · apply sqLength_pos_of_coord 1
      simpa using ha0
  by_cases ha1 : a 1 ≠ 0
  · refine ⟨![-a 1, a 0, 0], ?_, ?_, ?_⟩
    · simp [dot3]
      ring
    · simp [dot3]
      nlinarith
    · apply sqLength_pos_of_coord 0
      simpa using ha1
  have ha0z : a 0 = 0 := not_ne_iff.mp ha0
  have ha1z : a 1 = 0 := not_ne_iff.mp ha1
  by_cases ha2 : a 2 ≠ 0
  · refine ⟨![a 2, 0, 0], ?_, ?_, ?_⟩
    · simp [dot3, ha0z]
    · simp [dot3]
      simpa [ha0z, mul_comm] using hz1
    · apply sqLength_pos_of_coord 0
      simpa using ha2
  have ha2z : a 2 = 0 := not_ne_iff.mp ha2
  by_cases hb0 : b 0 ≠ 0
  · refine ⟨![-b 1, b 0, 0], ?_, ?_, ?_⟩
    · simp [dot3, ha0z, ha1z, ha2z]
    · simp [dot3]
      ring
    · apply sqLength_pos_of_coord 1
      simpa using hb0
  by_cases hb1 : b 1 ≠ 0
  · refine ⟨![-b 1, b 0, 0], ?_, ?_, ?_⟩
    · simp [dot3, ha0z, ha1z, ha2z]
    · simp [dot3]
      ring
    · apply sqLength_pos_of_coord 0
      simpa using hb1
  refine ⟨![1, 0, 0], ?_, ?_, ?_⟩
  · simp [dot3, ha0z]
  · simp [dot3, not_ne_iff.mp hb0]
  · norm_num [sqLength, dot3]

def normalize (v : Vec3) : Vec3 := fun i => v i / Real.sqrt (sqLength v)

theorem dot3_div_right (a v : Vec3) (s : ℝ) :
    dot3 a (fun i => v i / s) = dot3 a v / s := by
  unfold dot3
  ring

theorem dot3_div_left (a v : Vec3) (s : ℝ) :
    dot3 (fun i => a i / s) v = dot3 a v / s := by
  unfold dot3
  ring

theorem sqLength_div (v : Vec3) (s : ℝ) :
    sqLength (fun i => v i / s) = sqLength v / s ^ 2 := by
  unfold sqLength dot3
  ring

theorem normalize_unit {v : Vec3} (hv : 0 < sqLength v) :
    sqLength (normalize v) = 1 := by
  change sqLength (fun i => v i / Real.sqrt (sqLength v)) = 1
  rw [sqLength_div, Real.sq_sqrt hv.le]
  exact div_self (ne_of_gt hv)

theorem normalize_perp {a v : Vec3} (h : dot3 a v = 0) :
    dot3 a (normalize v) = 0 := by
  change dot3 a (fun i => v i / Real.sqrt (sqLength v)) = 0
  rw [dot3_div_right, h, zero_div]

/-- The least singular value of diag(c,-c,N) is at least c whenever
`0 ≤ c ≤ N`, expressed without choosing singular-value machinery. -/
theorem diagAction_sqLength_lower (c N : ℝ) (hc : 0 ≤ c) (hN : c ≤ N) (v : Vec3) :
    c ^ 2 * sqLength v ≤ sqLength (diagAction c N v) := by
  have hN2 : 0 ≤ N ^ 2 - c ^ 2 := by nlinarith
  have h := mul_nonneg hN2 (sq_nonneg (v 2))
  simp [sqLength, dot3, diagAction]
  nlinarith only [h]

theorem diagAction_dot_comm (c N : ℝ) (a v : Vec3) :
    dot3 a (diagAction c N v) = dot3 (diagAction c N a) v := by
  simp [dot3, diagAction]
  ring

theorem diagAction_normalize (c N : ℝ) (v : Vec3) :
    diagAction c N (normalize v) =
      fun i => diagAction c N v i / Real.sqrt (sqLength v) := by
  funext i
  fin_cases i <;> simp [diagAction, normalize] <;> ring

/-- The geometric content of EC2 Eq. (19).  The normals are arbitrary and
remain fixed throughout the construction. -/
theorem fixed_axes_diagonal_lower (c N : ℝ) (hc : 0 < c) (hN : c ≤ N)
    (n m : Vec3) :
    ∃ u v : Vec3,
      sqLength u = 1 ∧ sqLength v = 1 ∧
      dot3 n u = 0 ∧ dot3 m v = 0 ∧
      c ≤ dot3 u (diagAction c N v) := by
  obtain ⟨w, hwN, hwM, hwpos⟩ := common_perpendicular (diagAction c N n) m
  let v := normalize w
  have hvunit : sqLength v = 1 := normalize_unit hwpos
  have hvm : dot3 m v = 0 := normalize_perp hwM
  have hvn : dot3 n (diagAction c N v) = 0 := by
    rw [diagAction_dot_comm]
    exact normalize_perp hwN
  have hlower : c ^ 2 ≤ sqLength (diagAction c N v) := by
    simpa [hvunit] using diagAction_sqLength_lower c N hc.le hN v
  have hpos : 0 < sqLength (diagAction c N v) := by nlinarith
  let u := normalize (diagAction c N v)
  have huunit : sqLength u = 1 := normalize_unit hpos
  have hun : dot3 n u = 0 := normalize_perp hvn
  refine ⟨u, v, huunit, hvunit, hun, hvm, ?_⟩
  have hspos : 0 < Real.sqrt (sqLength (diagAction c N v)) := Real.sqrt_pos.2 hpos
  have hs2 : (Real.sqrt (sqLength (diagAction c N v))) ^ 2 =
      sqLength (diagAction c N v) := Real.sq_sqrt hpos.le
  have hroot : c ≤ Real.sqrt (sqLength (diagAction c N v)) := by nlinarith
  have hvalue : dot3 u (diagAction c N v) =
      Real.sqrt (sqLength (diagAction c N v)) := by
    change dot3 (fun i => diagAction c N v i /
      Real.sqrt (sqLength (diagAction c N v))) (diagAction c N v) = _
    rw [dot3_div_left]
    change sqLength (diagAction c N v) /
      Real.sqrt (sqLength (diagAction c N v)) = _
    apply (div_eq_iff (ne_of_gt hspos)).2
    nlinarith
  rw [hvalue]
  exact hroot

def correctedAction (c N : ℝ) (a b v : Vec3) : Vec3 :=
  fun i => diagAction c N v i + a i * v 2 - (if i = 2 then dot3 b v else 0)

/-- EC2 Eq. (18): both correction terms vanish in the prescribed
transverse planes, also when either Bloch vector vanishes. -/
theorem corrections_vanish (c N : ℝ) (a b u v : Vec3)
    (hua : dot3 u a = 0) (hbv : dot3 b v = 0) :
    dot3 u (correctedAction c N a b v) = dot3 u (diagAction c N v) := by
  have hid : dot3 u (correctedAction c N a b v) =
      dot3 u (diagAction c N v) + dot3 u a * v 2 - u 2 * dot3 b v := by
    simp [dot3, correctedAction, diagAction]
    ring
  rw [hid, hua, hbv]
  ring

/-- A marginal parallel to a chosen normal is annihilated by any vector
transverse to that normal; zero coefficients explicitly cover zero marginals. -/
theorem transverse_parallel (n u : Vec3) (α : ℝ) (h : dot3 n u = 0) :
    dot3 u (fun i => α * n i) = 0 := by
  have hid : dot3 u (fun i => α * n i) = α * dot3 n u := by
    unfold dot3
    ring
  rw [hid, h, mul_zero]

/-- The complete canonical geometric bound in EC2 Eqs. (17)--(19), for
every fixed marginal-axis choice.  No unit or nonvanishing assumption on
the normals is needed. -/
theorem fixed_axes_canonical_lower (c N : ℝ) (hc : 0 < c) (hN : c ≤ N)
    (n m : Vec3) (α β : ℝ) :
    ∃ u v : Vec3,
      sqLength u = 1 ∧ sqLength v = 1 ∧
      dot3 n u = 0 ∧ dot3 m v = 0 ∧
      c ≤ dot3 u (correctedAction c N (fun i => α * n i) (fun i => β * m i) v) := by
  obtain ⟨u, v, hu, hv, hun, hvm, huv⟩ := fixed_axes_diagonal_lower c N hc hN n m
  refine ⟨u, v, hu, hv, hun, hvm, ?_⟩
  rw [corrections_vanish]
  · exact huv
  · exact transverse_parallel n u α hun
  · rw [dot3_comm]
    exact transverse_parallel m v β hvm

/-- The unnormalized canonical concurrence does not exceed the trace. -/
theorem canonical_concurrence_le_trace (L u v s t r : ℝ) :
    2 * L * t ≤ L ^ 2 + u ^ 2 + v ^ 2 + s ^ 2 + t ^ 2 + r ^ 2 := by
  nlinarith [sq_nonneg (L - t), sq_nonneg u, sq_nonneg v, sq_nonneg s, sq_nonneg r]

theorem exists_unit_perpendicular (n : Vec3) :
    ∃ u : Vec3, sqLength u = 1 ∧ dot3 n u = 0 := by
  obtain ⟨w, hn, _, hw⟩ := common_perpendicular n 0
  exact ⟨normalize w, normalize_unit hw, normalize_perp hn⟩

/-- The absolute correlation bound includes the zero-concurrence case.
The two axes remain arbitrary fixed vectors even when α or β is zero. -/
theorem fixed_axes_canonical_abs_lower (c N : ℝ) (hc : 0 ≤ c) (hN : c ≤ N)
    (n m : Vec3) (α β : ℝ) :
    ∃ u v : Vec3,
      sqLength u = 1 ∧ sqLength v = 1 ∧
      dot3 n u = 0 ∧ dot3 m v = 0 ∧
      c ≤ |dot3 u (correctedAction c N (fun i => α * n i) (fun i => β * m i) v)| := by
  by_cases hcp : 0 < c
  · obtain ⟨u, v, hu, hv, hn, hm, h⟩ := fixed_axes_canonical_lower c N hcp hN n m α β
    exact ⟨u, v, hu, hv, hn, hm, h.trans (le_abs_self _)⟩
  have hc0 : c = 0 := by linarith
  obtain ⟨u, hu, hn⟩ := exists_unit_perpendicular n
  obtain ⟨v, hv, hm⟩ := exists_unit_perpendicular m
  refine ⟨u, v, hu, hv, hn, hm, ?_⟩
  rw [hc0]
  exact abs_nonneg _

/-- The real phase gauge in Eq. (20) has transverse block
diag(2(w+z), 2(z-w)). -/
def transverseGauge (w z : ℝ) (u v : Fin 2 → ℝ) : ℝ :=
  2 * (w + z) * u 0 * v 0 + 2 * (z - w) * u 1 * v 1

/-- Upper bound for every pair of unit transverse vectors in the real
nonnegative anti-diagonal gauge, including either or both zero coherences. -/
theorem transverse_gauge_bound (w z : ℝ) (hw : 0 ≤ w) (hz : 0 ≤ z)
    (u v : Fin 2 → ℝ)
    (hu : (u 0) ^ 2 + (u 1) ^ 2 = 1)
    (hv : (v 0) ^ 2 + (v 1) ^ 2 = 1) :
    |transverseGauge w z u v| ≤ 2 * (w + z) := by
  let a := 2 * (w + z) * v 0
  let b := 2 * (z - w) * v 1
  have hgap : 0 ≤ (4 * (w + z) ^ 2 - 4 * (z - w) ^ 2) * (v 1) ^ 2 := by
    apply mul_nonneg
    · nlinarith [mul_nonneg hw hz]
    · exact sq_nonneg _
  have hab : a ^ 2 + b ^ 2 ≤ (2 * (w + z)) ^ 2 := by
    have hvscaled := congrArg (fun t : ℝ => (2 * (w + z)) ^ 2 * t) hv
    dsimp [a, b]
    nlinarith only [hgap, hvscaled]
  have hcauchy : (u 0 * a + u 1 * b) ^ 2 ≤ a ^ 2 + b ^ 2 := by
    have huscaled := congrArg (fun t : ℝ => t * (a ^ 2 + b ^ 2)) hu
    nlinarith only [huscaled, sq_nonneg (u 0 * b - u 1 * a)]
  have hsq : (transverseGauge w z u v) ^ 2 ≤ (2 * (w + z)) ^ 2 := by
    have heq : transverseGauge w z u v = u 0 * a + u 1 * b := by
      dsimp [transverseGauge, a, b]
      ring
    rw [heq]
    exact hcauchy.trans hab
  have hnonneg : 0 ≤ 2 * (w + z) := by linarith
  have habs : |transverseGauge w z u v| ^ 2 = (transverseGauge w z u v) ^ 2 := sq_abs _
  nlinarith [abs_nonneg (transverseGauge w z u v)]

/-- The Eq. (20) upper bound is attained by the first transverse axes. -/
theorem transverse_gauge_attains (w z : ℝ) (hw : 0 ≤ w) (hz : 0 ≤ z) :
    |transverseGauge w z ![1, 0] ![1, 0]| = 2 * (w + z) := by
  simp [transverseGauge, abs_of_nonneg (show 0 ≤ w + z by linarith)]

theorem coord_sq_le_sqLength (u : Vec3) (i : Fin 3) : (u i) ^ 2 ≤ sqLength u := by
  fin_cases i
  · change (u 0) ^ 2 ≤ sqLength u
    unfold sqLength dot3
    nlinarith [sq_nonneg (u 1), sq_nonneg (u 2)]
  · change (u 1) ^ 2 ≤ sqLength u
    unfold sqLength dot3
    nlinarith [sq_nonneg (u 0), sq_nonneg (u 2)]
  · change (u 2) ^ 2 ≤ sqLength u
    unfold sqLength dot3
    nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]

theorem unit_coord_abs_le (u : Vec3) (hu : sqLength u = 1) (i : Fin 3) : |u i| ≤ 1 := by
  have hs := coord_sq_le_sqLength u i
  rw [hu] at hs
  nlinarith [sq_abs (u i), abs_nonneg (u i)]

/-- A concrete finite bound for every Euclidean-unit matrix correlation.
This ensures that the real supremum used for fixed-axis correlations is
a bounded supremum. -/
theorem unit_correlation_bounded (T : Matrix (Fin 3) (Fin 3) ℝ)
    (u v : Vec3) (hu : sqLength u = 1) (hv : sqLength v = 1) :
    |dot3 u (T.mulVec v)| ≤ ∑ i, ∑ j, |T i j| := by
  rw [dot3_eq_dotProduct]
  change |∑ i, u i * (∑ j, T i j * v j)| ≤ ∑ i, ∑ j, |T i j|
  simp_rw [Finset.mul_sum]
  calc
    |∑ i, ∑ j, u i * (T i j * v j)| ≤
        ∑ i, |∑ j, u i * (T i j * v j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |u i * (T i j * v j)| := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |T i j| := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_mul, ← mul_assoc]
      have hleft : |u i| * |T i j| ≤ |T i j| := by
        simpa using mul_le_mul_of_nonneg_right (unit_coord_abs_le u hu i) (abs_nonneg (T i j))
      calc
        |u i| * |T i j| * |v j| ≤ |T i j| * |v j| :=
          mul_le_mul_of_nonneg_right hleft (abs_nonneg (v j))
        _ ≤ |T i j| := by
          simpa using mul_le_mul_of_nonneg_left (unit_coord_abs_le v hv j) (abs_nonneg (T i j))

end
end ConcurrenceGeometry
end EC2
