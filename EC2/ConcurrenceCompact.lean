import EC2.ConcurrenceGeometry
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FunProp

/-! # Attainment of the fixed-axis transverse correlation maximum -/

namespace EC2
namespace ConcurrenceCompact

noncomputable section
open ConcurrenceGeometry Set

abbrev E3 := EuclideanSpace ℝ (Fin 3)

def transverseUnits (n : Vec3) : Set E3 :=
  {u | ‖u‖ = 1 ∧ dot3 n (fun i => u i) = 0}

theorem continuous_dot_left (n : Vec3) :
    Continuous (fun u : E3 => dot3 n (fun i => u i)) := by
  unfold dot3
  fun_prop

theorem transverseUnits_compact (n : Vec3) : IsCompact (transverseUnits n) := by
  have hs : IsCompact (Metric.sphere (0 : E3) 1) := isCompact_sphere _ _
  have hc : IsClosed {u : E3 | dot3 n (fun i => u i) = 0} :=
    isClosed_eq (continuous_dot_left n) continuous_const
  have heq : transverseUnits n =
      Metric.sphere (0 : E3) 1 ∩ {u : E3 | dot3 n (fun i => u i) = 0} := by
    ext u
    simp [transverseUnits, Metric.mem_sphere, dist_zero_right]
  rw [heq]
  exact hs.inter_right hc

theorem transverseUnits_nonempty (n : Vec3) : (transverseUnits n).Nonempty := by
  obtain ⟨u, hu, hn⟩ := exists_unit_perpendicular n
  exact ⟨asEuclidean u, (sqLength_eq_one_iff_norm u).mp hu, hn⟩

def correlationValue (T : Matrix (Fin 3) (Fin 3) ℝ) (p : E3 × E3) : ℝ :=
  |dot3 (fun i => p.1 i) (T.mulVec (fun i => p.2 i))|

theorem correlationValue_continuous (T : Matrix (Fin 3) (Fin 3) ℝ) :
    Continuous (correlationValue T) := by
  unfold correlationValue dot3 Matrix.mulVec dotProduct
  fun_prop

/-- For every two prescribed axes and every real 3×3 correlation matrix,
the absolute transverse correlation has a maximizing pair of unit vectors.
The statement includes zero or coincident axis vectors. -/
theorem exists_maximal_unit_correlation (T : Matrix (Fin 3) (Fin 3) ℝ) (n m : Vec3) :
    ∃ u v : Vec3,
      sqLength u = 1 ∧ sqLength v = 1 ∧ dot3 n u = 0 ∧ dot3 m v = 0 ∧
      ∀ x y : Vec3, sqLength x = 1 → sqLength y = 1 →
        dot3 n x = 0 → dot3 m y = 0 →
        |dot3 x (T.mulVec y)| ≤ |dot3 u (T.mulVec v)| := by
  have hs : IsCompact (transverseUnits n ×ˢ transverseUnits m) :=
    (transverseUnits_compact n).prod (transverseUnits_compact m)
  have hn : (transverseUnits n ×ˢ transverseUnits m).Nonempty :=
    (transverseUnits_nonempty n).prod (transverseUnits_nonempty m)
  obtain ⟨p, hp, hmax⟩ := hs.exists_isMaxOn hn (correlationValue_continuous T).continuousOn
  let u : Vec3 := fun i => p.1 i
  let v : Vec3 := fun i => p.2 i
  have hue : asEuclidean u = p.1 := rfl
  have hve : asEuclidean v = p.2 := rfl
  have hu : sqLength u = 1 := (sqLength_eq_one_iff_norm u).mpr (by rw [hue]; exact hp.1.1)
  have hv : sqLength v = 1 := (sqLength_eq_one_iff_norm v).mpr (by rw [hve]; exact hp.2.1)
  refine ⟨u, v, hu, hv, hp.1.2, hp.2.2, ?_⟩
  intro x y hx hy hxn hym
  have hxy : (asEuclidean x, asEuclidean y) ∈ transverseUnits n ×ˢ transverseUnits m :=
    ⟨⟨(sqLength_eq_one_iff_norm x).mp hx, hxn⟩,
      ⟨(sqLength_eq_one_iff_norm y).mp hy, hym⟩⟩
  exact hmax hxy

end
end ConcurrenceCompact
end EC2
