import EC2.EntropyScalar
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# The one-sided Hanner differentiation step

This file proves the analytic step at the balanced point, where the two
Schatten norms coincide. In particular it does not silently assume that
their difference is nonzero.
-/

noncomputable section

open scoped Topology
open Filter Set

namespace EC2.Entropy

/-- If `f(2)=0`, the potentially troublesome term `|f(q)|^q` has zero
right derivative at two. The proof compares it with `f(q)^2`. -/
theorem hasDerivWithinAt_abs_rpow_self_zero {f : ℝ → ℝ} {f' : ℝ}
    (hf : HasDerivAt f f' 2) (hf0 : f 2 = 0) :
    HasDerivWithinAt (fun q : ℝ => |f q| ^ q) 0 (Ioi 2) 2 := by
  have hsquare : HasDerivWithinAt (fun q => (f q) ^ 2) 0 (Ioi 2) 2 := by
    simpa [hf0] using (hf.fun_pow 2).hasDerivWithinAt (s := Ioi 2)
  have hlim := (hasDerivWithinAt_iff_tendsto_slope'
    (notMem_Ioi.mpr (le_refl (2 : ℝ)))).mp hsquare
  have hsmall : ∀ᶠ q in 𝓝 (2 : ℝ), |f q| < 1 :=
    hf.continuousAt.abs.eventually (gt_mem_nhds (by simp [hf0]))
  apply (hasDerivWithinAt_iff_tendsto_slope'
    (notMem_Ioi.mpr (le_refl (2 : ℝ)))).mpr
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [self_mem_nhdsWithin] with q hq
    simp only [slope_def_field, hf0, abs_zero, Real.zero_rpow (by norm_num : (2 : ℝ) ≠ 0),
      sub_zero]
    exact div_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (sub_pos.mpr hq).le
  · filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds] with q hq hs
    simp only [slope_def_field, hf0, abs_zero, Real.zero_rpow (by norm_num : (2 : ℝ) ≠ 0),
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero]
    apply div_le_div_of_nonneg_right _ (sub_pos.mpr hq).le
    simpa [Real.rpow_two, sq_abs] using
      Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg (f q)) hs.le
        (by norm_num : (0 : ℝ) ≤ 2) hq.le

/-- Uniform derivative formula for `|f(q)|^q` at `q=2`, including `f(2)=0`. -/
theorem hasDerivWithinAt_abs_rpow_self {f : ℝ → ℝ} {f' : ℝ}
    (hf : HasDerivAt f f' 2) :
    HasDerivWithinAt (fun q : ℝ => |f q| ^ q)
      (2 * f 2 * f' + (f 2) ^ 2 * Real.log |f 2|) (Ioi 2) 2 := by
  rcases lt_trichotomy (f 2) 0 with hneg | hzero | hpos
  · have habs := (hasDerivAt_abs_neg hneg).comp 2 hf
    have hp := habs.rpow (hasDerivAt_id (2 : ℝ)) (abs_pos.mpr hneg.ne)
    convert hp.hasDerivWithinAt (s := Ioi 2) using 1 <;>
      norm_num [Function.comp_def, id_eq, abs_of_neg hneg, Real.rpow_two] <;> ring
  · simpa [hzero] using hasDerivWithinAt_abs_rpow_self_zero hf hzero
  · have habs := (hasDerivAt_abs_pos hpos).comp 2 hf
    have hp := habs.rpow (hasDerivAt_id (2 : ℝ)) (abs_pos.mpr hpos.ne')
    convert hp.hasDerivWithinAt (s := Ioi 2) using 1 <;>
      norm_num [Function.comp_def, id_eq, abs_of_pos hpos, Real.rpow_two] <;> ring

/-- Differentiation of the Hanner right side. -/
theorem hasDerivWithinAt_hanner_rhs {r s : ℝ → ℝ} {r' s' : ℝ}
    (hr : HasDerivAt r r' 2) (hs : HasDerivAt s s' 2)
    (hpos : 0 < r 2 + s 2) :
    HasDerivWithinAt (fun q : ℝ => (r q + s q) ^ q + |r q - s q| ^ q)
      ((r 2 + s 2) ^ 2 * Real.log (r 2 + s 2) +
       (r 2 - s 2) ^ 2 * Real.log |r 2 - s 2| +
       4 * r 2 * r' + 4 * s 2 * s') (Ioi 2) 2 := by
  have hsum := ((hr.add hs).rpow (hasDerivAt_id (2 : ℝ)) hpos).hasDerivWithinAt
    (s := Ioi 2)
  have hdiff := hasDerivWithinAt_abs_rpow_self (hr.sub hs)
  convert hsum.fun_add hdiff using 1 <;>
    norm_num [Pi.add_apply, Pi.sub_apply, id_eq, Real.rpow_two] <;> ring

/-- The entropy form of the Hanner derivative, manuscript Eq. (9).
The derivative hypotheses specify arbitrary functions, not an assumed EC2
entropy inequality. -/
theorem hasDerivWithinAt_hanner_entropy_rhs {r s : ℝ → ℝ}
    {x y SX SY : ℝ}
    (hr : HasDerivAt r (-r 2 * SX / 4) 2)
    (hs : HasDerivAt s (-s 2 * SY / 4) 2)
    (hr0 : 0 ≤ r 2) (hs0 : 0 ≤ s 2)
    (hrx : (r 2) ^ 2 = x) (hsy : (s 2) ^ 2 = y) (hxy : x + y = 1) :
    HasDerivWithinAt (fun q : ℝ => (r q + s q) ^ q + |r q - s q| ^ q)
      (Real.log 2 - wNats |x - y| - x * SX - y * SY) (Ioi 2) 2 := by
  have hn : (r 2) ^ 2 + (s 2) ^ 2 = 1 := by rw [hrx, hsy, hxy]
  have hpos : 0 < r 2 + s 2 := by nlinarith
  have hd := hasDerivWithinAt_hanner_rhs hr hs hpos
  convert hd using 1
  rw [hanner_logarithmic_identity _ _ hr0 hs0 hn, hrx, hsy]
  linear_combination SX * hrx + SY * hsy

end EC2.Entropy
