import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Tensor iteration and the regularization limit

These are exact algebraic and limit consequences, explicitly conditional on the
additivity step or the tensor-power formula. They do not define an operational
LOCC model or substitute for the EC2 pure-state theorem.
-/

noncomputable section

open Filter Topology

namespace EC2.Consequences

/-- Peeling one copy at a time determines every finite tensor-power cost. -/
theorem finite_tensor_cost (F : ℕ → ℝ) (c : ℝ)
    (hone : F 1 = c) (hstep : ∀ n, 1 ≤ n → F (n + 1) = c + F n) :
    ∀ n, 1 ≤ n → F n = (n : ℝ) * c := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simpa using hone
  | succ n hn ih =>
    rw [hstep n hn, ih]
    push_cast
    ring

/-- Exact additivity makes the regularized sequence eventually constant. -/
theorem tensor_cost_div_eq (F : ℕ → ℝ) (c : ℝ)
    (hpower : ∀ n, 1 ≤ n → F n = (n : ℝ) * c) :
    ∀ n, 1 ≤ n → F n / (n : ℝ) = c := by
  intro n hn
  rw [hpower n hn]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  exact mul_div_cancel_left₀ c hn0

/-- No exchange of a dimension limit with an ensemble infimum is needed. -/
theorem regularized_tensor_cost (F : ℕ → ℝ) (c : ℝ)
    (hpower : ∀ n, 1 ≤ n → F n = (n : ℝ) * c) :
    Tendsto (fun n : ℕ => F n / (n : ℝ)) atTop (𝓝 c) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (tensor_cost_div_eq F c hpower n hn).symm

/-- A separately established operational regularization identity gives the same cost. -/
theorem operational_cost_of_regularization (F : ℕ → ℝ) (c operationalCost : ℝ)
    (hpower : ∀ n, 1 ≤ n → F n = (n : ℝ) * c)
    (hregularization : Tendsto (fun n : ℕ => F n / (n : ℝ)) atTop (𝓝 operationalCost)) :
    operationalCost = c :=
  tendsto_nhds_unique hregularization (regularized_tensor_cost F c hpower)

end EC2.Consequences
