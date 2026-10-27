module

public import HarmonicMaps.Sobolev
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# A fixed smooth normalized kernel

The kernel uses the explicit smooth transition evaluated at `1 - 4 * ‖x‖ ^ 2`.
Its support lies in the closed ball of radius one half, strictly inside the
open unit ball. The normalizing Lebesgue integral is finite and strictly positive.
This supplies the fixed kernel for the uniform smoothing estimates.
-/

@[expose] public section

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace HarmonicMaps

noncomputable section

/-- An explicit nonnegative smooth function supported in the half-unit ball. -/
def rawMollifierKernel (n : ℕ) (x : Domain n) : ℝ :=
  Real.smoothTransition (1 - 4 * ‖x‖ ^ 2)

theorem rawMollifierKernel_contDiff (n : ℕ) :
    ContDiff ℝ ∞ (rawMollifierKernel n) := by
  exact Real.smoothTransition.contDiff.comp
    (contDiff_const.sub (contDiff_const.mul (contDiff_norm_sq ℝ)))

theorem rawMollifierKernel_nonneg (n : ℕ) (x : Domain n) :
    0 ≤ rawMollifierKernel n x :=
  Real.smoothTransition.nonneg _

@[simp] theorem rawMollifierKernel_zero (n : ℕ) :
    rawMollifierKernel n 0 = 1 := by
  simp only [rawMollifierKernel, norm_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, sub_zero, Real.smoothTransition.one]

theorem rawMollifierKernel_support (n : ℕ) :
    Function.support (rawMollifierKernel n) =
      Metric.ball (0 : Domain n) (1 / 2) := by
  ext x
  rw [Function.mem_support, rawMollifierKernel]
  simp only [Ne, Real.smoothTransition.zero_iff_nonpos, Metric.mem_ball, dist_zero_right]
  have hnorm := norm_nonneg x
  constructor
  · intro hx
    have hpos : 0 < 1 - 4 * ‖x‖ ^ 2 := lt_of_not_ge hx
    nlinarith only [hpos, hnorm, sq_nonneg (‖x‖ - 1 / 2)]
  · intro hx hzero
    nlinarith only [hx, hzero, hnorm, sq_nonneg (‖x‖ - 1 / 2)]

theorem rawMollifierKernel_tsupport_subset (n : ℕ) :
    tsupport (rawMollifierKernel n) ⊆
      Metric.closedBall (0 : Domain n) (1 / 2) := by
  rw [tsupport, rawMollifierKernel_support]
  exact closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall

theorem rawMollifierKernel_hasCompactSupport (n : ℕ) :
    HasCompactSupport (rawMollifierKernel n) :=
  (isCompact_closedBall (0 : Domain n) (1 / 2)).of_isClosed_subset
    (isClosed_tsupport _) (rawMollifierKernel_tsupport_subset n)

theorem rawMollifierKernel_integrable (n : ℕ) :
    Integrable (rawMollifierKernel n) volume :=
  (rawMollifierKernel_contDiff n).continuous.integrable_of_hasCompactSupport
    (rawMollifierKernel_hasCompactSupport n)

/-- The extended nonnegative integral of the raw kernel is finite. -/
theorem rawMollifierKernel_lintegral_lt_top (n : ℕ) :
    (∫⁻ x, ENNReal.ofReal (rawMollifierKernel n x)) < ⊤ :=
  (rawMollifierKernel_integrable n).lintegral_lt_top

/-- The genuine normalizing integral is strictly positive. -/
theorem rawMollifierKernel_integral_pos (n : ℕ) :
    0 < ∫ x, rawMollifierKernel n x := by
  apply Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (x := (0 : Domain n)) (rawMollifierKernel_contDiff n).continuous
    (rawMollifierKernel_hasCompactSupport n) (rawMollifierKernel_nonneg n)
  rw [rawMollifierKernel_zero]
  exact one_ne_zero

/-- The fixed kernel normalized by its actual finite positive Lebesgue integral. -/
def fixedMollifierKernel (n : ℕ) (x : Domain n) : ℝ :=
  rawMollifierKernel n x / ∫ y, rawMollifierKernel n y

theorem fixedMollifierKernel_contDiff (n : ℕ) :
    ContDiff ℝ ∞ (fixedMollifierKernel n) :=
  (rawMollifierKernel_contDiff n).div_const _

theorem fixedMollifierKernel_nonneg (n : ℕ) (x : Domain n) :
    0 ≤ fixedMollifierKernel n x :=
  div_nonneg (rawMollifierKernel_nonneg n x) (rawMollifierKernel_integral_pos n).le

theorem fixedMollifierKernel_tsupport_subset_halfBall (n : ℕ) :
    tsupport (fixedMollifierKernel n) ⊆
      Metric.closedBall (0 : Domain n) (1 / 2) := by
  change tsupport ((fun t : ℝ => t / ∫ y, rawMollifierKernel n y) ∘
    rawMollifierKernel n) ⊆ _
  exact (tsupport_comp_subset
    (g := fun t : ℝ => t / ∫ y, rawMollifierKernel n y)
    (zero_div _) (rawMollifierKernel n)).trans
    (rawMollifierKernel_tsupport_subset n)

theorem fixedMollifierKernel_hasCompactSupport (n : ℕ) :
    HasCompactSupport (fixedMollifierKernel n) :=
  (isCompact_closedBall (0 : Domain n) (1 / 2)).of_isClosed_subset
    (isClosed_tsupport _) (fixedMollifierKernel_tsupport_subset_halfBall n)

theorem fixedMollifierKernel_tsupport_subset_unitBall (n : ℕ) :
    tsupport (fixedMollifierKernel n) ⊆ Metric.ball (0 : Domain n) 1 :=
  (fixedMollifierKernel_tsupport_subset_halfBall n).trans
    (Metric.closedBall_subset_ball (by norm_num : (1 / 2 : ℝ) < 1))

theorem fixedMollifierKernel_integrable (n : ℕ) :
    Integrable (fixedMollifierKernel n) volume :=
  (rawMollifierKernel_integrable n).div_const _

theorem fixedMollifierKernel_integral (n : ℕ) :
    (∫ x, fixedMollifierKernel n x) = 1 := by
  change (∫ x, rawMollifierKernel n x / ∫ y, rawMollifierKernel n y) = 1
  rw [integral_div]
  exact div_self (rawMollifierKernel_integral_pos n).ne'

/-- The explicit fixed kernel has the complete smoothing-kernel properties. -/
theorem fixedMollifierKernel_properties (n : ℕ) :
    ContDiff ℝ ∞ (fixedMollifierKernel n) ∧
    (∀ x, 0 ≤ fixedMollifierKernel n x) ∧
    HasCompactSupport (fixedMollifierKernel n) ∧
    tsupport (fixedMollifierKernel n) ⊆ Metric.ball (0 : Domain n) 1 ∧
    (∫ x, fixedMollifierKernel n x) = 1 :=
  ⟨fixedMollifierKernel_contDiff n, fixedMollifierKernel_nonneg n,
    fixedMollifierKernel_hasCompactSupport n,
    fixedMollifierKernel_tsupport_subset_unitBall n, fixedMollifierKernel_integral n⟩

end
end HarmonicMaps

end
