module

public import HarmonicMaps.Energy
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# The source exponent and geometric radius brackets

The literal logarithmic exponent of a positive contraction radius satisfies
the exact half-power identity. Successive geometric radii bracket every
positive inner radius, including the outer endpoint, with coefficient two.
-/

public section

namespace HarmonicMaps

/-- The fixed source radius produces its literal exponent and the exact
dyadic comparison at every positive pair of radii. -/
theorem iteration_scale_properties (tau : PositiveRadius) (hTau : tau.val < 1 / 8) :
    let alpha := Real.log 2 / (2 * Real.log (1 / tau.val))
    0 < alpha ∧ alpha < 1 ∧ tau.val ^ (2 * alpha) = 1 / 2 ∧
    ∀ (r s : PositiveRadius), r.val ≤ s.val →
      ∃ k : ℕ, tau.val ^ (k + 1) * s.val < r.val ∧
        r.val ≤ tau.val ^ k * s.val ∧
        (1 / 2 : ℝ) ^ k ≤ 2 * (r.val / s.val) ^ (2 * alpha) := by
  let alpha : ℝ := Real.log 2 / (2 * Real.log (1 / tau.val))
  have htOne : tau.val < 1 := hTau.trans (by norm_num)
  have hInv : (2 : ℝ) < 1 / tau.val := by
    apply (lt_div_iff₀ tau.property).mpr
    linarith only [hTau]
  have hLogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLog : Real.log 2 < Real.log (1 / tau.val) := Real.log_lt_log (by norm_num) hInv
  have hLogPos : 0 < Real.log (1 / tau.val) := hLogTwo.trans hLog
  have hAlpha : 0 < alpha := div_pos hLogTwo (mul_pos (by norm_num) hLogPos)
  have hAlphaOne : alpha < 1 := by
    apply (div_lt_iff₀ (mul_pos (by norm_num) hLogPos)).mpr
    linarith only [hLog, hLogPos]
  have hLogInv : Real.log (1 / tau.val) = -Real.log tau.val := by
    rw [one_div, Real.log_inv]
  have hExponent : Real.log tau.val * (2 * alpha) = -Real.log 2 := by
    dsimp only [alpha]
    rw [← neg_eq_iff_eq_neg.mpr hLogInv]
    field_simp [hLogPos.ne']
  have hPower : tau.val ^ (2 * alpha) = (1 / 2 : ℝ) := by
    rw [Real.rpow_def_of_pos tau.property, hExponent, Real.exp_neg,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  refine ⟨hAlpha, hAlphaOne, hPower, ?_⟩
  intro r s hrs
  have hRatio : 0 < r.val / s.val := div_pos r.property s.property
  have hRatioOne : r.val / s.val ≤ 1 := (div_le_one s.property).mpr hrs
  obtain ⟨k, hLower, hUpper⟩ := exists_nat_pow_near_of_lt_one hRatio hRatioOne tau.property htOne
  have hLowerRadius : tau.val ^ (k + 1) * s.val < r.val :=
    (lt_div_iff₀ s.property).mp hLower
  have hUpperRadius : r.val ≤ tau.val ^ k * s.val :=
    (div_le_iff₀ s.property).mp hUpper
  have hDyadic : (1 / 2 : ℝ) ^ k = 2 * (tau.val ^ (k + 1)) ^ (2 * alpha) := by
    rw [← Real.rpow_pow_comm tau.property.le, hPower, pow_succ]
    ring
  refine ⟨k, hLowerRadius, hUpperRadius, ?_⟩
  rw [hDyadic]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (pow_pos tau.property _).le hLower.le (by linarith only [hAlpha]))
    (by norm_num)

end HarmonicMaps
end
