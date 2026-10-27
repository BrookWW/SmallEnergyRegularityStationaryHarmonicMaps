module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Differentiation of integrals with dominated difference quotients

Integrable parameter slices and a dominated slope at zero suffice to
interchange a two-sided derivative and the integral.
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace HarmonicMaps

/-- A direct dominated-convergence criterion for the derivative of an
integral at zero. The domination is on the actual difference quotient. -/
theorem hasDerivAt_integral_of_dominated_slopes {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {F : ℝ → α → ℝ} {D b : α → ℝ}
    (h0 : Integrable (F 0) μ)
    (hF : ∀ᶠ t in 𝓝[≠] (0 : ℝ), Integrable (F t) μ)
    (hb : Integrable b μ)
    (hbound : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ᵐ x ∂μ,
      ‖t⁻¹ * (F t x - F 0 x)‖ ≤ b x)
    (hD : ∀ᵐ x ∂μ, HasDerivAt (fun t => F t x) (D x) 0) :
    HasDerivAt (fun t => ∫ x, F t x ∂μ) (∫ x, D x ∂μ) 0 := by
  have hm : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      AEStronglyMeasurable (fun x => t⁻¹ * (F t x - F 0 x)) μ := by
    filter_upwards [hF] with t ht
    exact (ht.aestronglyMeasurable.sub h0.aestronglyMeasurable).const_mul t⁻¹
  have hl : ∀ᵐ x ∂μ, Tendsto (fun t : ℝ => t⁻¹ * (F t x - F 0 x))
      (𝓝[≠] 0) (𝓝 (D x)) := by
    filter_upwards [hD] with x hx
    simpa only [zero_add, smul_eq_mul] using hx.tendsto_slope_zero
  have hi := tendsto_integral_filter_of_dominated_convergence b hm hbound hb hl
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  apply hi.congr'
  filter_upwards [hF] with t ht
  rw [integral_const_mul, integral_sub ht h0]
  simp only [zero_add, smul_eq_mul]

end HarmonicMaps
