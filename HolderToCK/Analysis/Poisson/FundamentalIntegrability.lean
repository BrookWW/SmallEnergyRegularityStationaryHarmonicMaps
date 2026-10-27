module

public import HolderToCK.Analysis.Poisson.KernelBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-! # Compact test products of the fundamental solution and radial gradient -/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology

namespace HolderToCK

theorem fundamentalPower_testIntegrable {n : ℕ} (hn : 3 ≤ n)
    {ψ : Domain n → ℝ} (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) :
    Integrable (fun x => fundamentalPowerExpression x * ψ x) volume := by
  simpa only [smul_eq_mul] using
    (fundamentalPower_locallyIntegrable hn).integrable_smul_right_of_hasCompactSupport hψ hcψ

theorem fundamentalLog_testIntegrable {ψ : Domain 2 → ℝ}
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) :
    Integrable (fun x => fundamentalLogExpression x * ψ x) volume := by
  simpa only [smul_eq_mul] using
    fundamentalLog_locallyIntegrable.integrable_smul_right_of_hasCompactSupport hψ hcψ

theorem normalizedRadialColumn_locallyIntegrable {n : ℕ} (hn : 0 < n) (i : Fin n) :
    LocallyIntegrable (fun x : Domain n =>
      (euclideanSphereArea n)⁻¹ * ‖x‖ ^ (-(n : ℝ)) * x i) volume := by
  have hi : LocallyIntegrable (fun x : Domain n =>
      fundamentalGradientExpression x (EuclideanSpace.single i 1)) volume := by
    intro x
    exact (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1)).integrableAtFilter_comp
      (fundamentalGradientExpression_locallyIntegrable hn x)
  simpa only [fundamentalGradientExpression, smul_apply, innerSL_apply_apply,
    EuclideanSpace.inner_single_right, one_mul, conj_trivial, smul_eq_mul] using hi

theorem normalizedRadialColumn_testIntegrable {n : ℕ} (hn : 0 < n) (i : Fin n)
    {ψ : Domain n → ℝ} (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) :
    Integrable (fun x : Domain n =>
      ((euclideanSphereArea n)⁻¹ * ‖x‖ ^ (-(n : ℝ)) * x i) * ψ x) volume := by
  simpa only [smul_eq_mul] using
    (normalizedRadialColumn_locallyIntegrable hn i).integrable_smul_right_of_hasCompactSupport
      hψ hcψ

end HolderToCK
end
