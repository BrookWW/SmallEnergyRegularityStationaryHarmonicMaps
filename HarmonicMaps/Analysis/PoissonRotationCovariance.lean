module

public import HarmonicMaps.Analysis.PoissonMeasureInvariance

/-!
# Rotation covariance of the canonical Poisson integral

Orthogonal change of variables moves a source rotation onto the boundary
function, with the same canonical scaled-polar measure and coefficient.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace HarmonicMaps

/-- An orthogonal source rotation is exactly boundary-data pullback for the
literal canonical scaled-polar Poisson formula. -/
theorem poisson_scaledPolar_rotation_covariance {n q : ℕ}
    (R : PositiveRadius) (T : Domain n ≃ₗᵢ[ℝ] Domain n)
    (m : Domain n → Ambient q) (x : Domain n) :
    ((R.val ^ 2 - ‖T x‖ ^ 2) /
      ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) •
      (∫ y : Domain n, (‖T x - y‖ ^ n)⁻¹ • m y
        ∂Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
          (ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere)) =
    ((R.val ^ 2 - ‖x‖ ^ 2) /
      ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) •
      (∫ y : Domain n, (‖x - y‖ ^ n)⁻¹ • m (T y)
        ∂Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
          (ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere)) := by
  let μ : Measure (Domain n) :=
    Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
      (ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere)
  have hT : MeasurePreserving T μ μ :=
    ⟨T.continuous.measurable, poisson_scaledPolar_rotationInvariant R T⟩
  have hIntegral := hT.integral_comp T.toHomeomorph.measurableEmbedding
    (fun y : Domain n => (‖T x - y‖ ^ n)⁻¹ • m y)
  have hChange : (∫ y : Domain n, (‖T x - y‖ ^ n)⁻¹ • m y ∂μ) =
      ∫ y : Domain n, (‖x - y‖ ^ n)⁻¹ • m (T y) ∂μ := by
    calc
      _ = ∫ y : Domain n, (‖T x - T y‖ ^ n)⁻¹ • m (T y) ∂μ := hIntegral.symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with y
        rw [← T.map_sub, T.norm_map]
  rw [T.norm_map]
  exact congrArg (fun z =>
    ((R.val ^ 2 - ‖x‖ ^ 2) /
      ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) • z) hChange

end HarmonicMaps
end
