module

public import HarmonicMaps.Analysis.BallPolarIntegral

/-!
# Radially weighted polar integrals

Continuous radial weights preserve genuine ball L1 integrability and commute
with the canonical polar angular integral.
-/

public section

open MeasureTheory Set

namespace HarmonicMaps

/-- A continuous radial coefficient preserves integrability on a bounded ball. -/
theorem integrableOn_radial_mul {n : ℕ} {f : Domain n → ℝ} {a : Domain n} {R : ℝ}
    (hf : IntegrableOn f (Metric.ball a R) volume) {c : ℝ → ℝ} (hc : Continuous c) :
    IntegrableOn (fun x => c ‖x - a‖ * f x) (Metric.ball a R) volume :=
  IntegrableOn.continuousOn_mul_of_subset
    ((hc.comp (continuous_id.sub continuous_const).norm).continuousOn) hf
    (isCompact_closedBall a R) Metric.isOpen_ball.measurableSet Metric.ball_subset_closedBall

/-- The same continuous radial coefficient factors out of the angular integral. -/
theorem integral_radial_mul_eq_polar {n : ℕ} (hn : 0 < n)
    {f : Domain n → ℝ} {a : Domain n} {R : ℝ}
    (hf : IntegrableOn f (Metric.ball a R) volume) {c : ℝ → ℝ} (hc : Continuous c) :
    (∫ x in Metric.ball a R, c ‖x - a‖ * f x) =
      ∫ r in Ioo (0 : ℝ) R, c r * (r ^ (n - 1) *
        ∫ θ : Metric.sphere (0 : Domain n) 1, f (a + r • θ.val)
          ∂(volume : Measure (Domain n)).toSphere) := by
  rw [integral_ball_eq_polar hn (integrableOn_radial_mul hf hc)]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r hr
  dsimp only
  have hnorm (θ : Metric.sphere (0 : Domain n) 1) : ‖a + r • θ.val - a‖ = r := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.1.le]
    have hθ : ‖θ.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
    rw [hθ, mul_one]
  simp_rw [hnorm]
  rw [integral_const_mul]
  ring

end HarmonicMaps
