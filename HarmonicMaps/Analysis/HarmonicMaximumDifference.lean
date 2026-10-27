module

public import HarmonicMaps.Analysis.PoissonBoundaryMaximum
public import Mathlib.Topology.Order.OrderClosed

/-!
# Difference between smoothing and harmonic replacement

Interior oscillation of smooth boundary data extends to the boundary sphere.
Poisson mass one then controls the same harmonic solution throughout the ball.
-/

public section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace HarmonicMaps

/-- An actual Poisson replacement differs from its datum by at most twice
the datum's oscillation around one fixed vector. -/
theorem poisson_harmonicDifference_le_of_oscillation {n q : ℕ} (hn : 2 ≤ n)
    (R : PositiveRadius) (U : Set (Domain n)) (hU : IsOpen U)
    (hclosed : Metric.closedBall (0 : Domain n) R.val ⊆ U)
    (m w : Domain n → Ambient q) (hm : ContDiffOn ℝ ∞ m U)
    (hformula : ∀ x ∈ Metric.ball (0 : Domain n) R.val,
      w x = ((R.val ^ 2 - ‖x‖ ^ 2) /
        ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) •
        (∫ y : Domain n, (‖x - y‖ ^ n)⁻¹ • m y
          ∂Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
            (ENNReal.ofReal (R.val ^ (n - 1)) •
              (volume : Measure (Domain n)).toSphere)))
    (c : Ambient q) (M : ℝ)
    (hbound : ∀ x ∈ Metric.ball (0 : Domain n) R.val, ‖m x - c‖ ≤ M)
    (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) R.val) :
    ‖m x - w x‖ ≤ 2 * M := by
  have hcont : ContinuousOn (fun z : Domain n => ‖m z - c‖)
      (closure (Metric.ball (0 : Domain n) R.val)) := by
    rw [closure_ball 0 R.property.ne']
    exact ((hm.continuousOn.mono hclosed).sub continuousOn_const).norm
  have hboundary (y : Domain n) (hy : y ∈ Metric.sphere (0 : Domain n) R.val) :
      ‖m y - c‖ ≤ M := by
    apply le_on_closure hbound hcont continuousOn_const
    rw [closure_ball 0 R.property.ne']
    exact Metric.sphere_subset_closedBall hy
  have hwbound : ‖w x - c‖ ≤ M := by
    rw [hformula x hx]
    exact poisson_scaledPolar_norm_sub_le_boundary hn R U hU hclosed m hm c M
      hboundary x hx
  calc
    ‖m x - w x‖ = ‖(m x - c) - (w x - c)‖ := by congr 1; abel
    _ ≤ ‖m x - c‖ + ‖w x - c‖ := norm_sub_le _ _
    _ ≤ M + M := add_le_add (hbound x hx) hwbound
    _ = 2 * M := by ring

end HarmonicMaps
end
