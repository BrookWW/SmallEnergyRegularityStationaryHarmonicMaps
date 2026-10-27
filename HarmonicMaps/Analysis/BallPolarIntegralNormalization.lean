module

public import HarmonicMaps.Analysis.BallPolarIntegral

/-!
# Normalization and null boundaries for polar ball integration

The canonical angular measure has mass n times the volume of the unit ball.
The polar boundary weight is r^(n-1). No Hausdorff-measure identification or
new surface measure definition is asserted here.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace HarmonicMaps

/-- Euclidean sphere boundaries are null in every positive dimension. -/
theorem volume_sphere_eq_zero {n : ℕ} (hn : 0 < n) (a : Domain n) (r : ℝ) :
    volume (Metric.sphere a r) = 0 := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact (volume : Measure (Domain n)).addHaar_sphere a r

/-- The center of a positive-dimensional Euclidean ball is null. -/
theorem volume_center_eq_zero {n : ℕ} (hn : 0 < n) (a : Domain n) :
    volume ({a} : Set (Domain n)) = 0 := by
  simpa only [Metric.sphere_zero] using volume_sphere_eq_zero hn a 0

/-- The exact mass normalization of the canonical angular measure. -/
theorem polar_angular_measure_univ {n : ℕ} :
    (volume : Measure (Domain n)).toSphere Set.univ =
      (n : ℝ≥0∞) * volume (Metric.ball (0 : Domain n) 1) := by
  simpa only [finrank_euclideanSpace, Fintype.card_fin] using
    (volume : Measure (Domain n)).toSphere_apply_univ

/-- At each nonnegative radius, the constant-density polar boundary integral
has the expected n times unit-ball-volume coefficient and radius power. -/
theorem polar_boundary_density_one {n : ℕ} (r : ℝ) (_hr : 0 ≤ r) :
    r ^ (n - 1) * (∫ _θ : Metric.sphere (0 : Domain n) 1, (1 : ℝ)
      ∂(volume : Measure (Domain n)).toSphere) =
      (n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * r ^ (n - 1) := by
  rw [integral_const, smul_eq_mul, mul_one,
    (volume : Measure (Domain n)).toSphere_real_apply_univ]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  ring

end HarmonicMaps
