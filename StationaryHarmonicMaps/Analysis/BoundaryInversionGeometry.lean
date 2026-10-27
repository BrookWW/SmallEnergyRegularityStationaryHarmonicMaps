module

public import StationaryHarmonicMaps.Geometry.UnitInversion

/-!
# Actual inversion geometry about a unit-sphere query center

The genuine inversion-distance identity fixes the unit-sphere center.
Exterior points therefore move closer to that same center. An exterior
boundary-query ball maps into the same query ball inside the original
unit ball. This is a set identity estimate, not a boundary PDE assumption.
-/

public section

open HarmonicMaps EuclideanGeometry Set
open StationaryHarmonicMaps.Geometry

namespace StationaryHarmonicMaps.Analysis

/-- The genuine inversion distance from an actual unit-sphere center is divided by the original radius. -/
theorem dist_unit_inversion_sphere_center {n : ℕ}
    (a x : Domain n) (ha : ‖a‖=1) (hx : x≠0) :
    dist (inversion (0 : Domain n) 1 x) a=‖x‖⁻¹*dist x a := by
  have ha0 : a≠0 := norm_ne_zero_iff.mp (by rw [ha];norm_num)
  have hIa : inversion (0 : Domain n) 1 a=a :=
    inversion_of_mem_sphere (by simpa only [Metric.mem_sphere,dist_zero_right] using ha)
  have H := dist_inversion_inversion hx ha0 (1 : ℝ)
  simpa only [hIa,one_pow,dist_zero_right,ha,mul_one,one_div] using H

/-- Actual exterior points do not increase their distance from any original unit-sphere center under inversion. -/
theorem dist_unit_inversion_sphere_center_le {n : ℕ}
    (a x : Domain n) (ha : ‖a‖=1) (hx : 1≤‖x‖) :
    dist (inversion (0 : Domain n) 1 x) a≤dist x a := by
  have hxPos : 0<‖x‖ := zero_lt_one.trans_le hx
  rw [dist_unit_inversion_sphere_center a x ha (norm_pos_iff.mp hxPos)]
  exact (mul_le_mul_of_nonneg_right ((inv_le_one₀ hxPos).mpr hx) dist_nonneg).trans_eq (one_mul _)

/-- The actual exterior portion of a sphere-centered query ball maps into the same query ball inside the unit ball. -/
theorem unit_inversion_image_exterior_boundary_ball_subset {n : ℕ}
    (a : Domain n) (ha : ‖a‖=1) (r : ℝ) :
    inversion (0 : Domain n) 1 '' (Metric.ball a r∩{x : Domain n | 1<‖x‖})⊆
      Metric.ball a r∩Metric.ball (0 : Domain n) 1 := by
  rintro _ ⟨x,hx,rfl⟩
  refine ⟨lt_of_le_of_lt (dist_unit_inversion_sphere_center_le a x ha hx.2.le) hx.1,?_⟩
  rw [Metric.mem_ball,dist_zero_right,norm_unit_inversion]
  exact (inv_lt_one₀ (zero_lt_one.trans hx.2)).mpr hx.2

end StationaryHarmonicMaps.Analysis

end
