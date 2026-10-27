module

public import HarmonicMaps.Target
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Nearest points on the actual compact target

Compactness supplies an ambient distance minimizer without choosing a projection.
The minimum characterization and two-minimizer distance bound hold on the whole
Euclidean ambient space; neither asserts uniqueness.
-/

public section

namespace HarmonicMaps.CompactSmoothEmbeddedTarget

/-- Every ambient point has a distance minimizer on the actual target. -/
theorem exists_nearest_point {q : ℕ} (N : CompactSmoothEmbeddedTarget q)
    (z : EuclideanSpace ℝ (Fin q)) :
    ∃ p : N.Carrier, dist z p.val = Metric.infDist z N.carrierSet ∧
      ∀ r : N.Carrier, dist z p.val ≤ dist z r.val := by
  obtain ⟨p, hp, heq⟩ := N.isCompact.exists_infDist_eq_dist N.nonempty z
  refine ⟨⟨p, hp⟩, heq.symm, ?_⟩
  intro r
  rw [← heq]
  exact Metric.infDist_le_dist_of_mem r.property

/-- Being a global distance minimizer is exactly attaining the set distance. -/
theorem nearest_point_iff {q : ℕ} (N : CompactSmoothEmbeddedTarget q)
    (z : EuclideanSpace ℝ (Fin q)) (p : N.Carrier) :
    (∀ r : N.Carrier, dist z p.val ≤ dist z r.val) ↔
      dist z p.val = Metric.infDist z N.carrierSet := by
  constructor
  · intro hp
    apply le_antisymm
    · apply (Metric.le_infDist N.nonempty).2
      intro r hr
      exact hp ⟨r, hr⟩
    · exact Metric.infDist_le_dist_of_mem p.property
  · intro hp r
    rw [hp]
    exact Metric.infDist_le_dist_of_mem r.property

/-- Any two actual minimizers are at most twice the target distance apart. -/
theorem dist_nearest_points_le {q : ℕ} (N : CompactSmoothEmbeddedTarget q)
    (z : EuclideanSpace ℝ (Fin q)) (p r : N.Carrier)
    (hp : ∀ s : N.Carrier, dist z p.val ≤ dist z s.val)
    (hr : ∀ s : N.Carrier, dist z r.val ≤ dist z s.val) :
    dist p.val r.val ≤ 2 * Metric.infDist z N.carrierSet := by
  calc
    dist p.val r.val ≤ dist p.val z + dist z r.val := dist_triangle _ _ _
    _ = Metric.infDist z N.carrierSet + Metric.infDist z N.carrierSet := by
      rw [dist_comm p.val z, (N.nearest_point_iff z p).1 hp,
        (N.nearest_point_iff z r).1 hr]
    _ = 2 * Metric.infDist z N.carrierSet := (two_mul _).symm

end HarmonicMaps.CompactSmoothEmbeddedTarget

end
