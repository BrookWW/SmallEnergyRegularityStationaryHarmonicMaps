module

public import HarmonicMaps.Geometry.TargetLocalNearestSmooth
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# A uniform radius for actual local nearest-point certificates

The union of all produced local certificate balls is an open neighborhood of
the actual compact target. A positive thickening lies inside that neighborhood.
Every point in the same uniform tube then has a smaller smooth nearest-point
certificate ball inside the tube, with uniqueness against all target points.
-/

public section

open Filter Topology Set
open scoped ContDiff

namespace HarmonicMaps.CompactSmoothEmbeddedTarget

/-- Compactness produces one positive radius for true local nearest certificates throughout a tube. -/
theorem exists_uniform_nearest_smooth_radius {q : ℕ} (N : CompactSmoothEmbeddedTarget q) :
    ∃ rho : ℝ, 0 < rho ∧
      ∀ z : EuclideanSpace ℝ (Fin q), Metric.infDist z N.carrierSet < 2 * rho →
        ∃ epsilon : ℝ, 0 < epsilon ∧
          Metric.ball z epsilon ⊆ {w | Metric.infDist w N.carrierSet < 2 * rho} ∧
          ∃ g : EuclideanSpace ℝ (Fin q) → EuclideanSpace ℝ (Fin q),
            ContDiffOn ℝ ∞ g (Metric.ball z epsilon) ∧
            ∀ w ∈ Metric.ball z epsilon,
              g w ∈ N.carrierSet ∧
              (∀ r : N.Carrier, dist w (g w) ≤ dist w r.val) ∧
              ∀ r : N.Carrier,
                (∀ s : N.Carrier, dist w r.val ≤ dist w s.val) → r.val = g w := by
  let O : Set (EuclideanSpace ℝ (Fin q)) :=
    {z | ∃ p : N.Carrier, ∃ delta : ℝ, 0 < delta ∧
      ∃ g : EuclideanSpace ℝ (Fin q) → EuclideanSpace ℝ (Fin q),
        ContDiffOn ℝ ∞ g (Metric.ball p.val delta) ∧
        (∀ w ∈ Metric.ball p.val delta,
          g w ∈ N.carrierSet ∧
          (∀ r : N.Carrier, dist w (g w) ≤ dist w r.val) ∧
          ∀ r : N.Carrier,
            (∀ s : N.Carrier, dist w r.val ≤ dist w s.val) → r.val = g w) ∧
        z ∈ Metric.ball p.val delta}
  have hOo : IsOpen O := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    obtain ⟨p, delta, hdelta, g, hg, hmin, hzball⟩ := hz
    exact Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hzball)
      (fun w hw => ⟨p, delta, hdelta, g, hg, hmin, hw⟩)
  have hNO : N.carrierSet ⊆ O := by
    intro p hp
    obtain ⟨delta, hdelta, g, hg, hmin⟩ :=
      N.exists_local_nearest_smooth_certificate ⟨p, hp⟩
    exact ⟨⟨p, hp⟩, delta, hdelta, g, hg, hmin, Metric.mem_ball_self hdelta⟩
  obtain ⟨eta, heta, hEta⟩ := N.isCompact.exists_thickening_subset_open hOo hNO
  have hrho : 2 * (eta / 2) = eta := by rw [two_mul, add_halves]
  let U : Set (EuclideanSpace ℝ (Fin q)) :=
    {w | Metric.infDist w N.carrierSet < 2 * (eta / 2)}
  have hUo : IsOpen U :=
    isOpen_lt (Metric.continuous_infDist_pt N.carrierSet) continuous_const
  refine ⟨eta / 2, half_pos heta, ?_⟩
  intro z hz
  have hzO : z ∈ O := by
    apply hEta
    apply (Metric.mem_thickening_iff_infDist_lt N.nonempty).mpr
    rwa [hrho] at hz
  obtain ⟨p, delta, hdelta, g, hg, hmin, hzball⟩ := hzO
  have hzU : z ∈ U := hz
  obtain ⟨epsilon, hepsilon, hBall⟩ := Metric.isOpen_iff.mp
    (Metric.isOpen_ball.inter hUo) z ⟨hzball, hzU⟩
  refine ⟨epsilon, hepsilon, fun w hw => (hBall hw).2, g, ?_, ?_⟩
  · exact hg.mono (fun w hw => (hBall hw).1)
  · intro w hw
    exact hmin w (hBall hw).1

end HarmonicMaps.CompactSmoothEmbeddedTarget

end
