module

public import HarmonicMaps.Geometry.TargetNearestPoint
import Mathlib.Tactic.Linarith

/-!
# Local confinement of all nearest points

Every closest point lies in a prescribed open neighborhood of a target point
when the ambient input is sufficiently close to that point. The local radius
comes from the actual neighborhood, and existence comes from compactness.
-/

public section

open Set

namespace HarmonicMaps.CompactSmoothEmbeddedTarget

/-- A local neighborhood confines all genuine competing minimizers. -/
theorem nearest_points_localize {q : ℕ} (N : CompactSmoothEmbeddedTarget q)
    (p : N.Carrier) (V : Set (EuclideanSpace ℝ (Fin q)))
    (hV : IsOpen V) (hpV : p.val ∈ V) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : EuclideanSpace ℝ (Fin q),
      dist z p.val < δ →
      (∃ r : N.Carrier, r.val ∈ V ∧
        dist z r.val = Metric.infDist z N.carrierSet ∧
        ∀ s : N.Carrier, dist z r.val ≤ dist z s.val) ∧
      ∀ r : N.Carrier,
        (∀ s : N.Carrier, dist z r.val ≤ dist z s.val) → r.val ∈ V := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV p.val hpV
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro z hz
  have hall (r : N.Carrier)
      (hr : ∀ s : N.Carrier, dist z r.val ≤ dist z s.val) : r.val ∈ V := by
    apply hball
    change dist r.val p.val < ε
    have hmin := hr p
    have htri := dist_triangle r.val z p.val
    rw [dist_comm r.val z] at htri
    linarith only [hz, hmin, htri]
  obtain ⟨r, heq, hr⟩ := N.exists_nearest_point z
  exact ⟨⟨r, hall r hr, heq, hr⟩, hall⟩

/-- All nearby minimizers lie in the actual target chart source. -/
theorem nearest_points_mem_chart {q : ℕ} (N : CompactSmoothEmbeddedTarget q)
    (p : N.Carrier) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : EuclideanSpace ℝ (Fin q),
      dist z p.val < δ → ∀ r : N.Carrier,
        (∀ s : N.Carrier, dist z r.val ≤ dist z s.val) →
          r ∈ (chartAt (EuclideanSpace ℝ (Fin N.dimension)) p).source := by
  let e := chartAt (EuclideanSpace ℝ (Fin N.dimension)) p
  obtain ⟨V, hV, heq⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp e.open_source
  have hpV : p.val ∈ V := by
    change p ∈ (Subtype.val : N.Carrier → EuclideanSpace ℝ (Fin q)) ⁻¹' V
    rw [heq]
    exact mem_chart_source _ p
  obtain ⟨δ, hδ, hlocal⟩ := N.nearest_points_localize p V hV hpV
  refine ⟨δ, hδ, ?_⟩
  intro z hz r hr
  have hmem : r ∈ (Subtype.val : N.Carrier → EuclideanSpace ℝ (Fin q)) ⁻¹' V :=
    (hlocal z hz).2 r hr
  rwa [heq] at hmem

end HarmonicMaps.CompactSmoothEmbeddedTarget

end
