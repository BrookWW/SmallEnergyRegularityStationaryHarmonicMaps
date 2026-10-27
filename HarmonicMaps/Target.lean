module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Geometry.Manifold.SmoothEmbedding

/-! # Compact smooth embedded targets

The target is an actual subset of a finite-dimensional Euclidean space, with its
induced topology. Its manifold charts use a full Euclidean model, so it has no
boundary. Smooth embeddedness includes immersion, not merely smoothness of the
inclusion and topological embeddedness.

This structure records the standing target assumptions in the manuscript. It
contains no tubular neighborhood, nearest-point projection, curvature estimate,
or other consequence that remains to be proved.
-/

@[expose] public section

open scoped Manifold ContDiff

namespace HarmonicMaps

/-- A nonempty compact smooth embedded submanifold of Euclidean space, without boundary.

The target metric in the manuscript is the metric induced by the ambient Euclidean
inner product. No independent metric or geometric proof obligation is bundled here.
-/
structure CompactSmoothEmbeddedTarget (q : ℕ) where
  /-- The intrinsic dimension of the target manifold. -/
  dimension : ℕ
  /-- The target as an actual subset of the ambient Euclidean space. -/
  carrierSet : Set (EuclideanSpace ℝ (Fin q))
  /-- The target subset is nonempty. -/
  nonempty : carrierSet.Nonempty
  /-- The target subset is compact in its induced ambient topology. -/
  isCompact : IsCompact carrierSet
  /-- Charts into the full Euclidean model, with the subtype topology on the target. -/
  [chartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin dimension)) carrierSet]
  /-- The target is infinitely differentiable in this charted structure. -/
  [isManifold : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin dimension)) ∞ carrierSet]
  /-- The inclusion is a smooth immersion and a topological embedding. -/
  isSmoothEmbedding :
    Manifold.IsSmoothEmbedding
      𝓘(ℝ, EuclideanSpace ℝ (Fin dimension)) 𝓘(ℝ, EuclideanSpace ℝ (Fin q)) ∞
      (Subtype.val : carrierSet → EuclideanSpace ℝ (Fin q))

namespace CompactSmoothEmbeddedTarget

variable {q : ℕ}

/-- The manifold carrier is the subtype of the actual ambient target subset. -/
abbrev Carrier (N : CompactSmoothEmbeddedTarget q) : Type := N.carrierSet

instance instChartedSpace (N : CompactSmoothEmbeddedTarget q) :
    ChartedSpace (EuclideanSpace ℝ (Fin N.dimension)) N.Carrier :=
  N.chartedSpace

instance instIsManifold (N : CompactSmoothEmbeddedTarget q) :
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension)) ∞ N.Carrier :=
  N.isManifold

instance instNonempty (N : CompactSmoothEmbeddedTarget q) : Nonempty N.Carrier :=
  N.nonempty.to_subtype

instance instCompactSpace (N : CompactSmoothEmbeddedTarget q) : CompactSpace N.Carrier :=
  isCompact_iff_compactSpace.mp N.isCompact

/-- The ambient embedding is exactly the subtype inclusion. -/
abbrev embedding (N : CompactSmoothEmbeddedTarget q) :
    N.Carrier → EuclideanSpace ℝ (Fin q) :=
  Subtype.val

/-- The intrinsic manifold has no boundary because its model is the full Euclidean space. -/
theorem boundaryless (N : CompactSmoothEmbeddedTarget q) :
    BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension)) N.Carrier :=
  inferInstance

/-- Compactness makes the actual ambient target subset closed. -/
theorem isClosed (N : CompactSmoothEmbeddedTarget q) : IsClosed N.carrierSet :=
  N.isCompact.isClosed

/-- The ambient range of the embedding is exactly the specified target subset. -/
@[simp] theorem range_embedding (N : CompactSmoothEmbeddedTarget q) :
    Set.range N.embedding = N.carrierSet :=
  Subtype.range_val

/-- Every point of the manifold carrier lies in the specified ambient target subset. -/
theorem embedding_mem (N : CompactSmoothEmbeddedTarget q) (p : N.Carrier) :
    N.embedding p ∈ N.carrierSet :=
  p.property

end CompactSmoothEmbeddedTarget
end HarmonicMaps

end
