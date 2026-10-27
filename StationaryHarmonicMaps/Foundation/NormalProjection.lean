module

public import StationaryHarmonicMaps.Foundation.TangentImage
public import StationaryHarmonicMaps.Frozen.NormalProjectionWellDefined
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! # The orthogonal normal projection of the actual embedded target -/

@[expose] public section

namespace StationaryHarmonicMaps.CompactC2EmbeddedTarget

/-- The orthogonal projection onto the normal subspace at a genuine target point. -/
noncomputable def normalProjection {q : ℕ} (N : CompactC2EmbeddedTarget q)
    (p : N.Carrier) :
    EuclideanSpace ℝ (Fin q) →L[ℝ] EuclideanSpace ℝ (Fin q) :=
  (N.tangentImage p)ᗮ.starProjection

end StationaryHarmonicMaps.CompactC2EmbeddedTarget

end
