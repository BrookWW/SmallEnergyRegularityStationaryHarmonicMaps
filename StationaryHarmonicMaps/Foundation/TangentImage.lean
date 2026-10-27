module

public import StationaryHarmonicMaps.Foundation.C2Target

/-! # Ambient tangent subspaces

The tangent subspace is the range of the actual inclusion differential.
-/

@[expose] public section

open scoped Manifold ContDiff

namespace StationaryHarmonicMaps.CompactC2EmbeddedTarget

variable {q : ℕ}

/-- The ambient tangent subspace is the image of the actual inclusion differential. -/
noncomputable def tangentImage (N : CompactC2EmbeddedTarget q) (p : N.Carrier) :
    Submodule ℝ (EuclideanSpace ℝ (Fin q)) :=
  (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension))
    𝓘(ℝ, EuclideanSpace ℝ (Fin q)) N.embedding p).range


end StationaryHarmonicMaps.CompactC2EmbeddedTarget

end
