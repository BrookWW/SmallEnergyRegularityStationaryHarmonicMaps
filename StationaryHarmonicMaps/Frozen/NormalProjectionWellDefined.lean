-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import StationaryHarmonicMaps.Providers.NormalProjectionWellDefined

/-! # Well-definedness of the ambient normal projection -/

public section

namespace StationaryHarmonicMaps.CompactC2EmbeddedTarget

theorem normalProjection_existsUnique :
    ∀ {q : ℕ} (N : CompactC2EmbeddedTarget q) (p : N.Carrier),
      ∃! P : EuclideanSpace ℝ (Fin q) →L[ℝ] EuclideanSpace ℝ (Fin q),
        ∀ v : EuclideanSpace ℝ (Fin q),
          P v ∈ (N.tangentImage p)ᗮ ∧ v - P v ∈ N.tangentImage p :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact StationaryHarmonicMaps.Providers.normalProjectionExistsUnique
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end StationaryHarmonicMaps.CompactC2EmbeddedTarget

end
-- FROZEN_ANCHOR_SUFFIX_END
