-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import StationaryHarmonicMaps.Providers.NormalProjectionCharacterization

/-! # Complete characterization of the actual normal projection -/

public section

namespace StationaryHarmonicMaps.CompactC2EmbeddedTarget

theorem normalProjection_characterization :
    ∀ {q : ℕ} (N : CompactC2EmbeddedTarget q) (p : N.Carrier),
    (∀ v : EuclideanSpace ℝ (Fin q),
      N.normalProjection p v ∈ (N.tangentImage p)ᗮ ∧
        v - N.normalProjection p v ∈ N.tangentImage p) ∧
    ∀ P : EuclideanSpace ℝ (Fin q) →L[ℝ] EuclideanSpace ℝ (Fin q),
      (∀ v : EuclideanSpace ℝ (Fin q),
        P v ∈ (N.tangentImage p)ᗮ ∧ v - P v ∈ N.tangentImage p) ↔
        P = N.normalProjection p :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact StationaryHarmonicMaps.Providers.normalProjectionCharacterization
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end StationaryHarmonicMaps.CompactC2EmbeddedTarget

end
-- FROZEN_ANCHOR_SUFFIX_END
