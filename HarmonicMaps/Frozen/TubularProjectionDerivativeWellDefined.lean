module
public import HarmonicMaps.Geometry.TubularProjectionCharacterization
import HarmonicMaps.Providers.TubularProjectionDerivativeWellDefined

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section
open scoped ContDiff
namespace HarmonicMaps

theorem tubularProjectionDerivativeWellDefined (q : ℕ) (N : CompactSmoothEmbeddedTarget q)
    (z : tubularTube q N) :
  ∃! D : Ambient q →L[ℝ] Ambient q,
    ∀ (V : Set (Ambient q)) (g : Ambient q → Ambient q),
      IsOpen V → z.val ∈ V → V ⊆ tubularTube q N → ContDiffOn ℝ ∞ g V →
      (∀ w : tubularTube q N, w.val ∈ V → g w.val = (tubularProjection q N w).val) →
      fderiv ℝ g z.val = D :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact HarmonicMaps.Providers.TubularProjectionDerivativeWellDefined.result q N z
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HarmonicMaps
end
-- FROZEN_ANCHOR_SUFFIX_END
