module
public import HarmonicMaps.Geometry.TubularProjectionCharacterization
import HarmonicMaps.Providers.TubularProjectionSecondDerivativeWellDefined

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section
open scoped ContDiff
namespace HarmonicMaps

theorem tubularProjectionSecondDerivativeWellDefined (q : ℕ) (N : CompactSmoothEmbeddedTarget q)
    (z : tubularTube q N) :
  ∃! H : Ambient q →L[ℝ] (Ambient q →L[ℝ] Ambient q),
    ∀ (V : Set (Ambient q)) (g : Ambient q → Ambient q),
      IsOpen V → z.val ∈ V → V ⊆ tubularTube q N → ContDiffOn ℝ ∞ g V →
      (∀ w : tubularTube q N, w.val ∈ V → g w.val = (tubularProjection q N w).val) →
      fderiv ℝ (fderiv ℝ g) z.val = H :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact HarmonicMaps.Providers.TubularProjectionSecondDerivativeWellDefined.result q N z
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HarmonicMaps
end
-- FROZEN_ANCHOR_SUFFIX_END
