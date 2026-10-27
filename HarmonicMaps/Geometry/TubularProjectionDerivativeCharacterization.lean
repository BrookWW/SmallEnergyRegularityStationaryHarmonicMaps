module
public import HarmonicMaps.Geometry.TubularProjectionDerivative
import HarmonicMaps.Providers.TubularProjectionDerivativeCharacterization

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section
open scoped ContDiff
namespace HarmonicMaps

theorem tubularProjectionDerivative_characterization (q : ℕ) (N : CompactSmoothEmbeddedTarget q) :
  (∀ (z : tubularTube q N) (V : Set (Ambient q)) (g : Ambient q → Ambient q),
    IsOpen V → z.val ∈ V → V ⊆ tubularTube q N → ContDiffOn ℝ ∞ g V →
    (∀ w : tubularTube q N, w.val ∈ V → g w.val = (tubularProjection q N w).val) →
    fderiv ℝ g z.val = tubularProjectionDerivative q N z) ∧
  (∀ z : tubularTube q N, ∃ V : Set (Ambient q),
    IsOpen V ∧ z.val ∈ V ∧ V ⊆ tubularTube q N ∧
    ∃ g : Ambient q → Ambient q,
      ContDiffOn ℝ ∞ g V ∧
      (∀ w : tubularTube q N, w.val ∈ V → g w.val = (tubularProjection q N w).val) ∧
      ContDiffOn ℝ ∞ (fderiv ℝ g) V ∧
      ∀ w : tubularTube q N, w.val ∈ V →
        fderiv ℝ g w.val = tubularProjectionDerivative q N w) ∧
  ∀ S : tubularTube q N → (Ambient q →L[ℝ] Ambient q),
    (∀ (z : tubularTube q N) (V : Set (Ambient q)) (g : Ambient q → Ambient q),
      IsOpen V → z.val ∈ V → V ⊆ tubularTube q N → ContDiffOn ℝ ∞ g V →
      (∀ w : tubularTube q N, w.val ∈ V → g w.val = (tubularProjection q N w).val) →
      fderiv ℝ g z.val = S z) → S = tubularProjectionDerivative q N :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact HarmonicMaps.Providers.TubularProjectionDerivativeCharacterization.result q N
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HarmonicMaps
end
-- FROZEN_ANCHOR_SUFFIX_END
