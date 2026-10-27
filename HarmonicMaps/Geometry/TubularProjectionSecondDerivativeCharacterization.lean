module
public import HarmonicMaps.Geometry.TubularProjectionSecondDerivative
import HarmonicMaps.Providers.TubularProjectionSecondDerivativeCharacterization

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section
open scoped ContDiff
namespace HarmonicMaps

theorem tubularProjectionSecondDerivative_characterization (q : ℕ) (N : CompactSmoothEmbeddedTarget q) :
  (∀ (z : tubularTube q N) (V : Set (Ambient q)) (g : Ambient q → Ambient q),
    IsOpen V → z.val ∈ V → V ⊆ tubularTube q N → ContDiffOn ℝ ∞ g V →
    (∀ w : tubularTube q N, w.val ∈ V → g w.val = (tubularProjection q N w).val) →
    fderiv ℝ (fderiv ℝ g) z.val = tubularProjectionSecondDerivative q N z) ∧
  (∀ z : tubularTube q N, ∃ V : Set (Ambient q),
    IsOpen V ∧ z.val ∈ V ∧ V ⊆ tubularTube q N ∧
    ∃ g : Ambient q → Ambient q,
      ContDiffOn ℝ ∞ g V ∧
      (∀ w : tubularTube q N, w.val ∈ V → g w.val = (tubularProjection q N w).val) ∧
      ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ g)) V ∧
      ∀ w : tubularTube q N, w.val ∈ V →
        fderiv ℝ (fderiv ℝ g) w.val = tubularProjectionSecondDerivative q N w) ∧
  ∀ S : tubularTube q N → (Ambient q →L[ℝ] (Ambient q →L[ℝ] Ambient q)),
    (∀ (z : tubularTube q N) (V : Set (Ambient q)) (g : Ambient q → Ambient q),
      IsOpen V → z.val ∈ V → V ⊆ tubularTube q N → ContDiffOn ℝ ∞ g V →
      (∀ w : tubularTube q N, w.val ∈ V → g w.val = (tubularProjection q N w).val) →
      fderiv ℝ (fderiv ℝ g) z.val = S z) → S = tubularProjectionSecondDerivative q N :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact HarmonicMaps.Providers.TubularProjectionSecondDerivativeCharacterization.result q N
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HarmonicMaps
end
-- FROZEN_ANCHOR_SUFFIX_END
