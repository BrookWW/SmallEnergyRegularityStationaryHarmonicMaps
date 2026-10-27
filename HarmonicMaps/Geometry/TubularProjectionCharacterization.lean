module
public import HarmonicMaps.Geometry.TubularProjection
import HarmonicMaps.Providers.TubularProjectionCharacterization

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section
open Set
open scoped ContDiff
namespace HarmonicMaps

theorem tubularProjection_characterization (q : ℕ) (N : CompactSmoothEmbeddedTarget q) :
  0 < tubularBaseRadius q N ∧
  let U := tubularTube q N
  let P := tubularProjection q N
  IsOpen U ∧
  (∀ z : U,
    (∀ p : N.Carrier, dist z.val (P z).val ≤ dist z.val p.val) ∧
    ∀ p : N.Carrier,
      (∀ p' : N.Carrier, dist z.val p.val ≤ dist z.val p'.val) → p = P z) ∧
  (∀ p : N.Carrier, ∃ hp : p.val ∈ U, P ⟨p.val, hp⟩ = p) ∧
  (∀ z : U, ∃ V : Set (Ambient q), IsOpen V ∧ z.val ∈ V ∧ V ⊆ U ∧
    ∃ g : Ambient q → Ambient q, ContDiffOn ℝ ∞ g V ∧
      ∀ w : U, w.val ∈ V → g w.val = (P w).val) ∧
  (∀ (z : U) (V₁ V₂ : Set (Ambient q)) (g₁ g₂ : Ambient q → Ambient q),
    IsOpen V₁ → IsOpen V₂ → z.val ∈ V₁ → z.val ∈ V₂ → V₁ ⊆ U → V₂ ⊆ U →
    ContDiffOn ℝ ∞ g₁ V₁ → ContDiffOn ℝ ∞ g₂ V₂ →
    (∀ w : U, w.val ∈ V₁ → g₁ w.val = (P w).val) →
    (∀ w : U, w.val ∈ V₂ → g₂ w.val = (P w).val) →
    fderiv ℝ g₁ z.val = fderiv ℝ g₂ z.val ∧
    fderiv ℝ (fderiv ℝ g₁) z.val = fderiv ℝ (fderiv ℝ g₂) z.val) ∧
  ∀ S : U → N.Carrier,
    (∀ z : U, ∀ p : N.Carrier, dist z.val (S z).val ≤ dist z.val p.val) → S = P :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact HarmonicMaps.Providers.TubularProjectionCharacterization.result q N
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HarmonicMaps
end
-- FROZEN_ANCHOR_SUFFIX_END
