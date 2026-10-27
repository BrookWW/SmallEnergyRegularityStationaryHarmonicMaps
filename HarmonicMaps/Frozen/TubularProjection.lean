module
public import HarmonicMaps.Geometry.TubularProjectionDerivativeCharacterization
public import HarmonicMaps.Geometry.TubularProjectionSecondDerivativeCharacterization
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import HarmonicMaps.Providers.TubularProjection

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section
open scoped ContDiff Manifold
namespace HarmonicMaps

theorem tubularProjection_complete (q : ℕ) (N : CompactSmoothEmbeddedTarget q) :
  ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ tubularBaseRadius q N ∧
  let U : Set (Ambient q) := {z | Metric.infDist z N.carrierSet < 2 * ρ}
  ∃ hsub : U ⊆ tubularTube q N,
    IsOpen U ∧
    (∀ z : U,
      (∀ p : N.Carrier,
        dist z.val (tubularProjection q N ⟨z.val, hsub z.property⟩).val ≤
          dist z.val p.val) ∧
      ∀ p : N.Carrier,
        (∀ p' : N.Carrier, dist z.val p.val ≤ dist z.val p'.val) →
        p = tubularProjection q N ⟨z.val, hsub z.property⟩) ∧
    (∀ p : N.Carrier, ∃ hp : p.val ∈ U,
      tubularProjection q N ⟨p.val, hsub hp⟩ = p ∧
      tubularProjectionDerivative q N ⟨p.val, hsub hp⟩ =
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension)) 𝓘(ℝ, Ambient q)
          (Subtype.val : N.Carrier → Ambient q) p).range.starProjection) ∧
    (∀ z : U, ∃ V : Set (Ambient q), IsOpen V ∧ z.val ∈ V ∧ V ⊆ U ∧
      ∃ g : Ambient q → Ambient q, ContDiffOn ℝ ∞ g V ∧
        ∀ w : U, w.val ∈ V →
          g w.val = (tubularProjection q N ⟨w.val, hsub w.property⟩).val) ∧
    (∀ z : U, ‖tubularProjectionDerivative q N ⟨z.val, hsub z.property⟩‖ ≤ 2) ∧
    let S : Set ℝ := {k | ∃ p : N.Carrier, ∃ hp : p.val ∈ tubularTube q N,
      k = ‖tubularProjectionSecondDerivative q N ⟨p.val, hp⟩‖}
    S.Nonempty ∧ BddAbove S ∧ 0 ≤ sSup S ∧
    (∀ (p : N.Carrier) (hp : p.val ∈ tubularTube q N),
      ‖tubularProjectionSecondDerivative q N ⟨p.val, hp⟩‖ ≤ sSup S) ∧
    ∃ Q : Ambient q → Ambient q, ContDiff ℝ ∞ Q ∧
      (∀ z : tubularTube q N, Metric.infDist z.val N.carrierSet < ρ →
        Q z.val = (tubularProjection q N z).val) ∧
      ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
        (∀ z, ‖fderiv ℝ Q z‖ ≤ C₁) ∧
        ∀ z, ‖fderiv ℝ (fderiv ℝ Q) z‖ ≤ C₂ :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact HarmonicMaps.Providers.TubularProjection.result q N
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HarmonicMaps
end
-- FROZEN_ANCHOR_SUFFIX_END
