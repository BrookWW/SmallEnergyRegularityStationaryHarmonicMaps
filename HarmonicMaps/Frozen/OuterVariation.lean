module
public import HarmonicMaps.Frozen.TubularProjection
public import HarmonicMaps.Minimizer
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import HarmonicMaps.Providers.OuterVariation

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section
open MeasureTheory Filter Set
open scoped ContDiff
namespace HarmonicMaps

theorem outerVariation_weakEquation (q : ℕ) (N : CompactSmoothEmbeddedTarget q) :
  let S : Set ℝ := {k | ∃ p : N.Carrier, ∃ hp : p.val ∈ tubularTube q N,
    k = ‖tubularProjectionSecondDerivative q N ⟨p.val, hp⟩‖}
  ∀ (n : ℕ) (hn : 2 ≤ n) (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q),
    MemW12Loc Ω u Du → TakesValuesIn N Ω u →
    IsLocallyEnergyMinimizing N Ω u Du →
    ∃ F : Domain n → Ambient q,
      LocallyIntegrableOn F Ω.val volume ∧
      (∀ᵐ x ∂volume.restrict Ω.val, ∃ hx : u x ∈ tubularTube q N,
        F x = ∑ i : Fin n,
          tubularProjectionSecondDerivative q N ⟨u x, hx⟩ (Du x i) (Du x i) ∧
        ‖F x‖ ≤ sSup S * hsNormSq (Du x)) ∧
      ∀ (ψ : Domain n → Ambient q), ContDiff ℝ ∞ ψ →
        HasCompactSupport ψ → tsupport ψ ⊆ Ω.val →
        IntegrableOn (fun x => ∑ i : Fin n,
          inner ℝ (Du x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) Ω.val ∧
        IntegrableOn (fun x => inner ℝ (F x) (ψ x)) Ω.val ∧
        (∫ x in Ω.val, ∑ i : Fin n,
          inner ℝ (Du x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
          -(∫ x in Ω.val, inner ℝ (F x) (ψ x)) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact HarmonicMaps.Providers.OuterVariation.result q N
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HarmonicMaps
end
-- FROZEN_ANCHOR_SUFFIX_END
