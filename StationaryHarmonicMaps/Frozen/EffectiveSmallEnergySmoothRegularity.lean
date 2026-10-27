-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import StationaryHarmonicMaps.Providers.EffectiveSmallEnergyRegularity

/-! # Effective stationary small-energy regularity for smooth targets -/

public section
open HarmonicMaps MeasureTheory Set Metric
open scoped ContDiff ENNReal
namespace StationaryHarmonicMaps

theorem stationary_small_energy_smooth_regularity_effective {n q : ℕ} (hn : 2≤n)
    (N : CompactSmoothEmbeddedTarget q)
    (G : Ambient q → (Ambient q →L[ℝ] Ambient q)) (L : ℚ)
    (hG : ContDiff ℝ 1 G) (hcG : HasCompactSupport G)
    (hGN : ∀ p : (SmoothTarget.toC2 N).Carrier,
      G p.val=(SmoothTarget.toC2 N).normalProjection p)
    (hL : 0≤L) (hDG : ∀ y,‖fderiv ℝ G y‖≤(L:ℝ)) :
      ∀(Ω : OpenDomain n) (u : Domain n→Ambient q) (Du : Domain n→Gradient n q),
        MemW12Loc Ω u Du →
        (∀ᵐx∂volume.restrict Ω.val,u x∈N.carrierSet) →
        IsWeaklyHarmonicByTangentVariations (SmoothTarget.toC2 N) Ω u Du →
        IsDomainStationary Ω Du →
        ∀(a : Domain n) (R : PositiveRadius),closedBall a R.val⊆Ω.val →
          normalizedEnergy Du a R≤ENNReal.ofReal (Analysis.effectiveStationaryEnergyThreshold n q L:ℝ) →
          ∃w : Domain n→Ambient q,
            ContDiffOn ℝ ∞ w (ball a (R.val/2)) ∧
            IsContinuousRepresentative (ballDomain a (R.val/2)) u (fun x=>w x.val) ∧
            (∀x∈ball a (R.val/2),w x∈N.carrierSet) ∧
            (∀x∈ball a (R.val/2),∀y∈ball a (R.val/2),
              ‖w x-w y‖≤(Analysis.effectiveStationaryHolderConstant n q L:ℝ)*R.val^(-(1/2:ℝ))*Real.sqrt (normalizedEnergy Du a R).toReal*(dist x y)^(1/2:ℝ)) ∧
            ∀v : ball a (R.val/2)→Ambient q,
              IsContinuousRepresentative (ballDomain a (R.val/2)) u v →
              v=(fun x=>w x.val) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  Providers.smallEnergySmoothRegularity_effective hn N G L hG hcG hGN hL hDG
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end StationaryHarmonicMaps
end
-- FROZEN_ANCHOR_SUFFIX_END
