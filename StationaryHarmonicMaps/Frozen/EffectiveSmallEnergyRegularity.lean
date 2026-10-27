-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import StationaryHarmonicMaps.Providers.EffectiveSmallEnergyRegularity

/-! # Effective stationary small-energy regularity for compact C² targets -/

public section
open HarmonicMaps MeasureTheory Set Metric
open scoped ContDiff ENNReal
namespace StationaryHarmonicMaps

theorem stationary_small_energy_regularity_effective {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactC2EmbeddedTarget q)
    (G : Ambient q → (Ambient q →L[ℝ] Ambient q)) (L : ℚ)
    (hG : ContDiff ℝ 1 G) (hcG : HasCompactSupport G)
    (hGN : ∀ p : N.Carrier,G p.val=N.normalProjection p)
    (hL : 0≤L) (hDG : ∀ y,‖fderiv ℝ G y‖≤(L:ℝ)) :
      ∀ (Ω : OpenDomain n) (u : Domain n → Ambient q)
        (Du : Domain n → Gradient n q),
        MemW12Loc Ω u Du →
        (∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet) →
        IsWeaklyHarmonicByTangentVariations N Ω u Du →
        IsDomainStationary Ω Du →
        ∀ (a : Domain n) (R : PositiveRadius),
          Metric.closedBall a R.val ⊆ Ω.val →
          normalizedEnergy Du a R ≤ ENNReal.ofReal (Analysis.effectiveStationaryEnergyThreshold n q L:ℝ) →
          ∃ w : Metric.ball a (R.val / 2) → Ambient q,
            IsContinuousRepresentative (ballDomain a (R.val / 2)) u w ∧
            (∀ x, w x ∈ N.carrierSet) ∧
            (∀ x y,
              ‖w x - w y‖ ≤ (Analysis.effectiveStationaryHolderConstant n q L:ℝ) * Real.rpow R.val (-(1/2:ℝ)) *
                Real.sqrt (normalizedEnergy Du a R).toReal *
                Real.rpow (dist (x : Domain n) (y : Domain n)) (1/2:ℝ)) ∧
            ∀ v : Metric.ball a (R.val / 2) → Ambient q,
              IsContinuousRepresentative (ballDomain a (R.val / 2)) u v → v = w :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  Providers.smallEnergyRegularity_effective hn N G L hG hcG hGN hL hDG
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end StationaryHarmonicMaps
end
-- FROZEN_ANCHOR_SUFFIX_END
