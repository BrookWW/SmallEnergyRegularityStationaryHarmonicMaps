-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import StationaryHarmonicMaps.Providers.SmallEnergyRegularity

/-! # Small-energy regularity for stationary harmonic maps into compact C² targets -/

public section

open HarmonicMaps MeasureTheory Set

namespace StationaryHarmonicMaps

theorem stationary_small_energy_regularity {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactC2EmbeddedTarget q) :
    ∃ ε α C : ℝ, 0 < ε ∧ 0 < α ∧ α < 1 ∧ 0 ≤ C ∧
      ∀ (Ω : OpenDomain n) (u : Domain n → Ambient q)
        (Du : Domain n → Gradient n q),
        MemW12Loc Ω u Du →
        (∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet) →
        IsWeaklyHarmonicByTangentVariations N Ω u Du →
        IsDomainStationary Ω Du →
        ∀ (a : Domain n) (R : PositiveRadius),
          Metric.closedBall a R.val ⊆ Ω.val →
          normalizedEnergy Du a R ≤ ENNReal.ofReal ε →
          ∃ w : Metric.ball a (R.val / 2) → Ambient q,
            IsContinuousRepresentative (ballDomain a (R.val / 2)) u w ∧
            (∀ x, w x ∈ N.carrierSet) ∧
            (∀ x y,
              ‖w x - w y‖ ≤ C * Real.rpow R.val (-α) *
                Real.sqrt (normalizedEnergy Du a R).toReal *
                Real.rpow (dist (x : Domain n) (y : Domain n)) α) ∧
            ∀ v : Metric.ball a (R.val / 2) → Ambient q,
              IsContinuousRepresentative (ballDomain a (R.val / 2)) u v → v = w :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact StationaryHarmonicMaps.Providers.smallEnergyRegularity hn N
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end StationaryHarmonicMaps

end
-- FROZEN_ANCHOR_SUFFIX_END
