-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import StationaryHarmonicMaps.Providers.StationaryMorreyBound

/-! # Interior localization of the critical Morrey bound -/

public section

open HarmonicMaps MeasureTheory Set

namespace StationaryHarmonicMaps

theorem stationary_morrey_bound :
    ∀ {n q : ℕ} (_hn : 2 ≤ n) {Ω : OpenDomain n}
      {u : Domain n → Ambient q} {Du : Domain n → Gradient n q},
      IsDomainStationary Ω Du → MemW12Loc Ω u Du →
      ∀ {a : Domain n} {R : ℝ} (hR : 0 < R),
        Metric.closedBall a R ⊆ Ω.val →
        criticalGradientMorreySquare Du (Metric.ball a (3 * R / 4)) ≤
          ENNReal.ofReal ((4 : ℝ) ^ (n - 2)) * normalizedEnergy Du a ⟨R, hR⟩ :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact StationaryHarmonicMaps.Providers.stationaryMorreyBound
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end StationaryHarmonicMaps

end
-- FROZEN_ANCHOR_SUFFIX_END
