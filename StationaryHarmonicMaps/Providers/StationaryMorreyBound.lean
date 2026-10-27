module

public import StationaryHarmonicMaps.Foundation.CriticalGradientMorrey
public import StationaryHarmonicMaps.Analysis.StationaryMorreyBound

/-! # All-center critical Morrey control from the stationary stress identity -/

public section

open HarmonicMaps MeasureTheory Set

namespace StationaryHarmonicMaps.Providers

/-- Interior localization of the source critical Morrey quantity. -/
theorem stationaryMorreyBound :
    ∀ {n q : ℕ} (_hn : 2 ≤ n) {Ω : OpenDomain n}
      {u : Domain n → Ambient q} {Du : Domain n → Gradient n q},
      IsDomainStationary Ω Du → MemW12Loc Ω u Du →
      ∀ {a : Domain n} {R : ℝ} (hR : 0 < R),
        Metric.closedBall a R ⊆ Ω.val →
        criticalGradientMorreySquare Du (Metric.ball a (3 * R / 4)) ≤
          ENNReal.ofReal ((4 : ℝ) ^ (n - 2)) * normalizedEnergy Du a ⟨R, hR⟩ := by
  intro n q hn Ω u Du hstationary hu a R hR hball
  refine iSup_le fun x => iSup_le fun r => ?_
  exact Analysis.stationary_truncated_ball_energy_bound hn hstationary hu hR hball
    x.property r.property

end StationaryHarmonicMaps.Providers

end
