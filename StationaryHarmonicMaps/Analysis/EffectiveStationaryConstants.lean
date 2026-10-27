module

public import StationaryHarmonicMaps.Analysis.CriticalNativeCoulombBallExistence
public import StationaryHarmonicMaps.Analysis.CompensatedSystemRepresentative
public import StationaryHarmonicMaps.Analysis.EffectiveEnergyAmplitudes

/-! Rational constants for stationary small-energy regularity. -/

@[expose] public section
namespace StationaryHarmonicMaps.Analysis

/-- A conservative rational normalized-energy threshold. -/
def effectiveStationaryEnergyThreshold (n q : ℕ) (L : ℚ) : ℚ :=
  rationalEnergyThreshold n q L (effectiveCoulombFrameGradientConstant n q)
    (effectiveCoulombFrameSmallness n q) (effectiveGivenFrameSmallness n q)

/-- A rational coefficient for the half-Hölder estimate on the half ball. -/
def effectiveStationaryHolderConstant (n q : ℕ) (L : ℚ) : ℚ :=
  rationalHolderCoefficient n q L (effectiveCoulombFrameGradientConstant n q)
    (effectiveGivenFrameHolderConstant n q)

theorem effectiveStationaryEnergyThreshold_pos (n : ℕ) (hn : 2≤n) (q : ℕ) (L : ℚ) :
    0<effectiveStationaryEnergyThreshold n q L :=
  rationalEnergyThreshold_pos n q L
    (effectiveCoulombFrameGradientConstant_pos n hn q).le
    (effectiveCoulombFrameSmallness_pos n hn q) (effectiveGivenFrameSmallness_pos n q)

theorem effectiveStationaryHolderConstant_pos (n : ℕ) (hn : 2≤n) (q : ℕ) (L : ℚ) :
    0<effectiveStationaryHolderConstant n q L :=
  rationalHolderCoefficient_pos n q L
    (effectiveCoulombFrameGradientConstant_pos n hn q).le
    (effectiveGivenFrameHolderConstant_pos n q)

end StationaryHarmonicMaps.Analysis
end
