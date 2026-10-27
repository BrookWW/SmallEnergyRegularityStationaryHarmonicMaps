module

public import HarmonicMaps
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import HarmonicMaps.Analysis.GeneralBallRegularity

/-! # SmallEnergyRegularity proof implementation

The regularity theorem follows from unit-ball regularity and affine
transport of continuous representatives, using the given Sobolev and
local energy-minimizing data.
-/

public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace HarmonicMaps.Providers.SmallEnergyRegularity

theorem result
    {n q : ℕ} (hn : 2 ≤ n) (N : CompactSmoothEmbeddedTarget q) :
    ∃ ε α : ℝ, ∃ C : ℝ≥0,
      0 < ε ∧ 0 < α ∧ α < 1 ∧
      ∀ (Ω : OpenDomain n) (u : Domain n → Ambient q)
        (Du : Domain n → Gradient n q),
        MemW12Loc Ω u Du →
        TakesValuesIn N Ω u →
        IsLocallyEnergyMinimizing N Ω u Du →
        ∀ (a : Domain n) (R : PositiveRadius),
          Metric.closedBall a R.val ⊆ Ω.val →
          normalizedEnergy Du a R ≤ ENNReal.ofReal ε →
          ∃ w : Metric.ball a (R.val / 2) → Ambient q,
            IsContinuousRepresentative (ballDomain a (R.val / 2)) u w ∧
            (∀ x, w x ∈ N.carrierSet) ∧
            (∀ x y : Metric.ball a (R.val / 2),
              ‖w x - w y‖ ≤
                (C : ℝ) * Real.rpow R.val (-α) *
                  Real.sqrt (normalizedEnergy Du a R).toReal *
                  Real.rpow (dist (x : Domain n) (y : Domain n)) α) ∧
            ∀ v : Metric.ball a (R.val / 2) → Ambient q,
              IsContinuousRepresentative (ballDomain a (R.val / 2)) u v →
              v = w := by
  exact HarmonicMaps.generalBallRegularity_complete hn N

end HarmonicMaps.Providers.SmallEnergyRegularity
end
