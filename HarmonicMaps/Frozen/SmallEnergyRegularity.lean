module

public import HarmonicMaps
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import HarmonicMaps.Providers.SmallEnergyRegularity

/-! # SmallEnergyRegularity

Small normalized energy yields a unique target-valued Hölder representative
on the concentric half-ball, with a quantitative scale-invariant estimate.
-/

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace HarmonicMaps

theorem smallEnergyRegularity
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
              v = w :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact HarmonicMaps.Providers.SmallEnergyRegularity.result hn N
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HarmonicMaps

end
-- FROZEN_ANCHOR_SUFFIX_END
