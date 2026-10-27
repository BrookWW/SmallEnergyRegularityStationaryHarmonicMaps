module

public import HarmonicMaps
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import HarmonicMaps.Providers.OneStepEnergyDecay

/-! # OneStepEnergyDecay

Small unit-ball energy yields a coefficient-one-half bound for the
normalized Dirichlet energy at a uniformly chosen smaller radius.
-/

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace HarmonicMaps

theorem oneStepEnergyDecay
    {n q : ℕ} (hn : 2 ≤ n) (N : CompactSmoothEmbeddedTarget q) :
    ∃ ε : ℝ, ∃ τ : PositiveRadius,
      0 < ε ∧ τ.val < (1 / 8 : ℝ) ∧
      ∀ (u : Domain n → Ambient q) (Du : Domain n → Gradient n q),
        MemW12Loc (ballDomain (0 : Domain n) 1) u Du →
        TakesValuesIn N (ballDomain (0 : Domain n) 1) u →
        IsLocallyEnergyMinimizing N (ballDomain (0 : Domain n) 1) u Du →
        dirichletEnergy Du (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal ε →
        normalizedEnergy Du (0 : Domain n) τ ≤
          (1 / 2 : ℝ≥0∞) * dirichletEnergy Du (Metric.ball (0 : Domain n) 1) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact HarmonicMaps.Providers.OneStepEnergyDecay.result hn N
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HarmonicMaps

end
-- FROZEN_ANCHOR_SUFFIX_END
