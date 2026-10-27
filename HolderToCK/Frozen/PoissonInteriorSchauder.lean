-- FROZEN_ANCHOR_PREFIX_BEGIN
module
public import HolderToCK
public import Mathlib.Analysis.InnerProductSpace.Laplacian

import HolderToCK.Providers.PoissonInteriorSchauder

public section
open HarmonicMaps MeasureTheory Set
open scoped NNReal ENNReal ContDiff
namespace HolderToCK

theorem poissonInteriorSchauder
    (n q : ℕ) (hn : 2 ≤ n) (γ : ℝ) (hγ : 0 < γ) (hγOne : γ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (v : Domain n → Ambient q) (Dv : Domain n → Gradient n q)
        (f : Domain n → Ambient q) (c : Ambient q) (M L H : ℝ),
        MemW12Loc (ballDomain (0 : Domain n) 1) v Dv →
        ContinuousOn v (Metric.ball (0 : Domain n) 1) →
        WeakPoissonOn (ballDomain (0 : Domain n) 1) Dv f →
        0 ≤ M → (∀ x ∈ Metric.ball (0 : Domain n) 1, ‖v x - c‖ ≤ M) →
        0 ≤ L → (∀ x ∈ Metric.ball (0 : Domain n) 1, ‖f x‖ ≤ L) →
        0 ≤ H → HolderBoundOn (Metric.ball (0 : Domain n) 1) f γ H →
        ContDiffOn ℝ 2 v (Metric.ball (0 : Domain n) (1 / 2)) ∧
        (∀ j : ℕ, j ≤ 2 → ∀ x ∈ Metric.ball (0 : Domain n) (1 / 2),
          ‖iteratedFDeriv ℝ j (fun y => v y - c) x‖ ≤ C * (M + L + H)) ∧
        HolderBoundOn (Metric.ball (0 : Domain n) (1 / 2))
          (iteratedFDeriv ℝ 2 v) γ (C * (M + L + H)) ∧
        ∀ x ∈ Metric.ball (0 : Domain n) (1 / 2), Laplacian.laplacian v x = f x :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact HolderToCK.Providers.PoissonInteriorSchauder.result n q hn γ hγ hγOne
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN
end HolderToCK
end
-- FROZEN_ANCHOR_SUFFIX_END
