-- FROZEN_ANCHOR_PREFIX_BEGIN
module
public import HolderToCK
public import Mathlib.Analysis.InnerProductSpace.Laplacian

import HolderToCK.Providers.HolderQuadraticPoissonSmooth

public section
open HarmonicMaps MeasureTheory Set
open scoped NNReal ENNReal ContDiff
namespace HolderToCK

theorem holderQuadraticPoisson_smooth
    (n q : ℕ) (hn : 2 ≤ n) (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (A : Ambient q → Ambient q →L[ℝ] Ambient q →L[ℝ] Ambient q)
    (hA : ContDiff ℝ ∞ A) (hu : MemW12Loc Ω u Du)
    (hHolder : LocallyHolderOn Ω u)
    (hEquation : WeakPoissonOn Ω Du
      (fun x => ∑ i : Fin n, A (u x) (Du x i) (Du x i))) :
    ContDiffOn ℝ ∞ u Ω.val :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact HolderToCK.Providers.HolderQuadraticPoissonSmooth.result n q hn Ω u Du A hA hu hHolder hEquation
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN
end HolderToCK
end
-- FROZEN_ANCHOR_SUFFIX_END
