-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import StationaryHarmonicMaps.Providers.VariationalWeakPoissonEquivalence

/-! # The complete variational and PDE equivalence for an actual C² target -/

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff

namespace StationaryHarmonicMaps.CompactC2EmbeddedTarget

theorem variational_weakPoisson_equivalence :
    ∀ {q : ℕ} (N : CompactC2EmbeddedTarget q),
    ∃ (G : Ambient q → Ambient q →L[ℝ] Ambient q) (L : ℝ),
      ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
      (∀ p : N.Carrier, G p.val = N.normalProjection p) ∧ 0 ≤ L ∧
      (∀ y : Ambient q, ‖fderiv ℝ G y‖ ≤ L) ∧
      ∀ {n : ℕ} {Ω : OpenDomain n} {u : Domain n → Ambient q}
        {Du : Domain n → Gradient n q}, MemW12Loc Ω u Du →
        (∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet) →
        (IsWeaklyHarmonicByTangentVariations N Ω u Du ↔
          HolderToCK.WeakPoissonOn Ω Du (fun x => -(∑ i : Fin n,
            fderiv ℝ G (u x) (Du x i) (Du x i)))) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact StationaryHarmonicMaps.Providers.variationalWeakPoissonEquivalence
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end StationaryHarmonicMaps.CompactC2EmbeddedTarget

end
-- FROZEN_ANCHOR_SUFFIX_END
