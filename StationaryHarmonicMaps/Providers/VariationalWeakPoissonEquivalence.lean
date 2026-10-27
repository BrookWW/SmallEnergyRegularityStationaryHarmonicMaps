module

public import StationaryHarmonicMaps.Analysis.WeakPoissonToVariations

/-! # Equivalence of the actual variation and signed PDE formulations -/

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff

namespace StationaryHarmonicMaps.Providers

/-- One target-dependent extension realizes both directions on every open domain. -/
theorem variationalWeakPoissonEquivalence :
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
            fderiv ℝ G (u x) (Du x i) (Du x i)))) := by
  intro q N
  exact Analysis.exists_normal_extension_tangentVariations_iff N

end StationaryHarmonicMaps.Providers

end
