-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import StationaryHarmonicMaps.Providers.SmallEnergySmoothRegularity

/-! # Small-energy smoothness for actual smooth targets -/

public section
open HarmonicMaps MeasureTheory Set Metric
open scoped ContDiff
namespace StationaryHarmonicMaps

theorem stationary_small_energy_smooth_regularity {n q : ℕ} (hn : 2≤n)
    (N : CompactSmoothEmbeddedTarget q) :
    ∃ε α C : ℝ,0<ε ∧ 0<α ∧ α<1 ∧ 0≤C ∧
      ∀(Ω : OpenDomain n) (u : Domain n→Ambient q) (Du : Domain n→Gradient n q),
        MemW12Loc Ω u Du →
        (∀ᵐx∂volume.restrict Ω.val,u x∈N.carrierSet) →
        IsWeaklyHarmonicByTangentVariations (SmoothTarget.toC2 N) Ω u Du →
        IsDomainStationary Ω Du →
        ∀(a : Domain n) (R : PositiveRadius),closedBall a R.val⊆Ω.val →
          normalizedEnergy Du a R≤ENNReal.ofReal ε →
          ∃w : Domain n→Ambient q,
            ContDiffOn ℝ ∞ w (ball a (R.val/2)) ∧
            IsContinuousRepresentative (ballDomain a (R.val/2)) u (fun x=>w x.val) ∧
            (∀x∈ball a (R.val/2),w x∈N.carrierSet) ∧
            (∀x∈ball a (R.val/2),∀y∈ball a (R.val/2),
              ‖w x-w y‖≤C*R.val^(-α)*Real.sqrt (normalizedEnergy Du a R).toReal*(dist x y)^α) ∧
            ∀v : ball a (R.val/2)→Ambient q,
              IsContinuousRepresentative (ballDomain a (R.val/2)) u v →
              v=(fun x=>w x.val) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact StationaryHarmonicMaps.Providers.smallEnergySmoothRegularity hn N
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end StationaryHarmonicMaps
end
-- FROZEN_ANCHOR_SUFFIX_END
