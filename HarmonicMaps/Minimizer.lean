module

public import HarmonicMaps.Energy
public import HarmonicMaps.Target

/-!
# Target-valued maps and local Dirichlet minimizers

Competitors range over all finite W1,2 maps with the same W1,2_0 boundary
difference and almost-everywhere target membership. Neither stationarity nor
any regularity or decay conclusion is an input.
-/

@[expose] public section

open MeasureTheory Set

namespace HarmonicMaps

/-- The map takes values in the given embedded target almost everywhere. -/
def TakesValuesIn {n q : ℕ} (N : CompactSmoothEmbeddedTarget q)
    (Ω : OpenDomain n) (u : Domain n → Ambient q) : Prop :=
  ∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet

/-- Local energy minimization against every admissible Sobolev competitor on
each positive ball whose closure is contained in the domain. Sobolev membership
and target membership of the original map are stated separately. -/
def IsLocallyEnergyMinimizing {n q : ℕ} (N : CompactSmoothEmbeddedTarget q)
    (Ω : OpenDomain n) (u : Domain n → Ambient q)
    (Du : Domain n → Gradient n q) : Prop :=
  ∀ (a : Domain n) (r : ℝ), 0 < r → Metric.closedBall a r ⊆ Ω.val →
    ∀ (v : Domain n → Ambient q) (Dv : Domain n → Gradient n q),
      MemW12 (ballDomain a r) v Dv →
      TakesValuesIn N (ballDomain a r) v →
      HasZeroBoundaryDifference (ballDomain a r) u Du v Dv →
      dirichletEnergy Du (Metric.ball a r) ≤
        dirichletEnergy Dv (Metric.ball a r)

end HarmonicMaps

end
