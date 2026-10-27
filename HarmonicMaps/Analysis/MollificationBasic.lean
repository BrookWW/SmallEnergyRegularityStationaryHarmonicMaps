module

public import HarmonicMaps.Analysis.FixedMollifierKernel
public import HarmonicMaps.Energy

/-!
# Literal auxiliaries for interior mollification

The source kernel is rescaled only by a strictly positive radius. Zero
extension is an explicit auxiliary of the unit-ball restriction; it does
not change the original map or assert global Sobolev membership.
-/

@[expose] public section

namespace HarmonicMaps

noncomputable section

/-- The source rescaling `phi_h(z) = h^{-n} phi(h^{-1} z)` at positive radius. -/
def scaledMollifierKernel (n : ℕ) (h : PositiveRadius) (z : Domain n) : ℝ :=
  (h.val ^ n)⁻¹ * fixedMollifierKernel n (h.val⁻¹ • z)

/-- The explicit zero extension of the restriction of the input map to B1. -/
def unitBallZeroExtension {n q : ℕ} (u : Domain n → Ambient q) : Domain n → Ambient q :=
  (Metric.ball (0 : Domain n) 1).indicator u

end
end HarmonicMaps
