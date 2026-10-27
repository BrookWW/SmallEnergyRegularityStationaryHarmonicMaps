module

public import HarmonicMaps.Energy

/-! # Squared critical Morrey energy on all truncated balls -/

@[expose] public section

open HarmonicMaps MeasureTheory Set
open scoped ENNReal

namespace StationaryHarmonicMaps

/-- The squared critical Morrey quantity uses the actual HS energy and all positive radii. -/
noncomputable def criticalGradientMorreySquare {n q : ℕ}
    (Du : Domain n → Gradient n q) (D : Set (Domain n)) : ℝ≥0∞ :=
  ⨆ x : D, ⨆ r : PositiveRadius,
    ENNReal.ofReal (r.val ^ (2 - (n : ℤ))) *
      dirichletEnergy Du (Metric.ball x.val r.val ∩ D)

end StationaryHarmonicMaps

end
