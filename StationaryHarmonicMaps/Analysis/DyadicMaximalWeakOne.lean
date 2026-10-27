module

public import StationaryHarmonicMaps.Analysis.DyadicMaximalWeakType

/-!
# Actual full integer-scale maximal weak L1 bound

The increasing two-sided finite windows recover the literal full maximal
function. Their strict superlevels form an increasing union. Continuity
from below transfers the genuine uniform finite-window Vitali estimate
to all integer scales, including arbitrarily small radii.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Every actual extended density has the full integer-scale weak-(1,1) estimate supplied by the original finite-window producers. -/
theorem dyadicBallMaximal_weak_one {n : ℕ} (f : Domain n → ℝ≥0∞)
    (L : ℝ) (hL : 0<L) :
    volume {x | ENNReal.ofReal L<dyadicBallMaximal f x}≤
      ENNReal.ofReal ((5 : ℝ)^n/L)*(∫⁻ y,f y) := by
  have hSet : {x | ENNReal.ofReal L<dyadicBallMaximal f x}=
      ⋃ N : ℕ,{x | ENNReal.ofReal L<dyadicBallMaximalWindow f N x} := by
    ext x
    simp only [mem_setOf_eq,mem_iUnion]
    rw [← iSup_dyadicBallMaximalWindow f x]
    exact lt_iSup_iff
  have hMono : Monotone (fun N : ℕ=>{x | ENNReal.ofReal L<dyadicBallMaximalWindow f N x}) := by
    intro N M hNM x hx
    exact hx.trans_le (dyadicBallMaximalWindow_monotone f x hNM)
  rw [hSet,hMono.measure_iUnion]
  exact iSup_le fun N=>dyadicBallMaximalWindow_weak_one f N L hL

end StationaryHarmonicMaps.Analysis

end
