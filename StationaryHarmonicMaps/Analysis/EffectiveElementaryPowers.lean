module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

/-! Elementary real-power bounds with rational majorants. -/

public section
namespace StationaryHarmonicMaps.Analysis

theorem rpow_le_one_add_self_of_unit_exponent (x s : ℝ) (hx : 0≤x)
    (hs : 0≤s) (hsOne : s≤1) : x^s≤1+x := by
  by_cases hxOne : x≤1
  · exact (Real.rpow_le_one hx hxOne hs).trans (by linarith only [hx])
  · exact (Real.rpow_le_self_of_one_le (not_le.mp hxOne).le hsOne).trans (by linarith only [hx])

end StationaryHarmonicMaps.Analysis
end
