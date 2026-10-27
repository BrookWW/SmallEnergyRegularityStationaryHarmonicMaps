module

public import HarmonicMaps.Sobolev

/-!
# Variable translations

The map `variableShift s y` translates a point by the scalar radius `s x`
in the direction `-y`. Its formula has its ordinary meaning on the whole
Euclidean space and requires no inverse or derivative selection.
-/

@[expose] public section

namespace HarmonicMaps

/-- The variable translation `x ↦ x - s(x)y`. -/
def variableShift {n : ℕ} (s : Domain n → ℝ) (y : Domain n) (x : Domain n) : Domain n :=
  x - s x • y

end HarmonicMaps
