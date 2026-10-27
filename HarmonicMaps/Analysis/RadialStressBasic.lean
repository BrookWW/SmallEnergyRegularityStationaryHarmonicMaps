/-
MIT License

Copyright (c) 2026 LeanStationaryHarmonicMaps contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import HarmonicMaps.Energy

/-!
# Radial field and gradient evaluation

The literal formulas use the existing Euclidean carriers and HS energy.
The radial gradient has a punctured carrier, so no direction is assigned at
the origin. Its linear-map characterization uses the standard Euclidean basis.

Source: `LeanStationaryHarmonicMaps/StationaryHarmonicMap/RadialGeometry.lean`
at upstream commit `bde641f98085e5a0443c10779a6fe519190b6adc`.
-/

@[expose] public section

open scoped BigOperators

namespace HarmonicMaps

noncomputable section

/-- The radial test vector field centered at the origin. -/
def radialVectorField {n : ℕ} (eta : ℝ → ℝ) (x : Domain n) : Domain n :=
  eta ‖x‖ • x

/-- Evaluation of the displayed gradient columns in the radial unit direction,
defined only where that direction exists. -/
def gradientRadialDerivative {n q : ℕ} (A : Gradient n q)
    (x : {x : Domain n // x ≠ 0}) : Ambient q :=
  ‖x.val‖⁻¹ • ∑ i : Fin n, x.val i • A i

/-- The radial column formula agrees with evaluation of any actual linear map. -/
theorem gradientRadialDerivative_eq_linearMap {n q : ℕ}
    (T : Domain n →L[ℝ] Ambient q) (x : {x : Domain n // x ≠ 0}) :
    gradientRadialDerivative (fun i => T (EuclideanSpace.single i 1)) x =
      T (‖x.val‖⁻¹ • x.val) := by
  have hrepr : (∑ i : Fin n, x.val i • EuclideanSpace.single i 1) = x.val := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x.val
  change ‖x.val‖⁻¹ • (∑ i : Fin n, x.val i • T (EuclideanSpace.single i 1)) = _
  rw [map_smul]
  apply congrArg (fun w : Ambient q => ‖x.val‖⁻¹ • w)
  calc
    (∑ i : Fin n, x.val i • T (EuclideanSpace.single i 1)) =
        T (∑ i : Fin n, x.val i • EuclideanSpace.single i 1) := by
      simp only [map_sum, map_smul]
    _ = T x.val := congrArg T hrepr

end
end HarmonicMaps
