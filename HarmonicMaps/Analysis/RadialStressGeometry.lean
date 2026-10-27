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

public import HarmonicMaps.Analysis.RadialVectorField
public import HarmonicMaps.Analysis.RadialStressAlgebra

/-!
# Radial stress identities with the displayed gradient

The coordinate differential of the actual radial vector field contracts with
an arbitrary field of gradient columns. Combining its divergence and its
double contraction gives the pointwise integrand used in the radial
stationarity calculation. No stationarity or integral conclusion is assumed.

Source: `LeanStationaryHarmonicMaps/StationaryHarmonicMap/RadialGeometry.lean`
at upstream commit `bde641f98085e5a0443c10779a6fe519190b6adc`.
-/

public section

open Set
open scoped BigOperators ContDiff

namespace HarmonicMaps

/-- The actual radial-field derivative contracts with the same displayed
gradient field. This is pointwise algebra, and does not require stationarity. -/
theorem weakRadialStressContractionFormula {n q : ℕ}
    (Du : Domain n → Gradient n q) {eta : ℝ → ℝ} {x : Domain n}
    (heta : DifferentiableAt ℝ eta ‖x‖) (hx : x ≠ 0) :
    (∑ i : Fin n, ∑ j : Fin n,
      inner ℝ (Du x i) (Du x j) *
        (fderiv ℝ (radialVectorField eta) x (EuclideanSpace.single i 1)) j) =
      eta ‖x‖ * hsNormSq (Du x) +
        ‖x‖ * deriv eta ‖x‖ * ‖gradientRadialDerivative (Du x) ⟨x, hx⟩‖ ^ 2 := by
  simp only [radialVectorField_fderiv_coord heta hx]
  exact gradientRadialStressContractionFormula (Du x) eta hx

/-- The pointwise stress integrand after radial substitution, with no half
factor in its HS energy. -/
theorem radialStressEnergyIdentity {n q : ℕ}
    (Du : Domain n → Gradient n q) {eta : ℝ → ℝ} {x : Domain n}
    (heta : DifferentiableAt ℝ eta ‖x‖) (hx : x ≠ 0) :
    hsNormSq (Du x) *
      (∑ i : Fin n, (fderiv ℝ (radialVectorField eta) x (EuclideanSpace.single i 1)) i) -
      2 * (∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (Du x i) (Du x j) *
          (fderiv ℝ (radialVectorField eta) x (EuclideanSpace.single i 1)) j) =
      (((n : ℝ) - 2) * eta ‖x‖ + ‖x‖ * deriv eta ‖x‖) * hsNormSq (Du x) -
        2 * ‖x‖ * deriv eta ‖x‖ *
          ‖gradientRadialDerivative (Du x) ⟨x, hx⟩‖ ^ 2 := by
  rw [radialVectorField_divergence heta hx, weakRadialStressContractionFormula Du heta hx]
  ring

/-- The stress contraction at the origin uses the true plateau differential,
and needs no chosen radial direction there. -/
theorem weakRadialStressContractionFormula_zero {n q : ℕ}
    (Du : Domain n → Gradient n q) {eta : ℝ → ℝ}
    (hplateau : ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ t ∈ Ico (0 : ℝ) epsilon, eta t = eta 0) :
    (∑ i : Fin n, ∑ j : Fin n,
      inner ℝ (Du 0 i) (Du 0 j) *
        (fderiv ℝ (radialVectorField eta) 0 (EuclideanSpace.single i 1)) j) =
      eta 0 * hsNormSq (Du 0) := by
  rw [(radialVectorField_hasFDerivAt_zero hplateau).fderiv]
  simp only [smul_apply, ContinuousLinearMap.id_apply,
    PiLp.smul_apply, smul_eq_mul]
  have hdiag (i : Fin n) :
      (∑ j : Fin n, inner ℝ (Du 0 i) (Du 0 j) *
        (eta 0 * (EuclideanSpace.single i (1 : ℝ)) j)) = eta 0 * ‖Du 0 i‖ ^ 2 := by
    rw [Finset.sum_eq_single i]
    · simp only [PiLp.single_apply, ite_true, mul_one, real_inner_self_eq_norm_sq]
      ring
    · intro j _ hji
      simp only [PiLp.single_apply, if_neg hji, mul_zero]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  simp only [hdiag, hsNormSq, Finset.mul_sum]

/-- At the origin the radial stress integrand is `(n-2) eta(0) |Du(0)|²`. -/
theorem radialStressEnergyIdentity_zero {n q : ℕ}
    (Du : Domain n → Gradient n q) {eta : ℝ → ℝ}
    (hplateau : ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ t ∈ Ico (0 : ℝ) epsilon, eta t = eta 0) :
    hsNormSq (Du 0) *
      (∑ i : Fin n, (fderiv ℝ (radialVectorField eta) 0 (EuclideanSpace.single i 1)) i) -
      2 * (∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (Du 0 i) (Du 0 j) *
          (fderiv ℝ (radialVectorField eta) 0 (EuclideanSpace.single i 1)) j) =
      ((n : ℝ) - 2) * eta 0 * hsNormSq (Du 0) := by
  rw [weakRadialStressContractionFormula_zero Du hplateau,
    (radialVectorField_hasFDerivAt_zero hplateau).fderiv]
  simp only [smul_apply, ContinuousLinearMap.id_apply,
    PiLp.smul_apply, smul_eq_mul, PiLp.single_apply, ite_true, mul_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Source smooth profiles yield the global field smoothness and the two
actual nonzero-point radial identities, together with the plateau value at
the origin. Compact support and stationarity are separate obligations. -/
theorem radialStressGeometry {n q : ℕ} (Du : Domain n → Gradient n q)
    {eta : ℝ → ℝ} (hs : ContDiff ℝ ∞ eta)
    (hplateau : ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ t ∈ Ico (0 : ℝ) epsilon, eta t = eta 0) :
    ContDiff ℝ ∞ (radialVectorField (n := n) eta) ∧
    (∀ x : Domain n, ∀ hx : x ≠ 0,
      (∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (Du x i) (Du x j) *
          (fderiv ℝ (radialVectorField eta) x (EuclideanSpace.single i 1)) j) =
        eta ‖x‖ * hsNormSq (Du x) + ‖x‖ * deriv eta ‖x‖ *
          ‖gradientRadialDerivative (Du x) ⟨x, hx⟩‖ ^ 2) ∧
    (∀ x : Domain n, ∀ hx : x ≠ 0,
      hsNormSq (Du x) *
        (∑ i : Fin n, (fderiv ℝ (radialVectorField eta) x (EuclideanSpace.single i 1)) i) -
        2 * (∑ i : Fin n, ∑ j : Fin n,
          inner ℝ (Du x i) (Du x j) *
            (fderiv ℝ (radialVectorField eta) x (EuclideanSpace.single i 1)) j) =
        (((n : ℝ) - 2) * eta ‖x‖ + ‖x‖ * deriv eta ‖x‖) * hsNormSq (Du x) -
          2 * ‖x‖ * deriv eta ‖x‖ *
            ‖gradientRadialDerivative (Du x) ⟨x, hx⟩‖ ^ 2) ∧
    (hsNormSq (Du 0) *
      (∑ i : Fin n, (fderiv ℝ (radialVectorField eta) 0 (EuclideanSpace.single i 1)) i) -
      2 * (∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (Du 0 i) (Du 0 j) *
          (fderiv ℝ (radialVectorField eta) 0 (EuclideanSpace.single i 1)) j) =
      ((n : ℝ) - 2) * eta 0 * hsNormSq (Du 0)) := by
  have hd : Differentiable ℝ eta := hs.differentiable (by norm_num)
  exact ⟨radialVectorField_contDiff hs hplateau,
    (fun x hx => weakRadialStressContractionFormula Du (hd ‖x‖) hx),
    (fun x hx => radialStressEnergyIdentity Du (hd ‖x‖) hx),
    radialStressEnergyIdentity_zero Du hplateau⟩

end HarmonicMaps
