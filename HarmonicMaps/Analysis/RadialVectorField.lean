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

public import HarmonicMaps.Analysis.RadialStressBasic
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Derivatives of the radial test vector field

The radial derivative formula is certified away from the origin by a local
differentiability hypothesis on the radius profile. A profile constant for
small nonnegative radii gives a smooth field at the origin.

Source: `LeanStationaryHarmonicMaps/StationaryHarmonicMap/RadialGeometry.lean`
at upstream commit `bde641f98085e5a0443c10779a6fe519190b6adc`.
-/

public section

open Filter Set
open scoped Topology BigOperators ContDiff

namespace HarmonicMaps

noncomputable section

/-- The differential of the Euclidean norm away from the origin. -/
theorem radialNorm_fderiv_apply {n : ℕ} {x v : Domain n} (hx : x ≠ 0) :
    fderiv ℝ (fun y : Domain n => ‖y‖) x v = inner ℝ x v / ‖x‖ := by
  have hnorm : DifferentiableAt ℝ (fun y : Domain n => ‖y‖) x :=
    (contDiffAt_norm (𝕜 := ℝ) (n := 1) hx).differentiableAt one_ne_zero
  have hsq_left :
      fderiv ℝ (fun y : Domain n => ‖y‖ ^ 2) x v = 2 * inner ℝ x v := by
    rw [fderiv_norm_sq_apply]
    simp only [two_smul, add_apply, innerSL_apply_apply, two_mul]
  have hsq_chain :
      fderiv ℝ (fun y : Domain n => ‖y‖ ^ 2) x v =
        2 * ‖x‖ * fderiv ℝ (fun y : Domain n => ‖y‖) x v := by
    rw [show (fun y : Domain n => ‖y‖ ^ 2) =
      (fun t : ℝ => t ^ 2) ∘ (fun y : Domain n => ‖y‖) by rfl]
    rw [fderiv_comp x (by fun_prop) hnorm]
    simp only [differentiableAt_fun_id, fderiv_fun_pow, Nat.add_one_sub_one, pow_one,
      nsmul_eq_mul, Nat.cast_ofNat, fderiv_fun_id, ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.id_comp, smul_apply, smul_eq_mul]
  have hnorm_ne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hmain :
      ‖x‖ * fderiv ℝ (fun y : Domain n => ‖y‖) x v = inner ℝ x v := by
    nlinarith only [hsq_left, hsq_chain]
  rw [eq_div_iff hnorm_ne]
  simpa only [mul_comm] using hmain

/-- A Fréchet derivative certificate for the norm at a nonzero point. -/
theorem radialNorm_hasFDerivAt {n : ℕ} {x : Domain n} (hx : x ≠ 0) :
    HasFDerivAt (fun y : Domain n => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hnorm : DifferentiableAt ℝ (fun y : Domain n => ‖y‖) x :=
    (contDiffAt_norm (𝕜 := ℝ) (n := 1) hx).differentiableAt one_ne_zero
  have hmap : fderiv ℝ (fun y : Domain n => ‖y‖) x = ‖x‖⁻¹ • innerSL ℝ x := by
    ext v
    rw [radialNorm_fderiv_apply hx]
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul,
      div_eq_mul_inv, mul_comm]
  rw [← hmap]
  exact hnorm.hasFDerivAt

/-- The chain rule for a differentiable radius profile away from the origin. -/
theorem radialProfile_hasFDerivAt {n : ℕ} {eta : ℝ → ℝ} {x : Domain n}
    (heta : DifferentiableAt ℝ eta ‖x‖) (hx : x ≠ 0) :
    HasFDerivAt (fun y : Domain n => eta ‖y‖)
      ((deriv eta ‖x‖ / ‖x‖) • innerSL ℝ x) x := by
  convert! heta.hasDerivAt.comp_hasFDerivAt x (radialNorm_hasFDerivAt hx) using 1
  simp only [smul_smul, div_eq_mul_inv]

/-- Evaluation of the chain-rule differential of the radius profile. -/
theorem radialProfile_fderiv_apply {n : ℕ} {eta : ℝ → ℝ} {x v : Domain n}
    (heta : DifferentiableAt ℝ eta ‖x‖) (hx : x ≠ 0) :
    fderiv ℝ (fun y : Domain n => eta ‖y‖) x v =
      deriv eta ‖x‖ * (inner ℝ x v / ‖x‖) := by
  rw [(radialProfile_hasFDerivAt heta hx).fderiv]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
  ring

/-- The actual differential of `x ↦ eta ‖x‖ • x` at a nonzero point. -/
theorem radialVectorField_hasFDerivAt {n : ℕ} {eta : ℝ → ℝ} {x : Domain n}
    (heta : DifferentiableAt ℝ eta ‖x‖) (hx : x ≠ 0) :
    HasFDerivAt (radialVectorField eta)
      (eta ‖x‖ • ContinuousLinearMap.id ℝ (Domain n) +
        ((deriv eta ‖x‖ / ‖x‖) • innerSL ℝ x).smulRight x) x := by
  exact (radialProfile_hasFDerivAt heta hx).smul (hasFDerivAt_id x)

/-- The differential applied to an arbitrary tangent vector. -/
theorem radialVectorField_fderiv_apply {n : ℕ} {eta : ℝ → ℝ} {x v : Domain n}
    (heta : DifferentiableAt ℝ eta ‖x‖) (hx : x ≠ 0) :
    fderiv ℝ (radialVectorField eta) x v =
      eta ‖x‖ • v + (deriv eta ‖x‖ * (inner ℝ x v / ‖x‖)) • x := by
  rw [(radialVectorField_hasFDerivAt heta hx).fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    smul_eq_mul]
  congr 1
  congr 1
  ring

/-- The coordinate formula `∂ᵢ Xⱼ = eta(r) δᵢⱼ + eta'(r) xᵢ xⱼ / r`. -/
theorem radialVectorField_fderiv_coord {n : ℕ} {eta : ℝ → ℝ} {x : Domain n}
    (heta : DifferentiableAt ℝ eta ‖x‖) (hx : x ≠ 0) (i j : Fin n) :
    (fderiv ℝ (radialVectorField eta) x (EuclideanSpace.single i 1)) j =
      eta ‖x‖ * (EuclideanSpace.single i (1 : ℝ)) j +
        deriv eta ‖x‖ * (x i * x j / ‖x‖) := by
  rw [radialVectorField_fderiv_apply heta hx]
  simp only [EuclideanSpace.inner_single_right, one_mul, conj_trivial,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- The trace of the actual differential is `n eta(r) + r eta'(r)`. -/
theorem radialVectorField_divergence {n : ℕ} {eta : ℝ → ℝ} {x : Domain n}
    (heta : DifferentiableAt ℝ eta ‖x‖) (hx : x ≠ 0) :
    (∑ i : Fin n, (fderiv ℝ (radialVectorField eta) x (EuclideanSpace.single i 1)) i) =
      (n : ℝ) * eta ‖x‖ + ‖x‖ * deriv eta ‖x‖ := by
  have hsum_sq : (∑ i : Fin n, x i * x i) = ‖x‖ ^ 2 := by
    simpa only [pow_two] using (EuclideanSpace.real_norm_sq_eq x).symm
  simp only [radialVectorField_fderiv_coord heta hx,
    PiLp.single_apply, ite_true, mul_one]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_div, hsum_sq]
  have hnorm_ne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp [hnorm_ne]

private theorem radialVectorField_eventuallyEq_at_zero {n : ℕ} {eta : ℝ → ℝ}
    (hplateau : ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ t ∈ Ico (0 : ℝ) epsilon, eta t = eta 0) :
    radialVectorField (n := n) eta =ᶠ[𝓝 (0 : Domain n)] (fun x => eta 0 • x) := by
  obtain ⟨epsilon, hepsilon, hconstant⟩ := hplateau
  filter_upwards [Metric.ball_mem_nhds (0 : Domain n) hepsilon] with x hx
  have hxnorm : ‖x‖ < epsilon := by
    simpa only [Metric.mem_ball, dist_zero_right] using hx
  change eta ‖x‖ • x = eta 0 • x
  rw [hconstant ‖x‖ ⟨norm_nonneg x, hxnorm⟩]

/-- A radius profile constant near zero gives the linear differential at zero. -/
theorem radialVectorField_hasFDerivAt_zero {n : ℕ} {eta : ℝ → ℝ}
    (hplateau : ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ t ∈ Ico (0 : ℝ) epsilon, eta t = eta 0) :
    HasFDerivAt (radialVectorField (n := n) eta)
      (eta 0 • ContinuousLinearMap.id ℝ (Domain n)) 0 := by
  exact ((hasFDerivAt_id (0 : Domain n)).const_smul (eta 0)).congr_of_eventuallyEq
    (radialVectorField_eventuallyEq_at_zero hplateau)

/-- A smooth radius profile constant near zero defines a globally smooth field. -/
theorem radialVectorField_contDiff {n : ℕ} {eta : ℝ → ℝ}
    (hs : ContDiff ℝ ∞ eta)
    (hplateau : ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ t ∈ Ico (0 : ℝ) epsilon, eta t = eta 0) :
    ContDiff ℝ ∞ (radialVectorField (n := n) eta) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    exact (contDiffAt_id.const_smul (eta 0)).congr_of_eventuallyEq
      (radialVectorField_eventuallyEq_at_zero hplateau)
  · exact (hs.contDiffAt.comp x (contDiffAt_norm (𝕜 := ℝ) hx)).smul contDiffAt_id

end
end HarmonicMaps
