module

public import HarmonicMaps.Analysis.SphereSurfaceScaling
public import HarmonicMaps.Analysis.SphereSurfaceLocalComparison
public import HarmonicMaps.Analysis.SphereSurfaceLocalBounds

/-!
# Canonical polar measure and normalized Euclidean sphere area

Arbitrarily sharp local central-chart comparisons identify the canonical polar
measure with normalized Euclidean Hausdorff measure on the unit sphere. Exact
Hausdorff scaling then gives the identification at every positive radius.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace HarmonicMaps

private theorem sphereSurface_coefficients_small (a b : ℕ) (C : ℝ) (hC : 1 < C) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ (1 + ε) ^ a < C ∧
      ((1 + ε) / (1 - ε)) ^ b < C := by
  have hA : ContinuousAt (fun ε : ℝ => (1 + ε) ^ a) 0 :=
    (continuous_const.add continuous_id).continuousAt.pow a
  have hB : ContinuousAt (fun ε : ℝ => ((1 + ε) / (1 - ε)) ^ b) 0 :=
    ((continuous_const.add continuous_id).continuousAt.div
      (continuous_const.sub continuous_id).continuousAt (by norm_num)).pow b
  have hAev : ∀ᶠ ε in 𝓝 (0 : ℝ), (1 + ε) ^ a < C :=
    hA (isOpen_Iio.mem_nhds (by simpa only [mem_Iio, add_zero, one_pow] using hC))
  have hBev : ∀ᶠ ε in 𝓝 (0 : ℝ), ((1 + ε) / (1 - ε)) ^ b < C :=
    hB (isOpen_Iio.mem_nhds (by simpa only [mem_Iio, add_zero, sub_zero, one_div, inv_one, one_pow] using hC))
  have hOne : ∀ᶠ ε in 𝓝 (0 : ℝ), ε < 1 := isOpen_Iio.mem_nhds (mem_Iio.mpr zero_lt_one)
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 < ε ∧ ε < 1 ∧ (1 + ε) ^ a < C ∧ ((1 + ε) / (1 - ε)) ^ b < C := by
    filter_upwards [self_mem_nhdsWithin, hOne.filter_mono nhdsWithin_le_nhds,
      hAev.filter_mono nhdsWithin_le_nhds, hBev.filter_mono nhdsWithin_le_nhds] with ε hε h1 h2 h3
    exact ⟨hε, h1, h2, h3⟩
  exact hev.exists

/-- The canonical cone-induced unit-sphere measure is precisely normalized
Euclidean Hausdorff area, as complete measures on the ambient Euclidean space. -/
theorem poisson_unitPolar_eq_euclideanSphereArea {n : ℕ} (hn : 0 < n) :
    Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => θ.val)
        (volume : Measure (Domain n)).toSphere =
      (Measure.euclideanHausdorffMeasure (n - 1) : Measure (Domain n)).restrict
        (Metric.sphere (0 : Domain n) 1) := by
  have hunit :
      (Measure.euclideanHausdorffMeasure (n - 1) :
        Measure (Metric.sphere (0 : Domain n) 1)) =
      (volume : Measure (Domain n)).toSphere := by
    apply measure_eq_of_locally_arbitrarily_sharp_comparison
    intro C hC e
    obtain ⟨ε, hε, hε1, hA, hB⟩ := sphereSurface_coefficients_small (n - 1 + n) (n - 1) C hC
    obtain ⟨U, hU, he, hμ, hν⟩ := sphereSurface_local_comparison hn e ε hε hε1
    refine ⟨U, hU, he, hμ.trans ?_, hν.trans ?_⟩
    · apply Measure.le_iff'.mpr
      intro s
      simp only [Measure.smul_apply, smul_eq_mul]
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hA.le) _
    · apply Measure.le_iff'.mpr
      intro s
      simp only [Measure.smul_apply, smul_eq_mul]
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hB.le) _
  rw [← hunit]
  simpa only [Subtype.range_coe] using
    (Isometry.map_euclideanHausdorffMeasure (d := n - 1)
      (isometry_subtype_coe : Isometry (fun θ : Metric.sphere (0 : Domain n) 1 => θ.val)))

/-- The canonical radius-weighted polar measure equals the normalized
Euclidean surface measure on every positive-radius source sphere. -/
theorem poisson_scaledPolar_eq_euclideanSphereArea {n : ℕ} (hn : 2 ≤ n)
    (R : PositiveRadius) :
    Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
        (ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere) =
      (Measure.euclideanHausdorffMeasure (n - 1) : Measure (Domain n)).restrict
        (Metric.sphere (0 : Domain n) R.val) :=
  sphereSurface_scaledPolar_eq_of_unit R
    (poisson_unitPolar_eq_euclideanSphereArea (by omega))

end HarmonicMaps
end
