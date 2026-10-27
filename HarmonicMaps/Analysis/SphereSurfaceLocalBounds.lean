module

public import HarmonicMaps.Analysis.SphereSurfaceConeBounds
public import HarmonicMaps.Analysis.SphereSurfaceChartTopology
public import HarmonicMaps.Analysis.EuclideanHausdorffLipschitz

/-!
# Local comparison of canonical and Euclidean sphere measures

Every unit-sphere point has actual central coordinates in which the canonical
cone measure and normalized Hausdorff area admit mutual bounds approaching
one. The bounds hold for all measurable subsets and hence for restricted
measures, including sets of infinite measure.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace HarmonicMaps

/-- Actual central charts give arbitrarily sharp restricted-measure bounds
between canonical sphere measure and normalized Euclidean surface area. -/
theorem sphereSurface_local_comparison {n : ℕ} (hn : 0 < n)
    (e : Metric.sphere (0 : Domain n) 1) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ U : Set (Metric.sphere (0 : Domain n) 1), IsOpen U ∧ e ∈ U ∧
      (Measure.euclideanHausdorffMeasure (n - 1) : Measure (Metric.sphere (0 : Domain n) 1)).restrict U ≤
        ENNReal.ofReal ((1 + ε) ^ (n - 1 + n)) •
          ((volume : Measure (Domain n)).toSphere.restrict U) ∧
      ((volume : Measure (Domain n)).toSphere.restrict U) ≤
        ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ (n - 1)) •
          (Measure.euclideanHausdorffMeasure (n - 1) : Measure (Metric.sphere (0 : Domain n) 1)).restrict U := by
  have he : ‖e.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using e.property
  let H := (ℝ ∙ e.val)ᗮ
  let ψ : H → Domain n := fun u => ‖e.val + (u : Domain n)‖⁻¹ • (e.val + u)
  let φ : H → Metric.sphere (0 : Domain n) 1 := fun u =>
    ⟨ψ u, by simpa only [Metric.mem_sphere, dist_zero_right] using
      (sphereSurface_chart_geometry e.val he u).2.1⟩
  have hφ : Continuous φ :=
    (sphereSurface_chart_continuous e.val he).subtype_mk _
  let U : Set (Metric.sphere (0 : Domain n) 1) :=
    {θ | 0 < inner ℝ e.val θ.val ∧ ‖(inner ℝ e.val θ.val)⁻¹ • θ.val - e.val‖ < ε}
  obtain ⟨hU, heU, hCover, _⟩ := sphereSurface_chart_neighborhood e.val he ε hε
  have hdim : Module.finrank ℝ H = n - 1 := by
    have he0 : e.val ≠ 0 := by intro h; simp [h] at he
    have h := (ℝ ∙ e.val).finrank_add_finrank_orthogonal
    rw [finrank_span_singleton he0, finrank_euclideanSpace_fin] at h
    dsimp only [H]
    omega
  let μ : Measure (Metric.sphere (0 : Domain n) 1) := Measure.euclideanHausdorffMeasure (n - 1)
  let ν : Measure (Metric.sphere (0 : Domain n) 1) := (volume : Measure (Domain n)).toSphere
  have hpos : 0 < 1 + ε := by linarith only [hε]
  have hK : 0 ≤ (1 + ε) / (1 - ε) := div_nonneg hpos.le (sub_pos.mpr hε1).le
  have hsets (A : Set (Metric.sphere (0 : Domain n) 1)) (hA : MeasurableSet A) (hAU : A ⊆ U) :
      μ A ≤ ENNReal.ofReal ((1 + ε) ^ (n - 1 + n)) * ν A ∧
      ν A ≤ ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ (n - 1)) * μ A := by
    let S : Set H := φ ⁻¹' A
    have hS : MeasurableSet S := hA.preimage hφ.measurable
    have hSbound (u : H) (hu : u ∈ S) : ‖u‖ ≤ ε := by
      have h := (hAU hu).2
      change ‖(inner ℝ e.val (ψ u))⁻¹ • ψ u - e.val‖ < ε at h
      rw [(sphereSurface_chart_geometry e.val he u).2.2.2] at h
      exact h.le
    have hSb : S ⊆ Metric.closedBall (0 : H) ε := by
      intro u hu
      simpa only [Metric.mem_closedBall, dist_zero_right] using hSbound u hu
    have hImage : Subtype.val '' A = ψ '' S := by
      ext x
      constructor
      · rintro ⟨θ, hθ, rfl⟩
        obtain ⟨u, _, hu⟩ := hCover θ (hAU hθ)
        refine ⟨u, ?_, hu⟩
        have hφeq : φ u = θ := Subtype.ext hu
        change φ u ∈ A
        rwa [hφeq]
      · rintro ⟨u, hu, rfl⟩
        exact ⟨φ u, hu, rfl⟩
    have hArea : μ A =
        (Measure.euclideanHausdorffMeasure (n - 1) : Measure (Domain n)) (ψ '' S) := by
      rw [← hImage, isometry_subtype_coe.euclideanHausdorffMeasure_image]
    obtain ⟨hνlower, hνupper⟩ := sphereSurface_canonical_chart_bounds hn e.val he ε hε.le
      S hS hSbound A hA hImage
    obtain ⟨hLip, hAnti⟩ := sphereSurface_chart_lipschitz e.val he ε hε.le hε1
    have hμupper : μ A ≤ ENNReal.ofReal ((1 + ε) ^ (n - 1)) * (volume : Measure H) S := by
      have h := euclideanHausdorff_lipschitzOn_image_le_volume hLip hSb
      rw [hdim, ← hArea] at h
      change μ A ≤ (ENNReal.ofReal (1 + ε)) ^ (n - 1) * (volume : Measure H) S at h
      simpa only [← ENNReal.ofReal_pow hpos.le] using h
    have hμlower : (volume : Measure H) S ≤
        ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ (n - 1)) * μ A := by
      have h := volume_le_euclideanHausdorff_image_of_antilipschitzOn
        (f := ψ) (patch := Metric.closedBall (0 : H) ε) (S := S)
        (K := Real.toNNReal ((1 + ε) / (1 - ε))) hAnti hSb
      rw [hdim, ← hArea] at h
      change (volume : Measure H) S ≤
        (ENNReal.ofReal ((1 + ε) / (1 - ε))) ^ (n - 1) * μ A at h
      simpa only [← ENNReal.ofReal_pow hK] using h
    have hCancel : ENNReal.ofReal ((1 + ε) ^ n) *
        ENNReal.ofReal (((1 + ε)⁻¹) ^ n) = 1 := by
      rw [← ENNReal.ofReal_mul (pow_nonneg hpos.le n), ← mul_pow,
        mul_inv_cancel₀ hpos.ne', one_pow, ENNReal.ofReal_one]
    have hV : (volume : Measure H) S ≤ ENNReal.ofReal ((1 + ε) ^ n) * ν A := by
      have h := mul_le_mul_right hνlower (ENNReal.ofReal ((1 + ε) ^ n))
      simpa only [← mul_assoc, hCancel, one_mul] using h
    constructor
    · calc
        μ A ≤ ENNReal.ofReal ((1 + ε) ^ (n - 1)) * (volume : Measure H) S := hμupper
        _ ≤ ENNReal.ofReal ((1 + ε) ^ (n - 1)) * (ENNReal.ofReal ((1 + ε) ^ n) * ν A) :=
          mul_le_mul_right hV _
        _ = ENNReal.ofReal ((1 + ε) ^ (n - 1 + n)) * ν A := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hpos.le _), ← pow_add]
    · exact hνupper.trans hμlower
  refine ⟨U, hU, heU, ?_, ?_⟩
  · apply Measure.le_iff.mpr
    intro A hA
    rw [Measure.restrict_apply hA, Measure.smul_apply, Measure.restrict_apply hA]
    exact (hsets (A ∩ U) (hA.inter hU.measurableSet) inter_subset_right).1
  · apply Measure.le_iff.mpr
    intro A hA
    rw [Measure.restrict_apply hA, Measure.smul_apply, Measure.restrict_apply hA]
    exact (hsets (A ∩ U) (hA.inter hU.measurableSet) inter_subset_right).2

end HarmonicMaps
end
