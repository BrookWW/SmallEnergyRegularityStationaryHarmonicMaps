module

public import HarmonicMaps.Analysis.SphereConeVolume
public import HarmonicMaps.Analysis.SphereSurfaceChart

/-!
# Canonical sphere measure in a central chart

The unit radial cone over a small central-chart image lies between two
truncated cones over the same tangent set. Their exact volumes give bounds
for the canonical angular measure with constants tending to one.
-/

public section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace HarmonicMaps

/-- Canonical angular measure and tangent volume have arbitrarily sharp
comparisons on actual central-chart images. -/
theorem sphereSurface_canonical_chart_bounds {n : ℕ} (hn : 0 < n)
    (e : Domain n) (he : ‖e‖ = 1) (ε : ℝ) (hε : 0 ≤ ε)
    (S : Set (ℝ ∙ e)ᗮ) (hS : MeasurableSet S)
    (hSbound : ∀ u ∈ S, ‖u‖ ≤ ε)
    (A : Set (Metric.sphere (0 : Domain n) 1)) (hA : MeasurableSet A)
    (hImage : Subtype.val '' A =
      (fun u : (ℝ ∙ e)ᗮ => ‖e + (u : Domain n)‖⁻¹ • (e + u)) '' S) :
    ENNReal.ofReal (((1 + ε)⁻¹) ^ n) * (volume : Measure (ℝ ∙ e)ᗮ) S ≤
        (volume : Measure (Domain n)).toSphere A ∧
      (volume : Measure (Domain n)).toSphere A ≤ (volume : Measure (ℝ ∙ e)ᗮ) S := by
  let ψ : (ℝ ∙ e)ᗮ → Domain n := fun u => ‖e + (u : Domain n)‖⁻¹ • (e + u)
  let b : ℝ := (1 + ε)⁻¹
  have hpos : 0 < 1 + ε := by linarith only [hε]
  have hb : 0 < b := inv_pos.mpr hpos
  have hNpos (u : (ℝ ∙ e)ᗮ) : 0 < ‖e + (u : Domain n)‖ :=
    lt_of_lt_of_le zero_lt_one (sphereSurface_chart_geometry e he u).1
  have hNupper (u : (ℝ ∙ e)ᗮ) (hu : u ∈ S) : ‖e + (u : Domain n)‖ ≤ 1 + ε := by
    calc
      ‖e + (u : Domain n)‖ ≤ ‖e‖ + ‖(u : Domain n)‖ := norm_add_le _ _
      _ ≤ 1 + ε := by rw [he]; have h := hSbound u hu; change ‖(u : Domain n)‖ ≤ ε at h; linarith
  have hLower : Ioo (0 : ℝ) b • ((fun u : (ℝ ∙ e)ᗮ => e + u.val) '' S) ⊆
      Ioo (0 : ℝ) 1 • (ψ '' S) := by
    rintro x ⟨t, ht, _, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨t * ‖e + (u : Domain n)‖, ⟨mul_pos ht.1 (hNpos u), ?_⟩,
      ψ u, ⟨u, hu, rfl⟩, ?_⟩
    · have htbound : t * (1 + ε) < 1 := by
        have h := mul_lt_mul_of_pos_right ht.2 hpos
        simpa only [b, inv_mul_cancel₀ hpos.ne'] using h
      exact (mul_le_mul_of_nonneg_left (hNupper u hu) ht.1.le).trans_lt htbound
    · dsimp only [ψ]
      rw [smul_smul, mul_assoc, mul_inv_cancel₀ (hNpos u).ne', mul_one]
  have hUpper : Ioo (0 : ℝ) 1 • (ψ '' S) ⊆
      Ioo (0 : ℝ) 1 • ((fun u : (ℝ ∙ e)ᗮ => e + u.val) '' S) := by
    rintro x ⟨r, hr, _, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨r * ‖e + (u : Domain n)‖⁻¹, ⟨mul_pos hr.1 (inv_pos.mpr (hNpos u)), ?_⟩,
      e + u.val, ⟨u, hu, rfl⟩, ?_⟩
    · have hi : ‖e + (u : Domain n)‖⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ (sphereSurface_chart_geometry e he u).1
      exact (mul_le_mul_of_nonneg_left hi hr.1.le).trans_lt (by simpa only [mul_one] using hr.2)
    · dsimp only [ψ]
      rw [smul_smul]
  have hnR : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have hnormalize (t : ℝ) :
      (n : ℝ≥0∞) * (ENNReal.ofReal (t ^ n / (n : ℝ)) * (volume : Measure (ℝ ∙ e)ᗮ) S) =
        ENNReal.ofReal (t ^ n) * (volume : Measure (ℝ ∙ e)ᗮ) S := by
    rw [← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
    congr 2
    field_simp
  rw [(volume : Measure (Domain n)).toSphere_apply' hA, finrank_euclideanSpace_fin,
    hImage]
  change ENNReal.ofReal (b ^ n) * (volume : Measure (ℝ ∙ e)ᗮ) S ≤
      (n : ℝ≥0∞) * (volume : Measure (Domain n)) (Ioo (0 : ℝ) 1 • (ψ '' S)) ∧
    (n : ℝ≥0∞) * (volume : Measure (Domain n)) (Ioo (0 : ℝ) 1 • (ψ '' S)) ≤ _
  constructor
  · have h := mul_le_mul_right (measure_mono (μ := (volume : Measure (Domain n))) hLower) (n : ℝ≥0∞)
    rwa [sphere_truncatedCone_volume e he b hb S hS, hnormalize] at h
  · have h := mul_le_mul_right (measure_mono (μ := (volume : Measure (Domain n))) hUpper) (n : ℝ≥0∞)
    rw [sphere_truncatedCone_volume e he 1 zero_lt_one S hS, hnormalize 1] at h
    simpa only [one_pow, ENNReal.ofReal_one, one_mul] using h

end HarmonicMaps
end
