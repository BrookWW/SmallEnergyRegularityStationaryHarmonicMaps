module

public import HarmonicMaps.Analysis.SphereConeCoordinates
public import HarmonicMaps.Analysis.SphereConeProductVolume

/-!
# Volume of truncated cones over a tangent hyperplane

Orthogonal normal coordinates and scalar dilation of tangent sections give the
exact volume of a truncated cone. The formula applies to every measurable
tangent set, without a finiteness assumption.
-/

public section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace HarmonicMaps

/-- The exact ambient volume of a cone over the affine tangent plane. -/
theorem sphere_truncatedCone_volume {n : ℕ} (e : Domain n) (he : ‖e‖ = 1)
    (b : ℝ) (hb : 0 < b) (S : Set (ℝ ∙ e)ᗮ) (hS : MeasurableSet S) :
    (volume : Measure (Domain n))
        (Ioo (0 : ℝ) b • ((fun u : (ℝ ∙ e)ᗮ => e + u.val) '' S)) =
      ENNReal.ofReal (b ^ n / (n : ℝ)) * (volume : Measure (ℝ ∙ e)ᗮ) S := by
  obtain ⟨T, hT, hTval⟩ := sphere_normal_volume_coordinates e he
  let D : Set (ℝ × (ℝ ∙ e)ᗮ) := {p | p.1 ∈ Ioo (0 : ℝ) b ∧ p.1⁻¹ • p.2 ∈ S}
  have hcone : T '' D = Ioo (0 : ℝ) b • ((fun u : (ℝ ∙ e)ᗮ => e + u.val) '' S) := by
    ext x
    constructor
    · rintro ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩
      refine ⟨t, ht, e + ((t⁻¹ • u : (ℝ ∙ e)ᗮ) : Domain n),
        ⟨t⁻¹ • u, hu, rfl⟩, ?_⟩
      rw [hTval]
      simp only [Submodule.coe_smul, smul_add, smul_smul,
        mul_inv_cancel₀ ht.1.ne', one_smul]
    · rintro ⟨t, ht, _, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨(t, t • u), ⟨ht, ?_⟩, ?_⟩
      · simpa only [smul_smul, inv_mul_cancel₀ ht.1.ne', one_smul] using hu
      · rw [hTval]
        simp only [Submodule.coe_smul, smul_add]
  have hdim : Module.finrank ℝ (ℝ ∙ e)ᗮ + 1 = n := by
    have he0 : e ≠ 0 := by intro h; simp [h] at he
    have hd := (ℝ ∙ e).finrank_add_finrank_orthogonal
    rw [finrank_span_singleton he0, finrank_euclideanSpace_fin] at hd
    omega
  rw [← hcone, ← hT.measure_preimage_equiv (T '' D), Set.preimage_image_eq _ T.injective]
  have hdimR : (Module.finrank ℝ (ℝ ∙ e)ᗮ : ℝ) + 1 = (n : ℝ) := by exact_mod_cast hdim
  simpa only [D, hdim, hdimR] using sphereCone_product_volume b hb S hS

end HarmonicMaps
end
