module

public import HarmonicMaps.Energy
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.Analysis.Normed.Module.Span

/-!
# Volume coordinates normal to a unit vector

Orthogonal decomposition identifies ambient volume with the product of real
volume in the normal direction and Euclidean volume on the tangent hyperplane.
The inverse coordinate map has its literal linear formula.
-/

public section

open MeasureTheory Set

namespace HarmonicMaps

/-- Normal and tangent coordinates preserve the actual Euclidean volume. -/
theorem sphere_normal_volume_coordinates {n : ℕ} (e : Domain n) (he : ‖e‖ = 1) :
    ∃ T : (ℝ × (ℝ ∙ e)ᗮ) ≃ᵐ Domain n,
      MeasurePreserving T ∧
      ∀ (t : ℝ) (u : (ℝ ∙ e)ᗮ), T (t, u) = t • e + u.val := by
  let K : Submodule ℝ (Domain n) := ℝ ∙ e
  let f : ℝ ≃ₗᵢ[ℝ] K := LinearIsometryEquiv.toSpanUnitSingleton e he
  let g : (ℝ × Kᗮ) ≃ᵐ (K × Kᗮ) :=
    f.toHomeomorph.toMeasurableEquiv.prodCongr (MeasurableEquiv.refl Kᗮ)
  let T : (ℝ × Kᗮ) ≃ᵐ Domain n := g.trans (K.measurableEquivProd (0 : Domain n)).symm
  have hg : MeasurePreserving g := f.measurePreserving.prod (MeasurePreserving.id volume)
  have hK : MeasurePreserving (K.measurableEquivProd (0 : Domain n)) := by
    simpa only [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] using
      K.measurePreserving_measurableEquivProd (0 : Domain n)
  refine ⟨T, hg.trans hK.symm, ?_⟩
  intro t u
  change (K.measurableEquivProd (0 : Domain n)).symm (f t, u) = _
  rw [Submodule.measurableEquivProd_symm_apply]
  have hfval : (f t).val = t • e :=
    congrArg Subtype.val (LinearIsometryEquiv.toSpanUnitSingleton_apply (𝕜 := ℝ) e he t)
  simp only [hfval, vadd_eq_add, add_zero]

end HarmonicMaps
end
